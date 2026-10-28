//! Benchmarks for the Rust witness. Every subcommand prints one JSON object on stdout.
//!
//! ```text
//! sigil-bench inproc --n 20000 --threads 1 --store memory|redb [--dir D]
//! sigil-bench seal   --sizes 4,7,10,31,100 --iters 2000
//! sigil-bench http   --url http://127.0.0.1:7000 --n 20000 --concurrency 16 [--new-conn]
//! sigil-bench fsync  --dir D --iters 200
//! ```
//!
//! Requests are pre-generated (owner signing is the client's cost, not the witness's), so the
//! timed loop measures only what a witness does: parse, check the lock (one Ed25519
//! verification), update the record, persist, sign the vote (one Ed25519 signature).

use std::collections::HashSet;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use clap::{Parser, Subcommand};
use sigil_witness::charter::{quorum, Registry};
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::proofs::{proves_dead, verify_seal};
use sigil_witness::store::Store;
use sigil_witness::testkit::{genesis, seal_from_votes, spend_request, vote};
use sigil_witness::witness::{system_clock, Witness};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Votes per second of an in-process witness.
    Inproc {
        #[arg(long, default_value_t = 20000)]
        n: usize,
        #[arg(long, default_value_t = 1)]
        threads: usize,
        #[arg(long, default_value = "memory")]
        store: String,
        #[arg(long, default_value = "/tmp")]
        dir: String,
    },
    /// Seal and death-proof verification, single vs batch Ed25519.
    Seal {
        #[arg(long, default_value = "4,7,10,31,100")]
        sizes: String,
        #[arg(long, default_value_t = 2000)]
        iters: usize,
    },
    /// HTTP load generator against any v0 witness (Rust or Python).
    Http {
        #[arg(long)]
        url: String,
        #[arg(long, default_value_t = 10000)]
        n: usize,
        #[arg(long, default_value_t = 16)]
        concurrency: usize,
        /// Open a new TCP connection per request (what Python's urllib client does).
        #[arg(long)]
        new_conn: bool,
        /// Request-generation threads.
        #[arg(long, default_value_t = 4)]
        gen_threads: usize,
    },
    /// Cost of the primitives a vote is made of.
    Micro {
        #[arg(long, default_value_t = 20000)]
        iters: usize,
    },
    /// Raw fsync latency of the disk under `dir`.
    Fsync {
        #[arg(long, default_value = "/tmp")]
        dir: String,
        #[arg(long, default_value_t = 200)]
        iters: usize,
    },
}

fn now() -> i128 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() as i128
}

fn pct(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    sorted[((sorted.len() as f64 - 1.0) * p).round() as usize]
}

fn requests(cid: &str, n: usize, threads: usize, tag: &str) -> Vec<Json> {
    let owner = Arc::new(KeyPair::from_py_seed(b"bench-owner"));
    let per = n.div_ceil(threads.max(1));
    let handles: Vec<_> = (0..threads.max(1))
        .map(|t| {
            let (owner, cid, tag) = (owner.clone(), cid.to_string(), tag.to_string());
            std::thread::spawn(move || {
                (t * per..((t + 1) * per).min(n))
                    .map(|i| spend_request(&owner, &cid, &format!("{tag}-{i:08}"), 0, now() + 86400, "bench").0)
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
}

fn main() {
    match Cli::parse().cmd {
        Cmd::Inproc { n, threads, store, dir } => inproc(n, threads, &store, &dir),
        Cmd::Seal { sizes, iters } => seal(&sizes, iters),
        Cmd::Http { url, n, concurrency, new_conn, gen_threads } => http(&url, n, concurrency, new_conn, gen_threads),
        Cmd::Fsync { dir, iters } => fsync(&dir, iters),
        Cmd::Micro { iters } => micro(iters),
    }
}

fn inproc(n: usize, threads: usize, store_kind: &str, dir: &str) {
    let keys: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("bench-w{i}").as_bytes())).collect();
    let (cid, regj) = genesis("bench", &keys.iter().collect::<Vec<_>>());
    let reg = Registry::from_json(&regj).unwrap();
    let path = format!("{dir}/sigil-bench-{}-{}.redb", std::process::id(), rand::random::<u32>());
    let (store, loaded) = match store_kind {
        "memory" => (Store::memory(), Default::default()),
        "redb" => Store::open(&path).unwrap(),
        other => panic!("unknown store {other}"),
    };
    let w = Arc::new(Witness::open(KeyPair::from_py_seed(b"bench-w0"), reg, &cid, store.clone(), loaded, system_clock()).unwrap());
    // Requests arrive as JSON bytes, as over the wire: parsing is part of the witness's cost.
    let reqs: Vec<Vec<u8>> = requests(&cid, n, 4, "inproc").iter().map(Json::canonical).collect();
    let reqs = Arc::new(reqs);
    let next = Arc::new(AtomicUsize::new(0));
    let t0 = Instant::now();
    let handles: Vec<_> = (0..threads)
        .map(|_| {
            let (w, reqs, next) = (w.clone(), reqs.clone(), next.clone());
            std::thread::spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= reqs.len() {
                    break;
                }
                let req = parse(&reqs[i]).unwrap();
                let (v, seq) = w.spend(&req);
                w.store.wait(seq);
                let _reply = obj([("ok", v.expect("vote"))]).canonical();
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
    let dt = t0.elapsed().as_secs_f64();
    store.close();
    let _ = std::fs::remove_file(&path);
    println!(
        "{}",
        obj([
            ("bench", "rust_inproc".into()),
            ("store", Json::str(store_kind)),
            ("threads", Json::Int(threads as i128)),
            ("n", Json::Int(n as i128)),
            ("seconds", Json::Float(dt)),
            ("votes_per_s", Json::Float(n as f64 / dt)),
            ("us_per_vote", Json::Float(dt * 1e6 / n as f64)),
        ])
        .canonical_string()
    );
}

fn seal(sizes: &str, iters: usize) {
    let mut rows = Vec::new();
    for n in sizes.split(',').map(|s| s.trim().parse::<usize>().unwrap()) {
        let keys: Vec<KeyPair> = (0..n).map(|i| KeyPair::from_py_seed(format!("seal-{n}-{i}").as_bytes())).collect();
        let (cid, regj) = genesis("sealbench", &keys.iter().collect::<Vec<_>>());
        let reg = Registry::from_json(&regj).unwrap();
        let q = quorum(n);
        let lock = obj([("op", "sig".into()), ("pk", Json::str(&keys[0].pk))]);
        let parcel = obj([("home", Json::str(&cid)), ("lock", lock.clone()), ("salt", "aa".into())]);
        let sigil = sigil_witness::model::sigil_of(&Json::str(&cid), &lock, &Json::str("aa"));
        let tid = "e".repeat(64);
        let votes: Vec<Json> = keys[..q].iter().map(|k| vote(k, &cid, &sigil, 0, &tid, 1_700_000_000)).collect();
        let s = seal_from_votes(&votes);
        let header = obj([
            ("inputs", Json::Arr(vec![Json::Arr(vec![Json::str(&sigil), Json::Int(0)])])),
            ("body", Json::str("b".repeat(64))),
        ]);
        let target = sigil_witness::model::transition_id(&header);
        let proof = obj([
            ("kind", "seal".into()),
            ("sigil", Json::str(&sigil)),
            ("gen", Json::Int(0)),
            ("parcel", parcel),
            ("seal", s.clone()),
        ]);
        let none = HashSet::new();
        let mut row = vec![("witnesses", Json::Int(n as i128)), ("quorum", Json::Int(q as i128))];
        for batch in [false, true] {
            assert!(verify_seal(&s, &reg, &none, batch));
            assert!(proves_dead(&header, &target, &proof, &reg, batch));
            let it = (iters * 10 / n.max(1)).max(20);
            let t0 = Instant::now();
            for _ in 0..it {
                assert!(verify_seal(&s, &reg, &none, batch));
            }
            let us = t0.elapsed().as_secs_f64() * 1e6 / it as f64;
            let t0 = Instant::now();
            for _ in 0..it {
                assert!(proves_dead(&header, &target, &proof, &reg, batch));
            }
            let us_dead = t0.elapsed().as_secs_f64() * 1e6 / it as f64;
            row.push((if batch { "seal_us_batch" } else { "seal_us_single" }, Json::Float(us)));
            row.push((if batch { "death_proof_us_batch" } else { "death_proof_us_single" }, Json::Float(us_dead)));
        }
        rows.push(Json::Obj(row.into_iter().map(|(k, v)| (k.to_string(), v)).collect()));
    }
    println!("{}", obj([("bench", "rust_seal".into()), ("rows", Json::Arr(rows))]).canonical_string());
}

/// A minimal blocking HTTP/1.1 client that reuses connections when the server allows it.
struct Conn {
    addr: String,
    host: String,
    stream: Option<BufReader<TcpStream>>,
}

impl Conn {
    fn post(&mut self, path: &str, body: &[u8], new_conn: bool) -> std::io::Result<(u16, Vec<u8>)> {
        if new_conn || self.stream.is_none() {
            let s = TcpStream::connect(&self.addr)?;
            s.set_nodelay(true)?;
            s.set_read_timeout(Some(Duration::from_secs(30)))?;
            self.stream = Some(BufReader::new(s));
        }
        let r = self.stream.as_mut().unwrap();
        let head = format!(
            "POST {path} HTTP/1.1\r\nHost: {}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n{}\r\n",
            self.host,
            body.len(),
            if new_conn { "Connection: close\r\n" } else { "" }
        );
        // One write for head and body: two small writes per request would interact with
        // delayed ACKs on a reused connection.
        let mut msg = head.into_bytes();
        msg.extend_from_slice(body);
        r.get_mut().write_all(&msg)?;
        let mut line = String::new();
        r.read_line(&mut line)?;
        let code: u16 = line.split_whitespace().nth(1).and_then(|c| c.parse().ok()).unwrap_or(0);
        let mut keep = line.starts_with("HTTP/1.1");
        let mut len = None;
        loop {
            let mut h = String::new();
            r.read_line(&mut h)?;
            let h = h.trim_end();
            if h.is_empty() {
                break;
            }
            let lower = h.to_ascii_lowercase();
            if let Some(v) = lower.strip_prefix("content-length:") {
                len = v.trim().parse::<usize>().ok();
            } else if lower.starts_with("connection:") && lower.contains("close") {
                keep = false;
            }
        }
        let mut out = Vec::new();
        match len {
            Some(n) => {
                out.resize(n, 0);
                r.read_exact(&mut out)?;
            }
            None => {
                r.read_to_end(&mut out)?;
                keep = false;
            }
        }
        if !keep || new_conn {
            self.stream = None;
        }
        Ok((code, out))
    }
}

fn http(url: &str, n: usize, concurrency: usize, new_conn: bool, gen_threads: usize) {
    let addr = url.trim_start_matches("http://").trim_end_matches('/').to_string();
    let info = {
        let mut s = TcpStream::connect(&addr).unwrap();
        write!(s, "GET /v0/info HTTP/1.1\r\nHost: {addr}\r\nConnection: close\r\n\r\n").unwrap();
        let mut b = Vec::new();
        s.read_to_end(&mut b).unwrap();
        let i = b.windows(4).position(|w| w == b"\r\n\r\n").unwrap();
        parse(&b[i + 4..]).unwrap()
    };
    let cid = info.get("ok").and_then(|o| o.get("constellation")).and_then(Json::as_str).unwrap().to_string();
    let tag = format!("http-{}-{}", std::process::id(), rand::random::<u32>());
    let bodies: Vec<Vec<u8>> = requests(&cid, n, gen_threads, &tag).into_iter().map(|r| obj([("request", r)]).canonical()).collect();
    let bodies = Arc::new(bodies);
    let next = Arc::new(AtomicUsize::new(0));
    let t0 = Instant::now();
    let handles: Vec<_> = (0..concurrency)
        .map(|_| {
            let (bodies, next, addr) = (bodies.clone(), next.clone(), addr.clone());
            std::thread::spawn(move || {
                let mut c = Conn { host: addr.clone(), addr, stream: None };
                let mut lat = Vec::new();
                let mut errors = 0usize;
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= bodies.len() {
                        break;
                    }
                    let t = Instant::now();
                    match c.post("/v0/spend", &bodies[i], new_conn) {
                        Ok((200, _)) => lat.push(t.elapsed().as_secs_f64() * 1e3),
                        Ok((code, body)) => {
                            errors += 1;
                            if errors < 3 {
                                eprintln!("HTTP {code}: {}", String::from_utf8_lossy(&body));
                            }
                        }
                        Err(e) => {
                            errors += 1;
                            c.stream = None;
                            if errors < 3 {
                                eprintln!("io error: {e}");
                            }
                        }
                    }
                }
                (lat, errors)
            })
        })
        .collect();
    let mut lat = Vec::new();
    let mut errors = 0;
    for h in handles {
        let (l, e) = h.join().unwrap();
        lat.extend(l);
        errors += e;
    }
    let dt = t0.elapsed().as_secs_f64();
    lat.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "{}",
        obj([
            ("bench", "http_spend".into()),
            ("url", Json::str(url)),
            ("n", Json::Int(n as i128)),
            ("ok", Json::Int(lat.len() as i128)),
            ("errors", Json::Int(errors as i128)),
            ("concurrency", Json::Int(concurrency as i128)),
            ("new_conn", Json::Bool(new_conn)),
            ("seconds", Json::Float(dt)),
            ("votes_per_s", Json::Float(lat.len() as f64 / dt)),
            ("p50_ms", Json::Float(pct(&lat, 0.5))),
            ("p99_ms", Json::Float(pct(&lat, 0.99))),
        ])
        .canonical_string()
    );
}

fn fsync(dir: &str, iters: usize) {
    let path = format!("{dir}/sigil-fsync-{}", std::process::id());
    let mut f = std::fs::OpenOptions::new().create(true).write(true).truncate(true).open(&path).unwrap();
    let mut lat = Vec::new();
    for i in 0..iters {
        f.write_all(&[i as u8; 512]).unwrap();
        let t = Instant::now();
        f.sync_data().unwrap();
        lat.push(t.elapsed().as_secs_f64() * 1e3);
    }
    let _ = std::fs::remove_file(&path);
    lat.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "{}",
        obj([
            ("bench", "fsync".into()),
            ("dir", Json::str(dir)),
            ("p50_ms", Json::Float(pct(&lat, 0.5))),
            ("p99_ms", Json::Float(pct(&lat, 0.99))),
        ])
        .canonical_string()
    );
}

fn time_us(iters: usize, mut f: impl FnMut()) -> Json {
    let t0 = Instant::now();
    for _ in 0..iters {
        f();
    }
    Json::Float(t0.elapsed().as_secs_f64() * 1e6 / iters as f64)
}

fn micro(iters: usize) {
    use sigil_witness::crypto::{decode_pk, decode_sig, signing_message, verify_message};
    let owner = KeyPair::from_py_seed(b"micro");
    let (req, sigil, tid) = spend_request(&owner, &"c".repeat(64), "aa", 0, 1 << 40, "m");
    let bytes = req.canonical();
    let msg = signing_message("unlock", &sigil_witness::model::unlock_message(&sigil, &tid, Json::Int(1 << 40)));
    let sig_hex = req.get("unlock").unwrap().get("sigs").unwrap().get(&owner.pk).unwrap().as_str().unwrap().to_string();
    let vk = decode_pk(&owner.pk).unwrap();
    let sig = decode_sig(&sig_hex).unwrap();
    let header = req.get("header").unwrap().clone();
    let v = vote(&owner, "c", &sigil, 0, &tid, 1);
    let payload = sigil_witness::model::vote_payload(&v).unwrap();
    let rows = obj([
        ("parse_request_us", time_us(iters, || drop(parse(&bytes).unwrap()))),
        ("canonical_request_us", time_us(iters, || drop(req.canonical()))),
        ("tid_hash_us", time_us(iters, || drop(sigil_witness::model::transition_id(&header)))),
        ("decode_pk_us", time_us(iters, || assert!(decode_pk(&owner.pk).is_some()))),
        ("ed25519_verify_us", time_us(iters, || assert!(verify_message(&vk, &msg, &sig)))),
        ("ed25519_sign_vote_us", time_us(iters, || drop(owner.sign("vote", &payload)))),
        ("lock_eval_us", time_us(iters, || {
            assert!(sigil_witness::locks::evaluate(req.get("lock").unwrap(), req.get("unlock").unwrap(), &sigil, &tid, Some(1), true))
        })),
    ]);
    println!("{}", obj([("bench", "rust_micro".into()), ("rows", rows)]).canonical_string());
}
