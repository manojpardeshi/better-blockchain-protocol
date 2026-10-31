//! The witness daemon, with the same files and flags as `python -m sigil.witnessd`.
//!
//! ```text
//! sigil-witness keygen  --out key.json
//! sigil-witness genesis --name orion --keys k1.pub k2.pub k3.pub k4.pub --out registry.json
//! sigil-witness run     --key key.json --registry registry.json --constellation <cid> \
//!                       --store data.redb [--host 127.0.0.1] [--port 7000] [--stamps] \
//!                       [--admin-token FILE] [--adopt]
//! ```
//!
//! Every vote is made durable before it is sent, so the daemon may be killed at any moment,
//! even with SIGKILL, and restarted on the same store.
//!
//! `--stamps` requires a stamp with every SPEND and sells them; the stamp key lives in
//! `<store>.stamps.json` (the reference's file and format), created on first use. A fresh
//! store joins charter version 0; a new member of a later version is started with `--adopt`
//! and waits for `/v0/adopt`. The rotation calls need the token in `--admin-token FILE`.

use std::io::Write;
use std::sync::Arc;

use clap::{Parser, Subcommand};
use sigil_witness::charter::{constellation_id, short};
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::stamps::load_mint;
use sigil_witness::store::Store;
use sigil_witness::witness::system_clock;
use sigil_witness::{load_admin_token, load_key, load_registry, server, write_private, KeyPair, Witness};

#[derive(Parser)]
#[command(name = "sigil-witness", about = "Sigil v0 witness (Rust)", version)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Generate a witness key (private file 0600, public key in <out>.pub).
    Keygen {
        #[arg(long)]
        out: String,
    },
    /// Create a constellation (charter version 0) from witness public keys.
    Genesis {
        #[arg(long)]
        name: String,
        /// Public keys: .pub files, key files or hex.
        #[arg(long, num_args = 1.., required = true)]
        keys: Vec<String>,
        /// Registry file (merged into if it exists).
        #[arg(long)]
        out: String,
    },
    /// Serve a witness.
    Run {
        #[arg(long)]
        key: String,
        #[arg(long)]
        registry: String,
        #[arg(long)]
        constellation: String,
        #[arg(long)]
        store: String,
        #[arg(long, default_value = "127.0.0.1")]
        host: String,
        #[arg(long, default_value_t = 7000)]
        port: u16,
        /// Require a stamp with every spend (and sell stamps); key in <store>.stamps.json.
        #[arg(long)]
        stamps: bool,
        /// File holding the operator token that authorises /v0/freeze and /v0/adopt.
        #[arg(long, value_name = "FILE")]
        admin_token: Option<String>,
        /// On a fresh store, do not join: wait for /v0/adopt into a later charter version.
        #[arg(long)]
        adopt: bool,
        /// Verify each signature on its own instead of Ed25519 batch verification.
        #[arg(long)]
        no_batch_verify: bool,
        /// Async worker threads (default: one per CPU).
        #[arg(long)]
        threads: Option<usize>,
        /// Keep state in memory only. FOR BENCHMARKS ONLY: a restart forgets every vote.
        #[arg(long)]
        unsafe_memory_store: bool,
    },
}

fn pub_path(key: &str) -> String {
    match key.rfind('.') {
        Some(i) if !key[i..].contains('/') => format!("{}.pub", &key[..i]),
        _ => format!("{key}.pub"),
    }
}

fn read_pk(arg: &str) -> Result<String, String> {
    if !std::path::Path::new(arg).exists() {
        hex::decode(arg).map_err(|_| format!("{arg}: neither a file nor hex"))?;
        return Ok(arg.to_lowercase());
    }
    let text = std::fs::read_to_string(arg).map_err(|e| e.to_string())?;
    let text = text.trim();
    if text.starts_with('{') {
        let v = parse(text.as_bytes()).map_err(|e| e.to_string())?;
        v.get("pk").and_then(Json::as_str).map(str::to_string).ok_or_else(|| format!("{arg}: no pk"))
    } else {
        Ok(text.to_string())
    }
}

fn main() {
    let cli = Cli::parse();
    let r = match cli.cmd {
        Cmd::Keygen { out } => keygen(&out),
        Cmd::Genesis { name, keys, out } => genesis(&name, &keys, &out),
        Cmd::Run {
            key,
            registry,
            constellation,
            store,
            host,
            port,
            stamps,
            admin_token,
            adopt,
            no_batch_verify,
            threads,
            unsafe_memory_store,
        } => run(RunArgs {
            key,
            registry,
            cid: constellation,
            store,
            host,
            port,
            stamps,
            admin_token,
            adopt,
            batch: !no_batch_verify,
            threads,
            memory: unsafe_memory_store,
        }),
    };
    if let Err(e) = r {
        eprintln!("sigil-witness: {e}");
        std::process::exit(1);
    }
}

fn keygen(out: &str) -> Result<(), String> {
    let (kp, seed) = KeyPair::generate();
    let v = obj([("seed", Json::str(hex::encode(seed))), ("pk", Json::str(&kp.pk))]);
    write_private(out, &v.canonical()).map_err(|e| format!("{out}: {e}"))?;
    std::fs::write(pub_path(out), format!("{}\n", kp.pk)).map_err(|e| e.to_string())?;
    println!("{}", kp.pk);
    Ok(())
}

fn genesis(name: &str, keys: &[String], out: &str) -> Result<(), String> {
    let pks = keys.iter().map(|k| read_pk(k)).collect::<Result<Vec<_>, _>>()?;
    let mut uniq = pks.clone();
    uniq.sort();
    uniq.dedup();
    if pks.is_empty() || uniq.len() != pks.len() {
        return Err("witness list must be non-empty and unique".into());
    }
    let body = obj([
        ("name", Json::str(name)),
        ("version", Json::Int(0)),
        ("witnesses", Json::Arr(pks.into_iter().map(Json::Str).collect())),
        ("prev", Json::Null),
    ]);
    let cid = constellation_id(&body);
    let mut reg = match std::fs::read(out) {
        Ok(b) => parse(&b).map_err(|e| format!("{out}: {e}"))?,
        Err(_) => Json::Obj(Default::default()),
    };
    if let Json::Obj(m) = &mut reg {
        m.insert(cid.clone(), Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Default::default()))])]));
    } else {
        return Err(format!("{out}: not a registry"));
    }
    let tmp = format!("{out}.tmp");
    std::fs::write(&tmp, reg.canonical()).map_err(|e| e.to_string())?;
    std::fs::rename(&tmp, out).map_err(|e| e.to_string())?;
    println!("{cid}");
    Ok(())
}

struct RunArgs {
    key: String,
    registry: String,
    cid: String,
    store: String,
    host: String,
    port: u16,
    stamps: bool,
    admin_token: Option<String>,
    adopt: bool,
    batch: bool,
    threads: Option<usize>,
    memory: bool,
}

fn run(a: RunArgs) -> Result<(), String> {
    let (cid, host, port) = (a.cid.as_str(), a.host.as_str(), a.port);
    let kp = load_key(&a.key)?;
    let reg = load_registry(&a.registry)?;
    if !reg.contains(cid) {
        return Err(format!("constellation {cid} is not in {}", a.registry));
    }
    let token = a.admin_token.as_deref().map(load_admin_token).transpose()?;
    let (store, loaded) = if a.memory {
        eprintln!("sigil-witness: WARNING --unsafe-memory-store: state is not durable (benchmarks only)");
        (Store::memory(), Default::default())
    } else {
        Store::open(&a.store)?
    };
    let mut w = Witness::open_with(kp, reg, cid, store.clone(), loaded, system_clock(), a.adopt)?;
    if a.stamps {
        // Redeemed serials come back from the witness store.
        w = w.with_stamps(load_mint(&format!("{}.stamps.json", a.store), 2048)?);
    }
    w.batch_verify = a.batch;
    let w = Arc::new(w);

    let mut rt = tokio::runtime::Builder::new_multi_thread();
    if let Some(n) = a.threads {
        rt.worker_threads(n.max(1));
    }
    let rt = rt.enable_all().build().map_err(|e| e.to_string())?;
    rt.block_on(async {
        let listener = tokio::net::TcpListener::bind((host, port)).await.map_err(|e| format!("{host}:{port}: {e}"))?;
        let addr = listener.local_addr().map_err(|e| e.to_string())?;
        match (w.cid(), w.version()) {
            (Some(c), Some(v)) => {
                println!("witness {} of {} v{} listening on http://{}:{}", short(&w.pk), short(&c), v, addr.ip(), addr.port())
            }
            _ => println!("witness {} awaiting ADOPT into {} listening on http://{}:{}", short(&w.pk), short(cid), addr.ip(), addr.port()),
        }
        let _ = std::io::stdout().flush();
        axum::serve(listener, server::router_with_admin(w.clone(), token))
            .tcp_nodelay(true)
            .with_graceful_shutdown(shutdown_signal())
            .await
            .map_err(|e| e.to_string())
    })?;
    drop(rt);
    store.close(); // flush every queued write before exiting
    println!("stopped");
    Ok(())
}

async fn shutdown_signal() {
    #[cfg(unix)]
    {
        use tokio::signal::unix::{signal, SignalKind};
        let mut term = signal(SignalKind::terminate()).expect("SIGTERM handler");
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {}
            _ = term.recv() => {}
        }
    }
    #[cfg(not(unix))]
    {
        let _ = tokio::signal::ctrl_c().await;
    }
}
