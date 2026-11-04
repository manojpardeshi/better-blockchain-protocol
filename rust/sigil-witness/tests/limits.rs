//! Resource bounds (docs/AI_THREAT_MODEL.md §2.6): what one request can make a witness store,
//! the size of a charter, ADOPT keeping each evidence entry once, and admission control over
//! HTTP (per-client rate limit, connection caps, idle timeout). The byte-for-byte comparison
//! with the reference is in vectors.rs (`limits` script); these cover the server and the
//! bounds themselves.

use std::sync::Arc;
use std::time::Duration;

use sigil_witness::charter::{charter_hash, Registry, MAX_CHARTER_BYTES, MAX_WITNESSES};
use sigil_witness::crypto::KeyPair;
use sigil_witness::gossip::GossipStore;
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::ratelimit::{ConnectionLimiter, RateLimiter};
use sigil_witness::store::Store;
use sigil_witness::testkit::{genesis, seal_from_votes, spend_request};
use sigil_witness::witness::{system_clock, Error, Witness, MAX_AUTH_BYTES, MAX_GEN, MAX_PROOF_BYTES};

const FAR: i128 = 4_000_000_000;

fn constellation(tag: &str, n: usize) -> (Vec<KeyPair>, String, Registry) {
    let keys: Vec<KeyPair> = (0..n).map(|i| KeyPair::from_py_seed(format!("{tag}{i}").as_bytes())).collect();
    let (cid, regj) = genesis(tag, &keys.iter().collect::<Vec<_>>());
    (keys, cid, Registry::from_json(&regj).unwrap())
}

fn witness(seed: &str, reg: &Registry, cid: &str) -> Witness {
    Witness::open(KeyPair::from_py_seed(seed.as_bytes()), reg.clone(), cid, Store::memory(), Default::default(), system_clock()).unwrap()
}

fn set(v: &mut Json, k: &str, x: Json) {
    if let Json::Obj(m) = v {
        m.insert(k.into(), x);
    }
}

#[test]
fn oversized_spend_is_rejected_and_stores_nothing() {
    let (_, cid, reg) = constellation("lim-a", 4);
    let w = witness("lim-a0", &reg, &cid);
    let owner = KeyPair::from_py_seed(b"lim-owner");
    // Before: an ~800 KiB salt (within the 1 MiB body cap) was stored whole in the log.
    let (big, s, _) = spend_request(&owner, &cid, &"ee".repeat(400_000), 0, FAR, "m");
    assert_eq!(w.spend(&big).0, Err(Error::Rejected("authorisation too large".into())));
    assert!(w.record(&s).is_none(), "a refused SPEND changes nothing");
    // The largest salt that fits is accepted, and pins about MAX_AUTH_BYTES.
    let fits = |n: usize| {
        let (r, _, _) = spend_request(&owner, &cid, &"e".repeat(n), 0, FAR, "m");
        let auth = obj(["home", "lock", "salt", "unlock", "header"].map(|k| (k, r.get(k).cloned().unwrap())));
        auth.canonical().len() <= MAX_AUTH_BYTES
    };
    let (mut lo, mut hi) = (0usize, MAX_AUTH_BYTES);
    while lo < hi {
        let mid = (lo + hi + 1) / 2;
        if fits(mid) {
            lo = mid
        } else {
            hi = mid - 1
        }
    }
    let (r, s2, _) = spend_request(&owner, &cid, &"e".repeat(lo), 0, FAR, "m");
    assert!(w.spend(&r).0.is_ok());
    let stored = w.record(&s2).unwrap().to_json().canonical().len();
    assert!(stored <= MAX_AUTH_BYTES + 4096, "{stored}");
    let (r, s3, _) = spend_request(&owner, &cid, &"e".repeat(lo + 1), 0, FAR, "m");
    assert_eq!(w.spend(&r).0, Err(Error::Rejected("authorisation too large".into())));
    assert!(w.record(&s3).is_none());
}

#[test]
fn a_sigil_is_bound_at_most_max_gen_times_and_proofs_are_capped() {
    let (keys, cid, reg) = constellation("lim-b", 4);
    let ws: Vec<Witness> = (0..4).map(|i| witness(&format!("lim-b{i}"), &reg, &cid)).collect();
    let owner = KeyPair::from_py_seed(b"lim-owner");
    // A kill switch k sealed once: every header {[s, g], [k, 0]} is then dead by that seal.
    let (kreq, k, _) = spend_request(&owner, &cid, &"ab".repeat(16), 0, FAR, "kill");
    let votes: Vec<Json> = ws.iter().map(|w| w.spend(&kreq).0.unwrap()).collect();
    let seal = seal_from_votes(&votes);
    let proof = obj([
        ("kind", "seal".into()),
        ("sigil", Json::str(&k)),
        ("gen", Json::Int(0)),
        ("seal", seal),
        ("parcel", obj([("home", Json::str(&cid)), ("lock", kreq.get("lock").cloned().unwrap()), ("salt", kreq.get("salt").cloned().unwrap())])),
    ]);
    let mut padded = proof.clone();
    set(&mut padded, "junk", Json::str("00".repeat(MAX_PROOF_BYTES / 2)));
    let w = &ws[0];
    let mut binds = 0;
    let mut s = String::new();
    for g in 0..40 {
        let (mut req, sigil, _) = spend_request(&owner, &cid, &"cd".repeat(16), g, FAR, &format!("m{g}"));
        // Re-sign over a header that also names the kill switch.
        let header = obj([
            ("inputs", Json::Arr(vec![Json::Arr(vec![Json::str(&sigil), Json::Int(g)]), Json::Arr(vec![Json::str(&k), Json::Int(0)])])),
            ("body", Json::str(format!("{g:064x}"))),
        ]);
        let tid = sigil_witness::model::transition_id(&header);
        let sig = owner.sign("unlock", &sigil_witness::model::unlock_message(&sigil, &tid, Json::Int(FAR)));
        let mut unlock = req.get("unlock").cloned().unwrap();
        set(&mut unlock, "sigs", Json::Obj([(owner.pk.clone(), Json::Str(sig))].into_iter().collect()));
        set(&mut req, "header", header);
        set(&mut req, "unlock", unlock);
        s = sigil.clone();
        match w.spend(&req).0 {
            Ok(_) => binds += 1,
            Err(e) => {
                assert_eq!(e, Error::Rejected("generation limit reached for this sigil".into()));
                let before = w.record(&s).unwrap();
                assert_eq!(w.spend(&req).0, Err(e), "still refused");
                assert_eq!(w.record(&s).unwrap(), before, "a refused SPEND changes nothing");
                break;
            }
        }
        let before = w.record(&s).unwrap();
        assert_eq!(w.release(&Json::str(&s), &padded).0, Err(Error::Rejected("death proof too large".into())));
        assert_eq!(w.record(&s).unwrap(), before, "a refused RELEASE changes nothing");
        assert_eq!(w.release(&Json::str(&s), &proof).0, Ok(Json::Int(g + 1)));
    }
    assert_eq!(binds, MAX_GEN);
    let stored = w.record(&s).unwrap().to_json().canonical().len();
    assert!(stored < MAX_GEN as usize * MAX_AUTH_BYTES / 8, "{stored}");
    let _ = keys;
}

#[test]
fn adopt_keeps_each_evidence_entry_once() {
    let (_, cid, reg) = constellation("lim-c", 4);
    let ws: Vec<Witness> = (0..4).map(|i| witness(&format!("lim-c{i}"), &reg, &cid)).collect();
    let owner = KeyPair::from_py_seed(b"lim-owner");
    let (req, s, _) = spend_request(&owner, &cid, &"ab".repeat(16), 0, FAR, "m");
    for w in &ws {
        w.spend(&req).0.unwrap();
    }
    let newk: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("lim-cn{i}").as_bytes())).collect();
    let body0 = reg.charter(&cid, 0).unwrap().body.clone();
    let next = obj([
        ("name", Json::str("lim-c")),
        ("version", Json::Int(1)),
        ("witnesses", Json::Arr(newk.iter().map(|k| Json::str(&k.pk)).collect())),
        ("prev", Json::str(charter_hash(&body0))),
    ]);
    let mut sigs = std::collections::BTreeMap::new();
    let mut snaps = Vec::new();
    for w in &ws[..3] {
        let out = w.freeze(&next).0.unwrap();
        sigs.insert(w.pk.clone(), out.get("sig").cloned().unwrap());
        snaps.push(out.get("snapshot").cloned().unwrap());
    }
    let mut chain = reg.raw_chain(&cid).to_vec();
    chain.push(obj([("body", next), ("sigs", Json::Obj(sigs.into_iter().collect()))]));
    let mut reg1 = reg.clone();
    reg1.add_chain(&cid, &chain).unwrap();
    let a = Witness::open_with(KeyPair::from_py_seed(b"lim-cn0"), reg1, &cid, Store::memory(), Default::default(), system_clock(), true).unwrap();
    // The same snapshot three times over, as honest signers hand it over.
    let mut three = snaps.clone();
    three.extend(snaps.iter().cloned());
    // A Byzantine signer pads an honest owner's unbound sigil with junk bind entries.
    let (fresh, fs, _) = spend_request(&owner, &cid, &"cd".repeat(16), 0, FAR, "fresh");
    let junk: Vec<Json> =
        (0..3 * MAX_GEN).map(|i| obj([("kind", "bind".into()), ("gen", Json::Int(i)), ("auth", Json::Null)])).collect();
    three.push(Json::Obj([(fs.clone(), Json::Arr(junk))].into_iter().collect()));
    a.adopt(&Json::str(&cid), &Json::Int(1), &three).0.unwrap();
    // One bind entry (identical in every snapshot) and the three signers' own votes.
    let log = a.record(&s).unwrap().log;
    assert_eq!(log.len(), 4, "{}", Json::Arr(log.clone()).canonical_string());
    // The junk never counts, and the generation cap reads the record: the owner can spend.
    let r = a.record(&fs).unwrap();
    assert_eq!((r.log.len() as i128, r.gen), (3 * MAX_GEN, 0));
    assert!(a.spend(&fresh).0.is_ok());
}

fn chain_json(name: &str, n: usize, pad_name: usize) -> (String, Json) {
    let ws: Vec<Json> = (0..n).map(|i| Json::str(format!("{i:064x}"))).collect();
    let body = obj([("name", Json::str(format!("{name}{}", "n".repeat(pad_name)))), ("version", Json::Int(0)), ("witnesses", Json::Arr(ws)), ("prev", Json::Null)]);
    let cid = sigil_witness::charter::constellation_id(&body);
    (cid, Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Default::default()))])]))
}

#[test]
fn charters_are_capped_in_verification_and_gossip() {
    // Before: one ~1 MiB gossip message registered a charter of 14,000 witnesses.
    for (n, pad, ok) in [(14_000, 0, false), (MAX_WITNESSES + 1, 0, false), (MAX_WITNESSES, 0, true), (4, 900_000, false), (4, 0, true)] {
        let (cid, chain) = chain_json("x", n, pad);
        let mut reg = Registry::default();
        assert_eq!(reg.add_chain(&cid, chain.as_arr().unwrap()).is_ok(), ok, "n={n} pad={pad}");
        let base = Arc::new(Registry::default());
        let mut cow = sigil_witness::gossip::CowRegistry::new(&base);
        let mut g = GossipStore::default();
        let msg = obj([("charters", Json::Obj([(cid.clone(), chain.clone())].into_iter().collect()))]);
        let out = g.merge(&mut cow, &msg, true).unwrap();
        assert_eq!(out.get("charters"), Some(&Json::Int(ok as i128)), "n={n} pad={pad}");
        if ok {
            assert!(chain.canonical().len() <= MAX_CHARTER_BYTES);
        }
    }
}

// ------------------------------------------------------------------------------- HTTP

async fn http(addr: std::net::SocketAddr, path: &str, body: &str) -> (u16, String, Json) {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    let mut s = tokio::net::TcpStream::connect(addr).await.unwrap();
    let req = format!("POST {path} HTTP/1.1\r\nHost: t\r\nConnection: close\r\nContent-Length: {}\r\n\r\n{body}", body.len());
    s.write_all(req.as_bytes()).await.unwrap();
    let mut out = Vec::new();
    s.read_to_end(&mut out).await.unwrap();
    let text = String::from_utf8(out).unwrap();
    let code = text[9..12].parse().unwrap();
    let (head, json) = text.split_once("\r\n\r\n").unwrap_or((&text, ""));
    (code, head.to_lowercase(), parse(json.as_bytes()).unwrap_or(Json::Null))
}

async fn start(w: Arc<Witness>, limiter: Option<Arc<RateLimiter>>, conns: Arc<ConnectionLimiter>, idle: Duration) -> std::net::SocketAddr {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    let app = sigil_witness::server::router_with_limits(w, Some("tok".into()), limiter);
    tokio::spawn(sigil_witness::server::serve_with(listener, app, conns, idle, std::future::pending()));
    addr
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_client_over_its_rate_gets_429_and_the_witness_never_sees_it() {
    let (_, cid, reg) = constellation("lim-d", 4);
    let w = Arc::new(witness("lim-d0", &reg, &cid));
    let limiter = Arc::new(RateLimiter::new(0.5, 3).unwrap());
    let addr = start(w.clone(), Some(limiter), ConnectionLimiter::new(64, Some(16)), Duration::from_secs(30)).await;
    let owner = KeyPair::from_py_seed(b"lim-owner");
    let status = obj([("sigil", Json::str("00".repeat(32)))]).canonical_string();
    for _ in 0..3 {
        assert_eq!(http(addr, "/v0/status", &status).await.0, 200);
    }
    // Over the burst: a SPEND that would bind is refused before the witness sees it.
    let (req, s, _) = spend_request(&owner, &cid, &"ab".repeat(16), 0, FAR, "m");
    let (code, head, body) = http(addr, "/v0/spend", &obj([("request", req)]).canonical_string()).await;
    assert_eq!(code, 429);
    assert_eq!(body.get("error").and_then(Json::as_str), Some("rejected"));
    assert_eq!(body.get("message").and_then(Json::as_str), Some("rate limited"));
    assert!(head.contains("retry-after: 2"), "{head}");
    assert!(w.record(&s).is_none(), "rate limiting never touches witness state");
    // Rotation calls are never limited (the admin token decides).
    let (code, _, body) = http(addr, "/v0/freeze", "{}").await;
    assert_eq!((code, body.get("message").and_then(Json::as_str)), (403, Some("bad admin token")));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn connections_are_capped_and_idle_ones_dropped() {
    use tokio::io::AsyncReadExt;
    let (_, cid, reg) = constellation("lim-e", 4);
    let w = Arc::new(witness("lim-e0", &reg, &cid));
    let conns = ConnectionLimiter::new(8, None);
    let addr = start(w, None, conns.clone(), Duration::from_millis(600)).await;
    let mut socks = Vec::new();
    for _ in 0..12 {
        socks.push(tokio::net::TcpStream::connect(addr).await.unwrap());
    }
    tokio::time::sleep(Duration::from_millis(200)).await;
    assert_eq!(conns.open(), 8, "at most the cap are held");
    let mut closed = 0;
    for s in socks.iter_mut() {
        let mut b = [0u8; 1];
        if let Ok(Ok(0)) = tokio::time::timeout(Duration::from_millis(20), s.read(&mut b)).await {
            closed += 1;
        }
    }
    assert_eq!(closed, 4, "connections over the cap are closed unread");
    tokio::time::sleep(Duration::from_millis(1200)).await;
    assert_eq!(conns.open(), 0, "silent connections are dropped after the idle timeout");
    // And the server still answers.
    let status = obj([("sigil", Json::str("00".repeat(32)))]).canonical_string();
    assert_eq!(http(addr, "/v0/status", &status).await.0, 200);
}
