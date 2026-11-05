//! Succession (SPEC §5.5) on the real standby member and witness: durable across restarts, and
//! over HTTP (operator token, admission control that exempts the operator calls, heartbeats
//! probed over the wire). The byte-for-byte comparison with the reference is in vectors.rs.

use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use sigil_witness::charter::{charter_hash, constellation_id, Registry};
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::ratelimit::RateLimiter;
use sigil_witness::store::{Loaded, Store};
use sigil_witness::succession::Standby;
use sigil_witness::testkit::spend_request;
use sigil_witness::witness::{Clock, Error, Witness};

const DEAD: i128 = 100;

struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(tag: &str) -> TempDir {
        let p = std::env::temp_dir().join(format!("sigil-succ-{tag}-{}-{}", std::process::id(), rand::random::<u64>()));
        std::fs::create_dir_all(&p).unwrap();
        TempDir(p)
    }

    fn path(&self, f: &str) -> String {
        self.0.join(f).to_str().unwrap().to_string()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn key(s: &str) -> KeyPair {
    KeyPair::from_py_seed(s.as_bytes())
}

/// Version 0 of `tag`: witnesses `<tag>w0..3`, committee `<tag>k0..3`, dead_man [`DEAD`].
struct World {
    cid: String,
    reg: Registry,
    owner: KeyPair,
    next: Json,
}

fn world(tag: &str) -> World {
    let pks = |p: &str| Json::Arr((0..4).map(|i| Json::str(key(&format!("{tag}{p}{i}")).pk)).collect());
    let body = obj([
        ("name", Json::str(tag)),
        ("version", Json::Int(0)),
        ("witnesses", pks("w")),
        ("prev", Json::Null),
        ("successor", obj([("committee", pks("k")), ("dead_man", Json::Int(DEAD))])),
    ]);
    let cid = constellation_id(&body);
    let next = obj([
        ("name", Json::str(tag)),
        ("version", Json::Int(1)),
        ("witnesses", pks("n")),
        ("prev", Json::str(charter_hash(&body))),
    ]);
    let chain = Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Default::default()))])]);
    let reg = Registry::from_json(&Json::Obj([(cid.clone(), chain)].into_iter().collect())).unwrap();
    World { cid, reg, owner: key(&format!("{tag}owner")), next }
}

fn clock(now: &Arc<AtomicI64>) -> Clock {
    let n = now.clone();
    Box::new(move || n.load(Ordering::SeqCst) as i128)
}

fn open_standby(path: &str, seed: &str, w: &World, now: &Arc<AtomicI64>) -> Standby {
    let (store, loaded) = Store::open(path).unwrap();
    Standby::open(key(seed), w.reg.clone(), &w.cid, store, loaded, clock(now), false).unwrap()
}

fn ok(o: (Result<Json, Error>, u64), store: &Store) -> Json {
    store.wait(o.1);
    o.0.unwrap()
}

fn with_version(req: &Json, v: i128) -> Json {
    let mut r = req.clone();
    if let Json::Obj(m) = &mut r {
        m.insert("version".into(), Json::Int(v));
    }
    r
}

#[test]
fn standby_survives_restarts() {
    let dir = TempDir::new("restart");
    let w = world("lyra");
    let now = Arc::new(AtomicI64::new(1_700_000_000));
    let p = dir.path("k0.redb");
    let (ra, sa, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "a");

    let k = open_standby(&p, "lyrak0", &w, &now);
    assert_eq!(k.member(), Some((w.cid.clone(), 0)), "a fresh store stands by for version 0");
    let ack = ok(k.mirror_bind(&with_version(&ra, 0)), &k.store);
    k.store.close();
    drop(k);

    // Restarted: the mirror log is back, so the same binding is acknowledged again without a
    // second entry, and a restart opens a new observation window.
    now.fetch_add(10 * DEAD as i64, Ordering::SeqCst);
    let k = open_standby(&p, "lyrak0", &w, &now);
    assert_eq!(ok(k.mirror_bind(&with_version(&ra, 0)), &k.store), ack);
    assert_eq!(k.snapshot().get(&sa).and_then(Json::as_arr).map(Vec::len), Some(1));
    assert!(!k.dead(), "it just came back: it has not watched for dead_man seconds yet");
    assert_eq!(
        k.succeed(&w.next, None).0,
        Err(Error::Rejected("the version is alive: no quorum of its members asked, and the dead-man period has not passed".into()))
    );
    now.fetch_add(DEAD as i64, Ordering::SeqCst);
    assert!(k.dead(), "no member answered for dead_man seconds");
    let signed = ok(k.succeed(&w.next, None), &k.store);
    assert_eq!(signed.get("snapshot"), Some(&k.snapshot()));
    k.store.close();
    drop(k);

    // Restarted again: still fenced for that successor and no other.
    let k = open_standby(&p, "lyrak0", &w, &now);
    assert!(k.fenced());
    assert_eq!(k.mirror_bind(&with_version(&ra, 0)).0, Err(Error::Rejected("fenced: this member signed a successor of the version".into())));
    assert_eq!(ok(k.succeed(&w.next, None), &k.store), signed, "the same successor: answered again");
    let mut other = w.next.clone();
    if let Json::Obj(m) = &mut other {
        m.insert("witnesses".into(), Json::Arr(vec![Json::str(key("x").pk)]));
    }
    assert_eq!(k.succeed(&other, None).0, Err(Error::Rejected("already signed a different successor".into())));
    k.store.close();
    drop(k);

    // A store belongs to one key and one constellation.
    let (store, loaded) = Store::open(&p).unwrap();
    assert!(Standby::open(key("lyrak1"), w.reg.clone(), &w.cid, store, loaded, clock(&now), false).is_err());
    // A key outside version 0's committee cannot stand by for it.
    let (store, loaded) = Store::open(dir.path("x.redb")).unwrap();
    assert!(Standby::open(key("lyrax"), w.reg.clone(), &w.cid, store, loaded, clock(&now), false).is_err());
}

#[test]
fn witnesses_vote_only_with_an_ack_quorum() {
    let w = world("vega");
    let now = Arc::new(AtomicI64::new(1_700_000_000));
    let wit = Witness::open(key("vegaw0"), w.reg.clone(), &w.cid, Store::memory(), Default::default(), clock(&now)).unwrap();
    let ks: Vec<Standby> = (0..4)
        .map(|i| Standby::open(key(&format!("vegak{i}")), w.reg.clone(), &w.cid, Store::memory(), Default::default(), clock(&now), false).unwrap())
        .collect();
    let (ra, sa, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "a");
    let acks: Vec<Json> = ks.iter().map(|k| k.mirror_bind(&with_version(&ra, 0)).0.unwrap()).collect();
    let with = |acks: &[Json]| {
        let mut r = ra.clone();
        if let Json::Obj(m) = &mut r {
            m.insert("mirror".into(), Json::Arr(acks.to_vec()));
        }
        r
    };
    let refused = Err(Error::Rejected("needs mirror acks from a quorum of the successor committee".into()));
    assert_eq!(wit.spend(&ra).0, refused);
    assert_eq!(wit.spend(&with(&acks[..2])).0, refused);
    assert!(wit.record(&sa).is_none(), "nothing is stored on refusal");
    let vote = wit.spend(&with(&acks[1..])).0.unwrap();
    assert_eq!(wit.spend(&ra).0.unwrap(), vote, "a vote it holds needs no acks");
    // A frozen witness answers no heartbeat; an active one signs the challenge.
    let hb = wit.heartbeat(&Json::str("c")).0.unwrap();
    assert!(ks[0].observe(&hb, "c"));
    assert!(!ks[0].observe(&hb, "d"));
    assert_eq!(wit.heartbeat(&Json::str("")).0, Err(Error::Rejected("challenge must be a string of 1 to 128 characters".into())));
    wit.freeze(&w.next).0.unwrap();
    assert_eq!(wit.heartbeat(&Json::str("c")).0, Err(Error::Rejected("witness not active".into())));
}

/// A member (or standby member) whose registry is older than its store, e.g. restarted with a
/// registry file nobody updated after a rotation into a version with a committee, cannot tell
/// whether acks are needed: it fails closed.
#[test]
fn without_its_own_charter_nothing_is_voted_or_signed() {
    let w = world("cass");
    let now = Arc::new(AtomicI64::new(1_700_000_000));
    let loaded = Loaded { member: Some((w.cid.clone(), 1)), ..Default::default() };
    let wit = Witness::open(key("cassn0"), w.reg.clone(), &w.cid, Store::memory(), loaded, clock(&now)).unwrap();
    let (ra, sa, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "a");
    assert_eq!(wit.spend(&ra).0, Err(Error::Rejected("own charter version unknown".into())));
    assert!(wit.record(&sa).is_none());
    let standby = obj([("constellation", Json::str(&w.cid)), ("version", Json::Int(1)), ("since", Json::Int(0))]);
    let loaded = Loaded { standby: Some(standby), ..Default::default() };
    let k = Standby::open(key("cassk0"), w.reg.clone(), &w.cid, Store::memory(), loaded, clock(&now), false).unwrap();
    now.fetch_add(10 * DEAD as i64, Ordering::SeqCst);
    assert!(!k.dead());
    assert_eq!(k.succeed(&w.next, None).0, Err(Error::Rejected("own charter version unknown".into())));
}

async fn http(addr: std::net::SocketAddr, method: &str, path: &str, auth: Option<&str>, body: &str) -> (u16, Json) {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    let mut s = tokio::net::TcpStream::connect(addr).await.unwrap();
    let auth = auth.map(|a| format!("Authorization: {a}\r\n")).unwrap_or_default();
    let req = format!(
        "{method} {path} HTTP/1.1\r\nHost: t\r\nConnection: close\r\nContent-Type: application/json\r\n{auth}Content-Length: {}\r\n\r\n{body}",
        body.len()
    );
    s.write_all(req.as_bytes()).await.unwrap();
    let mut out = Vec::new();
    s.read_to_end(&mut out).await.unwrap();
    let text = String::from_utf8(out).unwrap();
    let code = text[9..12].parse().unwrap();
    let json = text.split_once("\r\n\r\n").map(|(_, b)| b).unwrap_or("");
    (code, parse(json.as_bytes()).unwrap_or(Json::Null))
}

async fn listen(app: axum::Router) -> std::net::SocketAddr {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move { sigil_witness::server::serve(listener, app, None, std::future::pending()).await.unwrap() });
    addr
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn standby_over_http() {
    let w = world("orion");
    let wit = Arc::new(Witness::open(key("orionw0"), w.reg.clone(), &w.cid, Store::memory(), Default::default(), sigil_witness::witness::system_clock()).unwrap());
    let waddr = listen(sigil_witness::server::router(wit.clone())).await;
    let k = Arc::new(
        Standby::open(key("orionk0"), w.reg.clone(), &w.cid, Store::memory(), Default::default(), sigil_witness::witness::system_clock(), false).unwrap(),
    );
    let limiter = Arc::new(RateLimiter::new(0.001, 1).unwrap());
    let members = vec![format!("http://{waddr}")];
    let addr = listen(sigil_witness::server::standby_router(k.clone(), Some("t".into()), Some(limiter), members)).await;
    let open_addr = listen(sigil_witness::server::standby_router(k.clone(), None, None, vec![])).await;

    let (c, info) = http(open_addr, "GET", "/v0/info", None, "").await;
    let info = info.get("ok").unwrap().clone();
    assert_eq!((c, info.get("role"), info.get("version"), info.get("fenced")), (200, Some(&Json::str("standby")), Some(&Json::Int(0)), Some(&Json::Bool(false))));
    // Operator calls: disabled without a token, refused with a wrong one, never rate limited.
    let (c, r) = http(open_addr, "POST", "/v0/probe", Some("Bearer t"), "{}").await;
    assert_eq!((c, r.get("message").and_then(Json::as_str)), (403, Some("rotation calls are disabled on this witness (no admin token)")));
    let (c, _) = http(addr, "POST", "/v0/succeed", Some("Bearer x"), "{}").await;
    assert_eq!(c, 403);
    for _ in 0..3 {
        // The default member list: the witness answers our challenge over HTTP.
        let (c, r) = http(addr, "POST", "/v0/probe", Some("Bearer t"), "{}").await;
        assert_eq!((c, r.get("ok").and_then(|o| o.get("answered"))), (200, Some(&Json::Int(1))));
    }
    let (c, r) = http(addr, "POST", "/v0/probe", Some("Bearer t"), r#"{"urls":["http://127.0.0.1:9"]}"#).await;
    assert_eq!((c, r.get("ok").and_then(|o| o.get("answered"))), (200, Some(&Json::Int(0))), "an unreachable member does not count");
    let (c, _) = http(addr, "POST", "/v0/probe", Some("Bearer t"), r#"{"urls":"x"}"#).await;
    assert_eq!(c, 400);
    let (c, _) = http(addr, "POST", "/v0/standby", Some("Bearer t"), &format!(r#"{{"constellation":"{}","version":0,"snapshots":{{}}}}"#, w.cid)).await;
    assert_eq!(c, 400, "snapshots must be a list");
    let (c, r) = http(addr, "POST", "/v0/standby", Some("Bearer t"), &format!(r#"{{"constellation":"{}","version":0,"snapshots":[]}}"#, w.cid)).await;
    assert_eq!((c, r.get("ok").and_then(|o| o.get("version"))), (200, Some(&Json::Int(0))), "a retried STANDBY");

    // MIRROR is charged to the client's bucket (burst 1).
    let (ra, _, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "a");
    let body = obj([("request", with_version(&ra, 0))]).canonical_string();
    let (c, r) = http(addr, "POST", "/v0/mirror", None, &body).await;
    assert_eq!(c, 200, "{}", r.canonical_string());
    let (c, _) = http(addr, "POST", "/v0/mirror", None, &body).await;
    assert_eq!(c, 429);
    let (c, r) = http(open_addr, "POST", "/v0/spend", None, &body).await;
    assert_eq!((c, r.get("error").and_then(Json::as_str)), (400, Some("bad_request")), "a standby member is not a witness");
    let (c, r) = http(waddr, "POST", "/v0/heartbeat", None, r#"{"challenge":"abc"}"#).await;
    assert_eq!((c, r.get("ok").and_then(|o| o.get("challenge"))), (200, Some(&Json::str("abc"))));
}
