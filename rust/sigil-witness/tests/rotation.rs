//! Rotation (FREEZE/ADOPT/CONTESTED RELEASE), stamps and gossip on the real witness: durable
//! across restarts, and over HTTP with the admin token. The byte-for-byte comparison with the
//! reference is in vectors.rs; these tests cover what the vectors cannot (restarts, the server).

use std::sync::Arc;

use sigil_witness::charter::{charter_hash, Registry};
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{obj, parse, Json};
use sigil_witness::stamps::{blind, load_mint, to_hex, unblind, StampKey};
use sigil_witness::store::Store;
use sigil_witness::testkit::{genesis, seal_from_votes, spend_request};
use sigil_witness::witness::{system_clock, Error, Witness, CONTESTED};

struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(tag: &str) -> TempDir {
        let p = std::env::temp_dir().join(format!("sigil-rot-{tag}-{}-{}", std::process::id(), rand::random::<u64>()));
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

fn open(path: &str, seed: &str, reg: &Registry, cid: &str, adopt: bool) -> Witness {
    let (store, loaded) = Store::open(path).unwrap();
    Witness::open_with(KeyPair::from_py_seed(seed.as_bytes()), reg.clone(), cid, store, loaded, system_clock(), adopt).unwrap()
}

fn ok(o: (Result<Json, Error>, u64), w: &Witness) -> Json {
    w.store.wait(o.1);
    o.0.unwrap()
}

fn close(w: Witness) {
    w.store.close();
}

/// A constellation of 4 (seeds o0..o3) with a few bindings, and the body of the next charter.
struct World {
    cid: String,
    reg0: Registry,
    owner: KeyPair,
    next: Json,
}

fn world(tag: &str, new_seeds: &[&str]) -> World {
    let keys: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("{tag}o{i}").as_bytes())).collect();
    let (cid, regj) = genesis(tag, &keys.iter().collect::<Vec<_>>());
    let reg0 = Registry::from_json(&regj).unwrap();
    let body0 = reg0.charter(&cid, 0).unwrap().body.clone();
    let members: Vec<Json> = new_seeds.iter().map(|s| Json::str(KeyPair::from_py_seed(s.as_bytes()).pk)).collect();
    let next = obj([
        ("name", Json::str(tag)),
        ("version", Json::Int(1)),
        ("witnesses", Json::Arr(members)),
        ("prev", Json::str(charter_hash(&body0))),
    ]);
    World { cid, reg0, owner: KeyPair::from_py_seed(format!("{tag}owner").as_bytes()), next }
}

fn registry_v1(w: &World, sigs: Vec<(String, Json)>) -> Registry {
    let mut reg = w.reg0.clone();
    let mut chain = reg.raw_chain(&w.cid).to_vec();
    chain.push(obj([("body", w.next.clone()), ("sigs", Json::Obj(sigs.into_iter().collect()))]));
    reg.add_chain(&w.cid, &chain).unwrap();
    reg
}

#[test]
fn freeze_and_adopt_survive_restarts() {
    let dir = TempDir::new("restart");
    let w = world("orion", &["n0", "n1", "n2", "n3"]);
    let far = 1i128 << 40;
    let (ra, sa, _) = spend_request(&w.owner, &w.cid, "aa", 0, far, "a");
    let (rb1, sb, tb1) = spend_request(&w.owner, &w.cid, "bb", 0, far, "b1");
    let (rb2, _, tb2) = spend_request(&w.owner, &w.cid, "bb", 0, far, "b2");

    // Old members: all bind a; the owner equivocates on b (o0..o2 vote b1, o3 votes b2).
    let mut sigs = Vec::new();
    let mut snaps = Vec::new();
    let mut b1_votes = Vec::new();
    for i in 0..4 {
        let p = dir.path(&format!("o{i}.redb"));
        let o = open(&p, &format!("oriono{i}"), &w.reg0, &w.cid, false);
        ok(o.spend(&ra), &o);
        let v = ok(o.spend(if i < 3 { &rb1 } else { &rb2 }), &o);
        if i < 3 {
            b1_votes.push(v);
        }
        let f = ok(o.freeze(&w.next), &o);
        close(o);
        // Restarted, the witness is still frozen, for this successor only.
        let o = open(&p, &format!("oriono{i}"), &w.reg0, &w.cid, false);
        assert!(o.frozen());
        assert_eq!(o.spend(&ra).0, Err(Error::Rejected("witness not active".into())));
        let again = ok(o.freeze(&w.next), &o);
        assert_eq!(again, f, "re-freezing for the same successor signs and hands over the same");
        let mut other = w.next.clone();
        if let Json::Obj(m) = &mut other {
            m.insert("witnesses".into(), Json::Arr(vec![Json::str("ab".repeat(32))]));
        }
        assert_eq!(o.freeze(&other).0, Err(Error::Rejected("already frozen for a different successor charter".into())));
        sigs.push((o.pk.clone(), f.get("sig").unwrap().clone()));
        snaps.push(f.get("snapshot").unwrap().clone());
        close(o);
    }
    let reg1 = registry_v1(&w, sigs);

    // A new member waits for ADOPT (restarting it before then changes nothing).
    let p = dir.path("n0.redb");
    let n = open(&p, "n0", &reg1, &w.cid, true);
    assert_eq!((n.cid(), n.version()), (None, None));
    assert_eq!(n.spend(&ra).0, Err(Error::Rejected("witness not active".into())));
    close(n);
    // Without --adopt a fresh store refuses to start on a rotated constellation.
    let (store, loaded) = Store::open(&dir.path("fresh.redb")).unwrap();
    assert!(Witness::open(KeyPair::from_py_seed(b"n1"), reg1.clone(), &w.cid, store, loaded, system_clock()).is_err());

    let n = open(&p, "n0", &reg1, &w.cid, true);
    let cid = Json::str(&w.cid);
    assert!(matches!(n.adopt_once(&cid, &Json::Int(0), &snaps).0, Err(Error::BadRequest(_))), "not a member of v0");
    ok(n.adopt_once(&cid, &Json::Int(1), &snaps), &n);
    assert_eq!(ok(n.adopt_once(&cid, &Json::Int(1), &snaps), &n).get("version"), Some(&Json::Int(1)), "a retry answers the same");
    assert!(matches!(n.adopt_once(&cid, &Json::Int(2), &snaps).0, Err(Error::Rejected(_))));
    let va = ok(n.spend(&ra), &n);
    assert_eq!(va.get("version"), Some(&Json::Int(1)));
    close(n);

    let n = open(&p, "n0", &reg1, &w.cid, false); // restored from its store, --adopt or not
    assert_eq!((n.cid(), n.version()), (Some(w.cid.clone()), Some(1)));
    assert_eq!(ok(n.spend(&ra), &n), va, "same vote after a restart");
    let rec = n.record(&sb).unwrap();
    assert_eq!(rec.tid.as_deref(), Some(CONTESTED));
    let mut cands: Vec<String> = rec.candidates.iter().map(|c| c.1.clone()).collect();
    cands.sort();
    let mut want = vec![tb1.clone(), tb2.clone()];
    want.sort();
    assert_eq!(cands, want);
    assert!(matches!(n.spend(&rb1).0, Err(Error::Conflict(None))), "contested: never votes");

    // b1's seal proves b2 dead, and b1 is then the only candidate left and provably sealed:
    // the record binds to b1 at generation 0 (SPEC §5.2), and the seal is logged.
    let seal = seal_from_votes(&b1_votes);
    let parcel = obj([
        ("home", Json::str(&w.cid)),
        ("lock", rb1.get("lock").unwrap().clone()),
        ("salt", Json::str("bb")),
    ]);
    let proof = obj([
        ("kind", "seal".into()),
        ("sigil", Json::str(&sb)),
        ("gen", Json::Int(0)),
        ("parcel", parcel),
        ("seal", seal),
    ]);
    assert_eq!(ok(n.release(&Json::str(&sb), &proof), &n), Json::Int(0));
    close(n);
    let n = open(&p, "n0", &reg1, &w.cid, false);
    let rec = n.record(&sb).unwrap();
    assert_eq!((rec.gen, rec.tid.as_deref(), rec.candidates.len()), (0, Some(tb1.as_str()), 0));
    assert!(rec.log.iter().any(|e| e.get("kind").and_then(Json::as_str) == Some("seal")));
    // b1 is sealed, not dead: its own seal does not release it.
    assert_eq!(n.release(&Json::str(&sb), &proof).0, Err(Error::Rejected("invalid death proof".into())));
    assert!(n.spend(&rb1).0.is_ok(), "bound to the sealed b1: voting it again creates no second seal");
    let st = ok(n.status(&Json::str(&sa)), &n);
    assert_eq!(st.get("votes").and_then(Json::as_arr).map(Vec::len), Some(1));
    close(n);
}

#[test]
fn redeemed_stamps_survive_restarts() {
    let dir = TempDir::new("stamps");
    let w = world("lyra", &["x"]);
    let mint = dir.path("w.redb.stamps.json");
    let key = load_mint(&mint, 512).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(std::fs::metadata(&mint).unwrap().permissions().mode() & 0o777, 0o600);
    }
    let again = load_mint(&mint, 512).unwrap();
    assert_eq!((again.n.clone(), again.e.clone()), (key.n.clone(), key.e.clone()), "the key is kept across restarts");

    let p = dir.path("w.redb");
    let o = open(&p, "lyrao0", &w.reg0, &w.cid, false).with_stamps(load_mint(&mint, 512).unwrap());
    let info = o.info();
    let pubn = sigil_witness::stamps::parse_hex(info.get("stamps").unwrap().get("n").unwrap().as_str().unwrap()).unwrap();
    assert_eq!(pubn, key.n);
    let r = num_bigint_dig::BigUint::from(987_654_321u64);
    let blinded = blind(&key.n, &key.e, "c0ffee", &r);
    let bsig = ok(o.sell_stamp(&Json::str(to_hex(&blinded))), &o);
    let sig = unblind(&key.n, &sigil_witness::stamps::parse_hex(bsig.as_str().unwrap()).unwrap(), &r).unwrap();
    let stamp = obj([("serial", Json::str("c0ffee")), ("sig", Json::str(to_hex(&sig)))]);
    let (mut req, _, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "m");
    if let Json::Obj(m) = &mut req {
        m.insert("stamp".into(), stamp.clone());
    }
    ok(o.spend(&req), &o);
    close(o);
    let o = open(&p, "lyrao0", &w.reg0, &w.cid, false).with_stamps(StampKey::from_json(&key.numbers_json()).unwrap());
    let (mut req2, _, _) = spend_request(&w.owner, &w.cid, "bb", 0, 1 << 40, "m");
    if let Json::Obj(m) = &mut req2 {
        m.insert("stamp".into(), stamp);
    }
    assert_eq!(o.spend(&req2).0, Err(Error::Rejected("missing or spent stamp".into())), "redeemed before the restart");
    close(o);
}

// ------------------------------------------------------------------------------- HTTP

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

async fn serve(w: Arc<Witness>, token: Option<&str>) -> std::net::SocketAddr {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    let app = sigil_witness::server::router_with_admin(w, token.map(str::to_string));
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    addr
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rotation_calls_need_the_admin_token() {
    let w = world("vega", &["m0"]);
    let o = Arc::new(Witness::open(KeyPair::from_py_seed(b"vegao0"), w.reg0.clone(), &w.cid, Store::memory(), Default::default(), system_clock()).unwrap());
    let open_addr = serve(o.clone(), None).await;
    let addr = serve(o.clone(), Some("s3cret")).await;
    let body = obj([("charter", w.next.clone())]).canonical_string();
    let (c, r) = http(open_addr, "POST", "/v0/freeze", Some("Bearer s3cret"), &body).await;
    assert_eq!((c, r.get("message").and_then(Json::as_str)), (403, Some("rotation calls are disabled on this witness (no admin token)")));
    for bad in [None, Some("Bearer s3cre"), Some("Bearer s3cret2"), Some("s3cret"), Some("bearer s3cret")] {
        let (c, r) = http(addr, "POST", "/v0/freeze", bad, &body).await;
        assert_eq!((c, r.get("message").and_then(Json::as_str)), (403, Some("bad admin token")), "{bad:?}");
    }
    assert!(!o.frozen());
    // Spends go through the blocking pool and still answer.
    let (req, _, _) = spend_request(&w.owner, &w.cid, "aa", 0, 1 << 40, "m");
    let (c, _) = http(addr, "POST", "/v0/spend", None, &obj([("request", req.clone())]).canonical_string()).await;
    assert_eq!(c, 200);
    let (c, r) = http(addr, "POST", "/v0/freeze", Some("Bearer s3cret"), &body).await;
    assert_eq!(c, 200, "{}", r.canonical_string());
    let snap = r.get("ok").unwrap().get("snapshot").unwrap().clone();
    assert_eq!(snap.as_obj().map(|m| m.len()), Some(1));
    let (c, info) = http(addr, "GET", "/v0/info", None, "").await;
    assert_eq!((c, info.get("ok").unwrap().get("frozen")), (200, Some(&Json::Bool(true))));
    let (c, _) = http(addr, "POST", "/v0/spend", None, &obj([("request", req)]).canonical_string()).await;
    assert_eq!(c, 403);

    // The new member learns version 1 by gossip, then adopts over HTTP.
    let sig = r.get("ok").unwrap().get("sig").unwrap().clone();
    let mut chain = w.reg0.raw_chain(&w.cid).to_vec();
    let others: Vec<(String, Json)> = (1..4)
        .map(|i| {
            let k = KeyPair::from_py_seed(format!("vegao{i}").as_bytes());
            (k.pk.clone(), Json::str(k.sign("charter", &w.next)))
        })
        .collect();
    let mut sigs: Vec<(String, Json)> = vec![(o.pk.clone(), sig)];
    sigs.extend(others);
    chain.push(obj([("body", w.next.clone()), ("sigs", Json::Obj(sigs.into_iter().collect()))]));
    let m = Arc::new(
        Witness::open_with(KeyPair::from_py_seed(b"m0"), w.reg0.clone(), &w.cid, Store::memory(), Default::default(), system_clock(), true)
            .unwrap(),
    );
    let maddr = serve(m.clone(), Some("t")).await;
    let adopt = obj([("constellation", Json::str(&w.cid)), ("version", Json::Int(1)), ("snapshots", Json::Arr(vec![snap.clone()]))]).canonical_string();
    let (c, _) = http(maddr, "POST", "/v0/adopt", Some("Bearer t"), &adopt).await;
    assert_eq!(c, 400, "version 1 is not known yet");
    let gossip = obj([("charters", obj([(w.cid.as_str(), Json::Arr(chain))]))]).canonical_string();
    let (c, r) = http(maddr, "POST", "/v0/gossip", None, &gossip).await;
    assert_eq!((c, r.get("ok").unwrap().get("charters")), (200, Some(&Json::Int(1))));
    let (c, r) = http(maddr, "POST", "/v0/adopt", Some("Bearer t"), &adopt).await;
    assert_eq!((c, r.get("ok").unwrap().get("version")), (200, Some(&Json::Int(1))));
    let (c, _) = http(maddr, "POST", "/v0/adopt", Some("Bearer t"), &adopt).await;
    assert_eq!(c, 200, "a retried ADOPT answers the same");
    let bad = obj([("constellation", Json::str(&w.cid)), ("version", Json::Int(1)), ("snapshots", Json::Obj(Default::default()))]).canonical_string();
    let (c, _) = http(maddr, "POST", "/v0/adopt", Some("Bearer t"), &bad).await;
    assert_eq!(c, 400, "snapshots must be a list");
    let (c, charters) = http(maddr, "GET", "/v0/charters", None, "").await;
    assert_eq!(c, 200);
    assert_eq!(charters.get("ok").unwrap().get(&w.cid).and_then(Json::as_arr).map(Vec::len), Some(2));
    assert_eq!((m.cid(), m.version()), (Some(w.cid.clone()), Some(1)));
    let (c, p) = http(maddr, "GET", "/v0/proofs", None, "").await;
    assert_eq!((c, p.get("ok").unwrap().canonical_string()), (200, r#"{"forks":[],"proofs":[]}"#.to_string()));
}
