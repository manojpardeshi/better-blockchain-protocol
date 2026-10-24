//! Durable store: a reopened witness remembers every vote (SPEC §5), also under concurrency.

use std::sync::Arc;

use sigil_witness::charter::Registry;
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::Json;
use sigil_witness::proofs::verify_vote;
use sigil_witness::store::Store;
use sigil_witness::testkit::{genesis, spend_request};
use sigil_witness::witness::{system_clock, Error, Witness};

struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(tag: &str) -> TempDir {
        let p = std::env::temp_dir().join(format!("sigil-witness-{tag}-{}-{}", std::process::id(), rand::random::<u64>()));
        std::fs::create_dir_all(&p).unwrap();
        TempDir(p)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn open(path: &std::path::Path, kp: KeyPair, reg: &Registry, cid: &str) -> Witness {
    let (store, loaded) = Store::open(path).unwrap();
    Witness::open(kp, reg.clone(), cid, store, loaded, system_clock()).unwrap()
}

#[test]
fn reopened_witness_keeps_votes_and_refuses_conflicts() {
    let dir = TempDir::new("reopen");
    let keys: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("w{i}").as_bytes())).collect();
    let (cid, regj) = genesis("orion", &keys.iter().collect::<Vec<_>>());
    let reg = Registry::from_json(&regj).unwrap();
    let owner = KeyPair::from_py_seed(b"owner");
    let path = dir.0.join("w0.redb");
    let far = 1i128 << 40;
    let (r1, sigil, _) = spend_request(&owner, &cid, "aa", 0, far, "one");
    let (r2, _, _) = spend_request(&owner, &cid, "aa", 0, far, "two");

    let w = open(&path, KeyPair::from_py_seed(b"w0"), &reg, &cid);
    let (v1, seq) = w.spend(&r1);
    w.store.wait(seq);
    let v1 = v1.unwrap();
    assert!(verify_vote(&v1));
    w.store.close();
    drop(w);

    let w = open(&path, KeyPair::from_py_seed(b"w0"), &reg, &cid);
    assert_eq!(w.spend(&r1).0.unwrap(), v1, "same vote, byte for byte, after a restart");
    assert_eq!(w.spend(&r2).0, Err(Error::Conflict(Some(v1.clone()))));
    let st = w.status(&Json::str(&sigil)).0.unwrap();
    assert_eq!(st.get("votes").and_then(Json::as_arr).unwrap(), &vec![v1]);
    w.store.close();
    drop(w);

    // A store is bound to its key and constellation.
    let (store, loaded) = Store::open(&path).unwrap();
    assert!(Witness::open(KeyPair::from_py_seed(b"w1"), reg.clone(), &cid, store, loaded, system_clock()).is_err());
}

#[test]
fn group_commit_under_concurrency_loses_nothing() {
    let dir = TempDir::new("group");
    let keys: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("g{i}").as_bytes())).collect();
    let (cid, regj) = genesis("lyra", &keys.iter().collect::<Vec<_>>());
    let reg = Registry::from_json(&regj).unwrap();
    let path = dir.0.join("w.redb");
    let owner = Arc::new(KeyPair::from_py_seed(b"owner"));
    let w = Arc::new(open(&path, KeyPair::from_py_seed(b"g0"), &reg, &cid));
    let mut handles = Vec::new();
    for t in 0..8 {
        let (w, owner, cid) = (w.clone(), owner.clone(), cid.clone());
        handles.push(std::thread::spawn(move || {
            let mut out = Vec::new();
            for i in 0..25 {
                let (req, sigil, _) = spend_request(&owner, &cid, &format!("{t}-{i}"), 0, 1 << 40, "m");
                let (v, seq) = w.spend(&req);
                w.store.wait(seq);
                out.push((sigil, v.unwrap()));
            }
            out
        }));
    }
    let votes: Vec<(String, Json)> = handles.into_iter().flat_map(|h| h.join().unwrap()).collect();
    w.store.close();
    drop(w);
    let w = open(&path, KeyPair::from_py_seed(b"g0"), &reg, &cid);
    assert_eq!(w.record_count(), 200);
    for (sigil, v) in votes {
        let st = w.status(&Json::str(&sigil)).0.unwrap();
        assert_eq!(st.get("votes").and_then(Json::as_arr).unwrap(), &vec![v]);
    }
}
