//! Stores in older formats still open (BENCHMARKS.md: "stores written before rotation was
//! ported load unchanged"; store.rs: `frozen` is `true` in stores written before successor
//! binding).
//!
//! `write_raw_store` is a fixture writer for `tests/integration/test_store_compat.py` (run with
//! `--ignored`): it writes the `(kind, key, value)` entries of the JSON file `$SIGIL_RAW_ENTRIES`
//! (`[[kind, key, canonical JSON text], …]`) verbatim into a fresh redb store at
//! `$SIGIL_RAW_STORE`, the way the store's writer lays them out, so a test can build a store
//! as an older version wrote it without that version's code.

use redb::{Database, TableDefinition};
use sigil_witness::charter::Registry;
use sigil_witness::crypto::KeyPair;
use sigil_witness::json::{parse, Json};
use sigil_witness::store::Store;
use sigil_witness::testkit::{genesis, spend_request};
use sigil_witness::witness::{system_clock, Error, Witness};

const STATE: TableDefinition<&str, &[u8]> = TableDefinition::new("state");

fn write_raw(path: &std::path::Path, entries: &[(String, String, Vec<u8>)]) {
    let db = Database::create(path).unwrap();
    let txn = db.begin_write().unwrap();
    {
        let mut t = txn.open_table(STATE).unwrap();
        for (kind, key, value) in entries {
            t.insert(format!("{kind}\0{key}").as_str(), value.as_slice()).unwrap();
        }
    }
    txn.commit().unwrap();
}

#[test]
#[ignore]
fn write_raw_store() {
    let src = std::env::var("SIGIL_RAW_ENTRIES").expect("SIGIL_RAW_ENTRIES");
    let out = std::env::var("SIGIL_RAW_STORE").expect("SIGIL_RAW_STORE");
    let v = parse(&std::fs::read(src).unwrap()).unwrap();
    let entries: Vec<(String, String, Vec<u8>)> = v
        .as_arr()
        .unwrap()
        .iter()
        .map(|e| {
            let a = e.as_arr().unwrap();
            (a[0].as_str().unwrap().to_string(), a[1].as_str().unwrap().to_string(), a[2].as_str().unwrap().as_bytes().to_vec())
        })
        .collect();
    write_raw(std::path::Path::new(&out), &entries);
}

#[test]
fn frozen_true_and_records_without_candidates_load() {
    let dir = std::env::temp_dir().join(format!("sigil-legacy-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&dir).unwrap();
    let keys: Vec<KeyPair> = (0..4).map(|i| KeyPair::from_py_seed(format!("w{i}").as_bytes())).collect();
    let (cid, regj) = genesis("orion", &keys.iter().collect::<Vec<_>>());
    let reg = Registry::from_json(&regj).unwrap();
    let owner = KeyPair::from_py_seed(b"owner");
    let (r1, sigil, _) = spend_request(&owner, &cid, "aa", 0, 1i128 << 40, "one");
    // A current store holding one vote, to borrow a well-formed record from.
    let fresh = dir.join("fresh.redb");
    let (store, loaded) = Store::open(&fresh).unwrap();
    let w = Witness::open(KeyPair::from_py_seed(b"w0"), reg.clone(), &cid, store, loaded, system_clock()).unwrap();
    let (vote, seq) = w.spend(&r1);
    w.store.wait(seq);
    let vote = vote.unwrap();
    let status = w.status(&Json::str(&sigil)).0.unwrap();
    w.store.close();
    drop(w);
    let (_s, loaded) = Store::open(&fresh).unwrap();
    let mut rec = loaded.records.get(&sigil).unwrap().clone();
    drop(_s);
    if let Json::Obj(m) = &mut rec {
        assert!(m.remove("candidates").is_some());
    }
    let pk = KeyPair::from_py_seed(b"w0").pk;
    for frozen in [false, true] {
        let path = dir.join(format!("legacy-{frozen}.redb"));
        let mut entries = vec![
            ("pk".to_string(), String::new(), Json::str(&pk).canonical()),
            ("member".into(), String::new(), Json::Arr(vec![Json::str(&cid), Json::Int(0)]).canonical()),
            ("record".into(), sigil.clone(), rec.canonical()),
        ];
        if frozen {
            entries.push(("frozen".into(), String::new(), Json::Bool(true).canonical()));
        }
        write_raw(&path, &entries);
        let (store, loaded) = Store::open(&path).unwrap();
        assert_eq!((loaded.frozen, loaded.frozen_for.is_none()), (frozen, true));
        let w = Witness::open(KeyPair::from_py_seed(b"w0"), reg.clone(), &cid, store, loaded, system_clock()).unwrap();
        assert_eq!(w.status(&Json::str(&sigil)).0.unwrap(), status, "same STATUS from the legacy record");
        if frozen {
            assert!(matches!(w.spend(&r1).0, Err(Error::Rejected(_))), "a legacy frozen store never votes");
        } else {
            assert_eq!(w.spend(&r1).0.unwrap(), vote, "the legacy record's vote, byte for byte");
        }
        w.store.close();
    }
    let _ = std::fs::remove_dir_all(&dir);
}
