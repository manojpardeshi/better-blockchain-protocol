//! Durable witness state with group commit.
//!
//! A witness that forgets a vote after a crash could vote again for another transition at the
//! same `(sigil, gen)`: equivocation. So every state change is made durable *before* any reply
//! that depends on it leaves the process (SPEC §5).
//!
//! State is a key/value table in [redb](https://docs.rs/redb): key `"<kind>\0<key>"`, value
//! the canonical JSON of the current value. Kinds are those of `sigil/store.py`: `pk`,
//! `member` (`[cid, version]`), `frozen`, `record` (key = sigil, value = the record as the
//! reference's `asdict(Record)`). Each commit uses `Durability::Immediate`, i.e. redb's
//! checksummed commit followed by `fdatasync`, so a commit that returned survives a crash or
//! power loss and a batch lands entirely or not at all.
//!
//! **Group commit.** Callers `submit` a batch of entries while holding the witness state lock
//! and get a sequence number; they then release the lock and wait until the writer thread
//! reports that sequence durable. The writer drains everything queued into one transaction,
//! so N concurrent spends cost one fsync instead of N. A reply never leaves before everything
//! submitted up to the moment its state was read is durable, which is exactly "persist before
//! answering". If a commit fails the process aborts: in-memory state is then ahead of the disk,
//! and continuing could equivocate after a restart.

use std::collections::HashMap;
use std::path::Path;
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use redb::{Database, Durability, ReadableTable, TableDefinition};

use crate::json::{parse_with_depth, Json, MAX_DEPTH};

const STATE: TableDefinition<&str, &[u8]> = TableDefinition::new("state");

/// One durable fact: `(kind, key, value)`.
pub type Entry = (String, String, Json);

/// What a store held at startup.
#[derive(Debug, Default)]
pub struct Loaded {
    pub pk: Option<String>,
    pub member: Option<(String, i128)>,
    pub frozen: bool,
    pub records: HashMap<String, Json>,
}

struct Progress {
    durable: u64,
    closed: bool,
}

struct Shared {
    progress: Mutex<Progress>,
    cond: Condvar,
    watch: tokio::sync::watch::Sender<u64>,
}

pub struct Store {
    tx: Mutex<Option<mpsc::Sender<(u64, Vec<Entry>)>>>,
    submitted: Mutex<u64>,
    shared: Arc<Shared>,
    writer: Mutex<Option<thread::JoinHandle<()>>>,
    memory: bool,
}

impl Store {
    /// Open (or create) a durable store at `path`, returning it and what it holds.
    pub fn open(path: impl AsRef<Path>) -> Result<(Arc<Store>, Loaded), String> {
        let db = Database::create(path.as_ref()).map_err(|e| format!("cannot open store: {e}"))?;
        let loaded = load(&db)?;
        let shared = Arc::new(Shared {
            progress: Mutex::new(Progress { durable: 0, closed: false }),
            cond: Condvar::new(),
            watch: tokio::sync::watch::channel(0).0,
        });
        let (tx, rx) = mpsc::channel::<(u64, Vec<Entry>)>();
        let sh = shared.clone();
        let writer = thread::Builder::new()
            .name("sigil-store".into())
            .spawn(move || writer_loop(db, rx, sh))
            .map_err(|e| e.to_string())?;
        Ok((
            Arc::new(Store {
                tx: Mutex::new(Some(tx)),
                submitted: Mutex::new(0),
                shared,
                writer: Mutex::new(Some(writer)),
                memory: false,
            }),
            loaded,
        ))
    }

    /// A store that keeps nothing (benchmarks and tests only: a restart forgets every vote).
    pub fn memory() -> Arc<Store> {
        Arc::new(Store {
            tx: Mutex::new(None),
            submitted: Mutex::new(0),
            shared: Arc::new(Shared {
                progress: Mutex::new(Progress { durable: 0, closed: false }),
                cond: Condvar::new(),
                watch: tokio::sync::watch::channel(0).0,
            }),
            writer: Mutex::new(None),
            memory: true,
        })
    }

    pub fn is_memory(&self) -> bool {
        self.memory
    }

    /// Queue `entries` as one atomic batch; returns its sequence number. Call this while
    /// holding the lock that orders the state changes, so batches are written in that order.
    pub fn submit(&self, entries: Vec<Entry>) -> u64 {
        let mut n = self.submitted.lock().expect("store lock");
        *n += 1;
        let seq = *n;
        if self.memory {
            self.mark_durable(seq);
            return seq;
        }
        let tx = self.tx.lock().expect("store lock");
        match tx.as_ref() {
            Some(tx) if tx.send((seq, entries)).is_ok() => {}
            _ => {
                eprintln!("sigil-witness: store is closed; refusing to continue");
                std::process::abort();
            }
        }
        seq
    }

    /// The newest sequence number handed out so far.
    pub fn last_submitted(&self) -> u64 {
        *self.submitted.lock().expect("store lock")
    }

    fn mark_durable(&self, seq: u64) {
        let mut p = self.shared.progress.lock().expect("store lock");
        if seq > p.durable {
            p.durable = seq;
        }
        drop(p);
        self.shared.watch.send_replace(seq);
        self.shared.cond.notify_all();
    }

    /// Block until batch `seq` (and every earlier one) is durable.
    pub fn wait(&self, seq: u64) {
        let mut p = self.shared.progress.lock().expect("store lock");
        while p.durable < seq {
            if p.closed {
                eprintln!("sigil-witness: store closed before a write became durable");
                std::process::abort();
            }
            p = self.shared.cond.wait(p).expect("store lock");
        }
    }

    /// Wait asynchronously until batch `seq` is durable.
    pub async fn wait_async(&self, seq: u64) {
        let mut rx = self.shared.watch.subscribe();
        if *rx.borrow() >= seq {
            return;
        }
        if rx.wait_for(|d| *d >= seq).await.is_err() {
            eprintln!("sigil-witness: store writer stopped");
            std::process::abort();
        }
    }

    /// Flush everything queued and stop the writer.
    pub fn close(&self) {
        self.tx.lock().expect("store lock").take();
        if let Some(w) = self.writer.lock().expect("store lock").take() {
            let _ = w.join();
        }
    }
}

impl Drop for Store {
    fn drop(&mut self) {
        self.close();
    }
}

fn writer_loop(db: Database, rx: mpsc::Receiver<(u64, Vec<Entry>)>, shared: Arc<Shared>) {
    while let Ok(first) = rx.recv() {
        let mut batch = vec![first];
        while let Ok(more) = rx.try_recv() {
            batch.push(more);
            if batch.len() >= 4096 {
                break;
            }
        }
        let last = batch.last().map(|(s, _)| *s).unwrap_or(0);
        if let Err(e) = commit(&db, &batch) {
            eprintln!("sigil-witness: store commit failed ({e}); aborting so no vote is ever forgotten");
            std::process::abort();
        }
        {
            let mut p = shared.progress.lock().expect("store lock");
            p.durable = last;
        }
        shared.watch.send_replace(last);
        shared.cond.notify_all();
    }
    let mut p = shared.progress.lock().expect("store lock");
    p.closed = true;
    drop(p);
    shared.cond.notify_all();
}

fn commit(db: &Database, batch: &[(u64, Vec<Entry>)]) -> Result<(), redb::Error> {
    let mut txn = db.begin_write()?;
    txn.set_durability(Durability::Immediate);
    {
        let mut t = txn.open_table(STATE)?;
        for (_, entries) in batch {
            for (kind, key, value) in entries {
                let k = format!("{kind}\0{key}");
                t.insert(k.as_str(), value.canonical().as_slice())?;
            }
        }
    }
    txn.commit()?;
    Ok(())
}

fn load(db: &Database) -> Result<Loaded, String> {
    let mut out = Loaded::default();
    let txn = db.begin_read().map_err(|e| e.to_string())?;
    let t = match txn.open_table(STATE) {
        Ok(t) => t,
        Err(redb::TableError::TableDoesNotExist(_)) => return Ok(out),
        Err(e) => return Err(e.to_string()),
    };
    for item in t.iter().map_err(|e| e.to_string())? {
        let (k, v) = item.map_err(|e| e.to_string())?;
        let (kind, key) = k.value().split_once('\0').ok_or("corrupt store key")?;
        // A record nests what a request carried a few levels deeper, so it gets more depth than
        // a request: anything the witness accepted must load again after a restart.
        let value = parse_with_depth(v.value(), MAX_DEPTH + 16).map_err(|e| format!("corrupt store value: {e}"))?;
        match kind {
            "pk" => out.pk = value.as_str().map(str::to_string),
            "member" => {
                let a = value.as_arr().ok_or("corrupt member entry")?;
                let cid = a.first().and_then(Json::as_str).ok_or("corrupt member entry")?;
                let ver = a.get(1).and_then(Json::as_int).ok_or("corrupt member entry")?;
                out.member = Some((cid.to_string(), ver));
            }
            // `true` in older stores, the successor charter's hash since successor binding.
            // Anything but false/null is frozen: misreading it must fail closed.
            "frozen" => out.frozen = !matches!(value, Json::Bool(false) | Json::Null),
            "record" => {
                out.records.insert(key.to_string(), value);
            }
            _ => return Err(format!("unknown store entry kind {kind:?}")),
        }
    }
    Ok(out)
}
