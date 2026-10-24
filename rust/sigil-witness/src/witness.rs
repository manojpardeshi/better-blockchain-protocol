//! The witness (SPEC §5): SPEND, RELEASE and STATUS, with durable state.
//!
//! Mirrors `sigil/witness.py`. Per sigil an honest witness keeps a generation counter and at
//! most one binding per generation, and votes at most once per `(sigil, generation)`. Rotation
//! (FREEZE/ADOPT, SPEC §5.4) is not implemented: records keep the `log` a successor would need,
//! in the reference's format, so it can be added without migrating stores.
//!
//! Concurrency: signature checks run without any lock; the record update runs under one state
//! mutex and submits its write to the store before releasing it; the caller then waits for the
//! store to report that write (and every earlier one) durable before it answers.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use crate::charter::{short, Registry};
use crate::crypto::KeyPair;
use crate::json::{obj, Json};
use crate::locks::evaluate;
use crate::model::{sigil_of, transition_id, vote_payload};
use crate::proofs::proves_dead;
use crate::store::{Entry, Loaded, Store};

pub const CONTESTED: &str = "!contested";

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    /// The witness declined (HTTP 403 `rejected`).
    Rejected(String),
    /// Already bound to a different transition at this generation (HTTP 409), with our vote.
    Conflict(Option<Json>),
    /// Malformed request (HTTP 400 `bad_request`).
    BadRequest(String),
}

fn rejected<T>(msg: &str) -> Result<T, Error> {
    Err(Error::Rejected(msg.to_string()))
}

/// Per-sigil state, persisted as the reference's `asdict(Record)`.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Record {
    pub gen: i128,
    pub tid: Option<String>,
    pub header: Option<Json>,
    pub vote: Option<Json>,
    pub log: Vec<Json>,
    pub votes: Vec<Json>,
    pub abstain: bool,
}

impl Record {
    pub fn to_json(&self) -> Json {
        obj([
            ("gen", Json::Int(self.gen)),
            ("tid", self.tid.clone().into()),
            ("header", self.header.clone().unwrap_or(Json::Null)),
            ("vote", self.vote.clone().unwrap_or(Json::Null)),
            ("log", Json::Arr(self.log.clone())),
            ("votes", Json::Arr(self.votes.clone())),
            ("abstain", Json::Bool(self.abstain)),
        ])
    }

    pub fn from_json(v: &Json) -> Option<Record> {
        let opt = |k: &str| v.get(k).filter(|x| !x.is_null()).cloned();
        Some(Record {
            gen: v.get("gen")?.as_int()?,
            tid: match v.get("tid")? {
                Json::Null => None,
                Json::Str(s) => Some(s.clone()),
                _ => return None,
            },
            header: opt("header"),
            vote: opt("vote"),
            log: v.get("log")?.as_arr()?.clone(),
            votes: v.get("votes")?.as_arr()?.clone(),
            abstain: v.get("abstain")? == &Json::Bool(true),
        })
    }
}

/// `authorises`: validate an owner authorisation, returning the `(gen, tid)` it binds.
/// `now` is the clock for time locks (`None`: time conditions hold, as for a holder or ADOPT).
/// `Err` is the reference's uncaught `AttributeError` on a non-object unlock (HTTP 400).
pub fn authorises(sigil: &Json, auth: &Json, now: Option<i128>, batch: bool) -> Result<Option<(i128, String)>, Error> {
    let null = Json::Null;
    let get = |k: &str| auth.get(k).unwrap_or(&null);
    let Some(sigil) = sigil.as_str() else { return Ok(None) };
    let header = get("header");
    let Some(inputs) = header.get("inputs").and_then(Json::as_arr) else { return Ok(None) };
    if sigil_of(get("home"), get("lock"), get("salt")) != sigil {
        return Ok(None);
    }
    let mut sigils: Vec<&str> = Vec::with_capacity(inputs.len());
    let mut gens = Vec::new();
    for inp in inputs {
        let Some([s, g]) = inp.as_arr().map(Vec::as_slice).and_then(|a| <&[Json; 2]>::try_from(a).ok()) else {
            return Ok(None);
        };
        let Some(s) = s.as_str() else { return Ok(None) };
        if s == sigil {
            gens.push(g);
        }
        sigils.push(s);
    }
    let n = sigils.len();
    sigils.sort_unstable();
    sigils.dedup();
    if gens.len() != 1 || sigils.len() != n {
        return Ok(None);
    }
    let gen = match gens[0] {
        Json::Int(g) if *g >= 0 && *g < (1i128 << 62) => *g,
        _ => return Ok(None),
    };
    let unlock = get("unlock");
    if unlock.as_obj().is_none() {
        return Err(Error::BadRequest("unlock must be an object".into()));
    }
    if !matches!(unlock.get("expires"), Some(Json::Int(_))) {
        return Ok(None);
    }
    let tid = transition_id(header);
    if !evaluate(get("lock"), unlock, sigil, &tid, now, batch) {
        return Ok(None);
    }
    Ok(Some((gen, tid)))
}

pub type Clock = Box<dyn Fn() -> i128 + Send + Sync>;

pub fn system_clock() -> Clock {
    Box::new(|| {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as i128).unwrap_or(0)
    })
}

struct State {
    records: HashMap<String, Record>,
}

pub struct Witness {
    kp: KeyPair,
    pub pk: String,
    pub registry: Registry,
    pub cid: String,
    pub version: i128,
    state: Mutex<State>,
    /// Set by FREEZE (not implemented here, so only ever restored from a store): no more votes.
    frozen: bool,
    pub store: Arc<Store>,
    clock: Clock,
    /// Use Ed25519 batch verification for seals, death proofs and equivocation proofs.
    pub batch_verify: bool,
}

/// What a call returns, plus the store sequence its reply depends on.
pub type Outcome = (Result<Json, Error>, u64);

impl Witness {
    /// Restore a witness from its store, or join `cid` on first start (newest charter version
    /// that lists our key), exactly like `sigil.witnessd.build_witness`.
    pub fn open(kp: KeyPair, registry: Registry, cid: &str, store: Arc<Store>, loaded: Loaded, clock: Clock) -> Result<Witness, String> {
        if !registry.contains(cid) {
            return Err(format!("constellation {cid} is not in the registry"));
        }
        let mut setup: Vec<Entry> = Vec::new();
        match &loaded.pk {
            None => setup.push(("pk".into(), String::new(), Json::str(&kp.pk))),
            Some(pk) if *pk != kp.pk => return Err("store belongs to a different witness key".into()),
            _ => {}
        }
        let (cid, version) = match loaded.member {
            Some((c, v)) if c == cid => (c, v),
            Some((c, _)) => return Err(format!("store belongs to constellation {c}, not {cid}")),
            None => {
                let version = registry
                    .chain(cid)
                    .iter()
                    .filter(|c| c.is_member(&kp.pk))
                    .map(|c| c.version)
                    .max()
                    .ok_or_else(|| format!("{} is not a member of {}", short(&kp.pk), short(cid)))?;
                setup.push(("member".into(), String::new(), Json::Arr(vec![Json::str(cid), Json::Int(version)])));
                (cid.to_string(), version)
            }
        };
        if !setup.is_empty() {
            let seq = store.submit(setup);
            store.wait(seq);
        }
        let mut records = HashMap::with_capacity(loaded.records.len());
        for (s, r) in &loaded.records {
            records.insert(s.clone(), Record::from_json(r).ok_or_else(|| format!("corrupt record for {s}"))?);
        }
        Ok(Witness {
            pk: kp.pk.clone(),
            kp,
            registry,
            cid,
            version,
            state: Mutex::new(State { records }),
            frozen: loaded.frozen,
            store,
            clock,
            batch_verify: true,
        })
    }

    pub fn now(&self) -> i128 {
        (self.clock)()
    }

    pub fn frozen(&self) -> bool {
        self.frozen
    }

    fn vote(&self, sigil: &str, gen: i128, tid: &str, now: i128) -> Json {
        let mut v = obj([
            ("constellation", Json::str(&self.cid)),
            ("version", Json::Int(self.version)),
            ("witness", Json::str(&self.pk)),
            ("sigil", Json::str(sigil)),
            ("gen", Json::Int(gen)),
            ("tid", Json::str(tid)),
            ("time", Json::Int(now)),
        ]);
        let sig = self.kp.sign("vote", &vote_payload(&v).expect("complete vote"));
        if let Json::Obj(m) = &mut v {
            m.insert("sig".into(), Json::Str(sig));
        }
        v
    }

    fn persist(&self, sigil: &str, rec: &Record) -> u64 {
        self.store.submit(vec![("record".into(), sigil.to_string(), rec.to_json())])
    }

    /// SPEND (SPEC §5.1). `req` carries sigil, header, home, lock, salt, unlock.
    pub fn spend(&self, req: &Json) -> Outcome {
        let r = self.spend_inner(req);
        (r, self.store.last_submitted())
    }

    fn spend_inner(&self, req: &Json) -> Result<Json, Error> {
        if self.frozen() {
            return rejected("witness not active");
        }
        if req.as_obj().is_none() {
            return rejected("malformed request");
        }
        let null = Json::Null;
        let sigil_v = req.get("sigil").unwrap_or(&null);
        if req.get("home").and_then(Json::as_str) != Some(self.cid.as_str()) {
            return rejected("sigil does not live here");
        }
        let auth = obj(["home", "lock", "salt", "unlock", "header"].map(|k| (k, req.get(k).cloned().unwrap_or(Json::Null))));
        let now = self.now();
        // One evaluation against our clock suffices: the lock language is monotone, so a lock
        // satisfied at `now` is satisfied with time conditions ignored (the reference checks both).
        let (gen, tid) = match authorises(sigil_v, &auth, Some(now), self.batch_verify)? {
            Some(b) => b,
            None => {
                return match authorises(sigil_v, &auth, None, self.batch_verify)? {
                    Some(_) => rejected("lock not satisfied now"),
                    None => rejected("malformed request or lock not satisfied"),
                };
            }
        };
        let sigil = sigil_v.as_str().expect("authorised sigil is a string");
        let expires = auth.get("unlock").and_then(|u| u.get("expires")).and_then(Json::as_int).expect("checked");

        // The vote is fully determined by (sigil, gen, tid, now), so sign it before taking the
        // lock; it is only used (and only ever leaves) if the record logic below says so.
        let fresh = self.vote(sigil, gen, &tid, now);

        let mut st = self.state.lock().expect("state lock");
        // Fast path: already bound here at this generation (a repeated request, or a conflict).
        if let Some(r) = st.records.get(sigil) {
            if gen == r.gen {
                match (&r.tid, &r.vote) {
                    (Some(t), _) if *t != tid => return Err(Error::Conflict(r.vote.clone())),
                    (Some(_), Some(v)) => return Ok(v.clone()),
                    _ => {}
                }
            }
        }
        let mut rec = st.records.get(sigil).cloned().unwrap_or_default();
        if gen < rec.gen {
            return rejected("stale generation");
        }
        if gen > rec.gen {
            if rec.tid.is_some() {
                return rejected("bound at an earlier generation; release it first");
            }
            rec.gen = gen; // we never voted at the skipped generations: abstaining is safe
        }
        if rec.tid.is_none() {
            // Never *newly* bind on an expired authorisation.
            if now > expires {
                return rejected("authorisation expired");
            }
            rec.tid = Some(tid.clone());
            rec.header = auth.get("header").cloned();
            rec.log.push(obj([("kind", "bind".into()), ("gen", Json::Int(gen)), ("auth", auth)]));
        }
        if rec.tid.as_deref() != Some(tid.as_str()) {
            return Err(Error::Conflict(rec.vote.clone()));
        }
        if rec.vote.is_none() && rec.abstain {
            return rejected("this key already voted for another transition at this generation");
        }
        if rec.vote.is_none() {
            rec.vote = Some(fresh.clone());
            rec.votes.push(fresh);
        }
        // Past the fast path the record always changed (new binding, new generation or new vote).
        let vote = rec.vote.clone().expect("vote set");
        self.persist(sigil, &rec); // durable before the vote leaves (the caller waits)
        st.records.insert(sigil.to_string(), rec);
        Ok(vote)
    }

    /// RELEASE (SPEC §5.2): abandon the binding if `proof` shows it can never be sealed.
    pub fn release(&self, sigil: &Json, proof: &Json) -> Outcome {
        let r = self.release_inner(sigil, proof);
        (r, self.store.last_submitted())
    }

    fn release_inner(&self, sigil: &Json, proof: &Json) -> Result<Json, Error> {
        if matches!(sigil, Json::Arr(_) | Json::Obj(_)) {
            return Err(Error::BadRequest("unhashable sigil".into()));
        }
        if self.frozen() {
            return rejected("witness not active");
        }
        let Some(sigil) = sigil.as_str() else { return rejected("nothing to release") };
        // Verify against a snapshot, outside the lock, then re-check the record is unchanged.
        let snapshot = {
            let st = self.state.lock().expect("state lock");
            match st.records.get(sigil) {
                Some(r) if r.tid.is_some() && r.tid.as_deref() != Some(CONTESTED) => r.clone(),
                _ => return rejected("nothing to release"),
            }
        };
        let header = snapshot.header.clone().unwrap_or(Json::Null);
        let tid = snapshot.tid.clone().expect("bound");
        if !proves_dead(&header, &tid, proof, &self.registry, self.batch_verify) {
            return rejected("invalid death proof");
        }
        let mut st = self.state.lock().expect("state lock");
        let mut rec = match st.records.get(sigil) {
            Some(r) if r.gen == snapshot.gen && r.tid == snapshot.tid => r.clone(),
            _ => return rejected("record changed; retry"),
        };
        rec.log.push(obj([
            ("kind", "release".into()),
            ("gen", Json::Int(rec.gen)),
            ("tid", Json::str(&tid)),
            ("header", header),
            ("proof", proof.clone()),
        ]));
        rec.gen += 1;
        rec.tid = None;
        rec.header = None;
        rec.vote = None;
        rec.abstain = false;
        let gen = rec.gen;
        self.persist(sigil, &rec);
        st.records.insert(sigil.to_string(), rec);
        Ok(Json::Int(gen))
    }

    /// STATUS (SPEC §5.3): `{gen, tid, votes}`.
    pub fn status(&self, sigil: &Json) -> Outcome {
        if matches!(sigil, Json::Arr(_) | Json::Obj(_)) {
            return (Err(Error::BadRequest("unhashable sigil".into())), 0);
        }
        let st = self.state.lock().expect("state lock");
        let out = match sigil.as_str().and_then(|s| st.records.get(s)) {
            None => obj([("gen", Json::Int(0)), ("tid", Json::Null), ("votes", Json::Arr(vec![]))]),
            Some(r) => obj([("gen", Json::Int(r.gen)), ("tid", r.tid.clone().into()), ("votes", Json::Arr(r.votes.clone()))]),
        };
        let seq = self.store.last_submitted();
        drop(st);
        (Ok(out), seq)
    }

    /// `/v0/info`.
    pub fn info(&self) -> Json {
        obj([
            ("pk", Json::str(&self.pk)),
            ("constellation", Json::str(&self.cid)),
            ("version", Json::Int(self.version)),
            ("frozen", Json::Bool(self.frozen())),
            ("stamps", Json::Null),
        ])
    }

    pub fn record_count(&self) -> usize {
        self.state.lock().expect("state lock").records.len()
    }
}
