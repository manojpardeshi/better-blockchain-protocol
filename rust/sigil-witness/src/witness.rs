//! The witness (SPEC §5): SPEND, RELEASE, STATUS, FREEZE and ADOPT, with durable state.
//!
//! Mirrors `sigil/witness.py`. Per sigil an honest witness keeps a generation counter and at
//! most one binding per generation, and votes at most once per `(sigil, generation)`, also
//! across charter versions: FREEZE hands the witness's evidence (bindings, releases and its
//! own votes) to the next version, and ADOPT inherits a binding only when the evidence shows
//! no sibling at its generation (otherwise the record is CONTESTED until RELEASE proves every
//! candidate dead).
//!
//! Concurrency: signature checks run without any lock; every record update runs under one
//! state mutex and submits its write to the store before releasing it; the caller then waits
//! for the store to report that write (and every earlier one) durable before it answers. The
//! membership, the frozen flag and the records live under that same mutex, so a SPEND or
//! RELEASE that raced a FREEZE is refused unless it committed before the FREEZE took its
//! snapshot of the evidence.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, RwLock};

use crate::charter::{charter_hash, short, Registry};
use crate::crypto::KeyPair;
use crate::gossip::{check_message, CowRegistry, GossipStore};
use crate::json::{obj, Json};
use crate::locks::evaluate;
use crate::model::{sigil_of, transition_id, vote_payload};
use crate::proofs::{proves_dead, verify_vote};
use crate::stamps::StampKey;
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

/// A CONTESTED record's live candidate binding `(gen, tid, header)`, still to be proven dead.
pub type Candidate = (i128, String, Json);

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
    pub candidates: Vec<Candidate>,
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
            (
                "candidates",
                Json::Arr(
                    self.candidates.iter().map(|(g, t, h)| Json::Arr(vec![Json::Int(*g), Json::str(t), h.clone()])).collect(),
                ),
            ),
        ])
    }

    /// The inverse of [`Record::to_json`]. `candidates` may be missing (stores written before
    /// rotation was ported): it is then empty.
    pub fn from_json(v: &Json) -> Option<Record> {
        let opt = |k: &str| v.get(k).filter(|x| !x.is_null()).cloned();
        let mut candidates = Vec::new();
        if let Some(cs) = v.get("candidates") {
            for c in cs.as_arr()? {
                let [g, t, h] = <&[Json; 3]>::try_from(c.as_arr()?.as_slice()).ok()?;
                candidates.push((g.as_int()?, t.as_str()?.to_string(), h.clone()));
            }
        }
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
            candidates,
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
    /// `(cid, version)` once joined (genesis) or adopted; `None` while awaiting ADOPT.
    member: Option<(String, i128)>,
    frozen: bool,
    /// The successor charter hash we froze for (`None` with `frozen` from an older store).
    frozen_for: Option<String>,
}

impl State {
    fn active(&self) -> Option<(String, i128)> {
        if self.frozen {
            None
        } else {
            self.member.clone()
        }
    }
}

pub struct Witness {
    kp: KeyPair,
    pub pk: String,
    /// The charter registry; gossip replaces it with a longer one (copy on write).
    registry: RwLock<Arc<Registry>>,
    gossip: Mutex<GossipStore>,
    state: Mutex<State>,
    stamps: Option<StampKey>,
    redeemed: Mutex<HashSet<String>>,
    pub store: Arc<Store>,
    clock: Clock,
    /// Use Ed25519 batch verification for seals, death proofs and equivocation proofs.
    pub batch_verify: bool,
}

/// What a call returns, plus the store sequence its reply depends on.
pub type Outcome = (Result<Json, Error>, u64);

/// Insertion-ordered map with the reference's `dict` semantics (a later insert of a known key
/// replaces the value in place).
struct OrderedMap<K, V> {
    keys: HashMap<K, usize>,
    items: Vec<(K, V)>,
}

impl<K: std::hash::Hash + Eq + Clone, V> OrderedMap<K, V> {
    fn new() -> Self {
        OrderedMap { keys: HashMap::new(), items: Vec::new() }
    }

    fn insert(&mut self, k: K, v: V) {
        match self.keys.get(&k) {
            Some(&i) => self.items[i].1 = v,
            None => {
                self.keys.insert(k.clone(), self.items.len());
                self.items.push((k, v));
            }
        }
    }

    fn get_mut_or_insert_with(&mut self, k: K, f: impl FnOnce() -> V) -> &mut V {
        let i = match self.keys.get(&k) {
            Some(&i) => i,
            None => {
                self.keys.insert(k.clone(), self.items.len());
                self.items.push((k, f()));
                self.items.len() - 1
            }
        };
        &mut self.items[i].1
    }
}

impl Witness {
    /// Restore a witness from its store, or join `cid` on first start, exactly like
    /// `sigil.witnessd.build_witness`: a fresh store joins version 0, and refuses to start if
    /// the constellation has rotated past it (a later version is entered only by ADOPT).
    pub fn open(kp: KeyPair, registry: Registry, cid: &str, store: Arc<Store>, loaded: Loaded, clock: Clock) -> Result<Witness, String> {
        Witness::open_with(kp, registry, cid, store, loaded, clock, false)
    }

    /// [`Witness::open`]; with `adopt`, a fresh store does not join anything and waits for
    /// ADOPT (`witnessd run --adopt`). A store that already joined is restored either way.
    pub fn open_with(
        kp: KeyPair,
        registry: Registry,
        cid: &str,
        store: Arc<Store>,
        loaded: Loaded,
        clock: Clock,
        adopt: bool,
    ) -> Result<Witness, String> {
        if !registry.contains(cid) {
            return Err(format!("constellation {cid} is not in the registry"));
        }
        let mut setup: Vec<Entry> = Vec::new();
        match &loaded.pk {
            None => setup.push(("pk".into(), String::new(), Json::str(&kp.pk))),
            Some(pk) if *pk != kp.pk => return Err("store belongs to a different witness key".into()),
            _ => {}
        }
        let member = match loaded.member {
            Some((c, v)) if c == cid => Some((c, v)),
            Some((c, _)) => return Err(format!("store belongs to constellation {c}, not {cid}")),
            None if adopt => None,
            None => {
                let chain = registry.chain(cid);
                if !chain.iter().any(|c| c.is_member(&kp.pk)) {
                    return Err(format!("{} is not a member of {}", short(&kp.pk), short(cid)));
                }
                if chain.len() > 1 {
                    return Err(format!(
                        "{} has rotated past version 0: a fresh store joins a later version only by ADOPT (start with --adopt)",
                        short(cid)
                    ));
                }
                setup.push(("member".into(), String::new(), Json::Arr(vec![Json::str(cid), Json::Int(0)])));
                Some((cid.to_string(), 0))
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
            registry: RwLock::new(Arc::new(registry)),
            gossip: Mutex::new(GossipStore::default()),
            state: Mutex::new(State { records, member, frozen: loaded.frozen, frozen_for: loaded.frozen_for }),
            stamps: None,
            redeemed: Mutex::new(loaded.stamps),
            store,
            clock,
            batch_verify: true,
        })
    }

    /// Require a stamp with every SPEND, sold by this key (`witnessd run --stamps`).
    pub fn with_stamps(mut self, key: StampKey) -> Witness {
        self.stamps = Some(key);
        self
    }

    pub fn now(&self) -> i128 {
        (self.clock)()
    }

    pub fn frozen(&self) -> bool {
        self.state.lock().expect("state lock").frozen
    }

    /// The constellation joined or adopted (`None` while awaiting ADOPT).
    pub fn cid(&self) -> Option<String> {
        self.state.lock().expect("state lock").member.as_ref().map(|m| m.0.clone())
    }

    pub fn version(&self) -> Option<i128> {
        self.state.lock().expect("state lock").member.as_ref().map(|m| m.1)
    }

    /// The current charter registry (a snapshot: gossip may replace it later).
    pub fn registry(&self) -> Arc<Registry> {
        self.registry.read().expect("registry lock").clone()
    }

    pub fn stamp_key(&self) -> Option<&StampKey> {
        self.stamps.as_ref()
    }

    fn vote(&self, cid: &str, version: i128, sigil: &str, gen: i128, tid: &str, now: i128) -> Json {
        let mut v = obj([
            ("constellation", Json::str(cid)),
            ("version", Json::Int(version)),
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

    /// `StampMint.redeem` (the caller persists the serial).
    fn redeem(&self, key: &StampKey, stamp: Option<&Json>) -> Option<String> {
        let stamp = stamp.filter(|s| s.as_obj().is_some())?;
        let serial = stamp.get("serial")?.as_str()?;
        if self.redeemed.lock().expect("stamp lock").contains(serial) || !key.verify(stamp) {
            return None;
        }
        // Verified outside the lock: of two concurrent redemptions only one inserts.
        self.redeemed.lock().expect("stamp lock").insert(serial.to_string()).then(|| serial.to_string())
    }

    /// SPEND (SPEC §5.1). `req` carries sigil, header, home, lock, salt, unlock, [stamp].
    pub fn spend(&self, req: &Json) -> Outcome {
        let r = self.spend_inner(req);
        (r, self.store.last_submitted())
    }

    fn spend_inner(&self, req: &Json) -> Result<Json, Error> {
        let Some((cid, version)) = self.state.lock().expect("state lock").active() else {
            return rejected("witness not active");
        };
        if req.as_obj().is_none() {
            return rejected("malformed request");
        }
        if let Some(key) = &self.stamps {
            match self.redeem(key, req.get("stamp")) {
                Some(serial) => {
                    self.store.submit(vec![("stamp".into(), serial, Json::Bool(true))]);
                }
                None => return rejected("missing or spent stamp"),
            }
        }
        let null = Json::Null;
        let sigil_v = req.get("sigil").unwrap_or(&null);
        if req.get("home").and_then(Json::as_str) != Some(cid.as_str()) {
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

        // The vote is fully determined by (membership, sigil, gen, tid, now), so sign it before
        // taking the lock; it is only used (and only ever leaves) if the record logic says so.
        let fresh = self.vote(&cid, version, sigil, gen, &tid, now);

        let mut st = self.state.lock().expect("state lock");
        if st.active().as_ref() != Some(&(cid.clone(), version)) {
            return rejected("witness not active"); // frozen (or re-membered) since we looked
        }
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

    /// RELEASE (SPEC §5.2): abandon the binding if `proof` shows it can never be sealed. A
    /// CONTESTED record drops each candidate that `proof` kills, and is released once none is
    /// left.
    pub fn release(&self, sigil: &Json, proof: &Json) -> Outcome {
        let r = self.release_inner(sigil, proof);
        (r, self.store.last_submitted())
    }

    fn release_inner(&self, sigil: &Json, proof: &Json) -> Result<Json, Error> {
        let snapshot = {
            let st = self.state.lock().expect("state lock");
            if st.active().is_none() {
                return rejected("witness not active");
            }
            if matches!(sigil, Json::Arr(_) | Json::Obj(_)) {
                return Err(Error::BadRequest("unhashable sigil".into()));
            }
            let Some(s) = sigil.as_str() else { return rejected("nothing to release") };
            match st.records.get(s) {
                Some(r) if r.tid.is_some() => r.clone(),
                _ => return rejected("nothing to release"),
            }
        };
        let sigil = sigil.as_str().expect("checked");
        let registry = self.registry();
        // Verify against the snapshot, outside the lock, then re-check the record is unchanged.
        let contested = snapshot.tid.as_deref() == Some(CONTESTED);
        let killed: Vec<Candidate> = if contested {
            snapshot.candidates.iter().filter(|(_, t, h)| proves_dead(h, t, proof, &registry, self.batch_verify)).cloned().collect()
        } else {
            let header = snapshot.header.clone().unwrap_or(Json::Null);
            let tid = snapshot.tid.clone().expect("bound");
            if proves_dead(&header, &tid, proof, &registry, self.batch_verify) {
                vec![(snapshot.gen, tid, header)]
            } else {
                vec![]
            }
        };
        if killed.is_empty() {
            return rejected("invalid death proof");
        }
        let mut st = self.state.lock().expect("state lock");
        if st.active().is_none() {
            return rejected("witness not active");
        }
        let mut rec = match st.records.get(sigil) {
            Some(r) if r.gen == snapshot.gen && r.tid == snapshot.tid && r.candidates == snapshot.candidates => r.clone(),
            _ => return rejected("record changed; retry"),
        };
        if contested {
            for (g, t, h) in &killed {
                rec.log.push(release_entry(*g, t, h.clone(), proof));
            }
            rec.candidates.retain(|c| !killed.contains(c));
            // We never vote while contested, so the generation can rise as each candidate
            // dies; once none is left we sit past all of them, unbound.
            rec.gen = killed.iter().map(|(g, _, _)| g + 1).fold(rec.gen, i128::max);
            if rec.candidates.is_empty() {
                rec.tid = None;
                // A re-used key skips every generation it voted at (abstention).
                if let Some(top) = rec.votes.iter().filter_map(|v| v.get("gen").and_then(Json::as_int)).max() {
                    rec.gen = rec.gen.max(top + 1);
                }
            }
        } else {
            let (g, t, h) = killed.into_iter().next().expect("one");
            rec.log.push(release_entry(g, &t, h, proof));
            rec.gen += 1;
            rec.tid = None;
            rec.header = None;
            rec.vote = None;
            rec.abstain = false;
        }
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

    /// The full record of a sigil, for tests and tools (`None` if the witness has none).
    pub fn record(&self, sigil: &str) -> Option<Record> {
        self.state.lock().expect("state lock").records.get(sigil).cloned()
    }

    /// `sell_stamp`: blind-sign `blinded` (hex), returning the blind signature (hex).
    pub fn sell_stamp(&self, blinded: &Json) -> Outcome {
        let r = match blinded.as_str().and_then(crate::stamps::parse_hex) {
            None => Err(Error::BadRequest("blinded must be a hex string".into())),
            Some(b) => match &self.stamps {
                None => rejected("this witness does not sell stamps"),
                Some(key) => key.sign_blinded(&b).map(|s| Json::str(crate::stamps::to_hex(&s))).map_err(Error::BadRequest),
            },
        };
        (r, 0)
    }

    // ------------------------------------------------------------------ rotation (§5.4)

    /// FREEZE: stop voting forever and hand over evidence for `next_charter`, the body of the
    /// next charter version. Returns `{sig, snapshot}`: our signature on it and our evidence
    /// `{sigil: log ‖ [{kind: "vote", vote} for every vote we cast on sigil]}`. We freeze for
    /// exactly one successor: the same one is signed again, any other is refused.
    pub fn freeze(&self, next_charter: &Json) -> Outcome {
        let r = self.freeze_inner(next_charter);
        (r, self.store.last_submitted())
    }

    fn freeze_inner(&self, next_charter: &Json) -> Result<Json, Error> {
        let mut st = self.state.lock().expect("state lock");
        let Some((cid, version)) = st.member.clone() else { return rejected("witness not active") };
        let Some(prev) = next_charter.as_obj().and_then(|m| m.get("prev")) else {
            return Err(Error::BadRequest("'prev'".into()));
        };
        let registry = self.registry();
        let ours = registry.charter(&cid, version).map(|c| c.body.clone()).unwrap_or(Json::Null);
        if prev.as_str() != Some(charter_hash(&ours).as_str()) {
            return rejected("charter does not extend ours");
        }
        // Signing two successors lets a quorum of honest witnesses certify two conflicting
        // version v+1 charters (a fork).
        let h = charter_hash(next_charter);
        if st.frozen && st.frozen_for.as_deref() != Some(h.as_str()) {
            return rejected("already frozen for a different successor charter");
        }
        if !st.frozen {
            self.store.submit(vec![("frozen".into(), String::new(), Json::str(&h))]);
            st.frozen = true;
            st.frozen_for = Some(h);
        }
        // Our signed votes travel with the evidence, so that a re-used key never votes another
        // transition at a (sigil, generation) where it already voted.
        let snapshot = Json::Obj(
            st.records
                .iter()
                .map(|(s, r)| {
                    let mut log = r.log.clone();
                    log.extend(r.votes.iter().map(|v| obj([("kind", "vote".into()), ("vote", v.clone())])));
                    (s.clone(), Json::Arr(log))
                })
                .collect(),
        );
        drop(st);
        Ok(obj([("sig", Json::str(self.kp.sign("charter", next_charter))), ("snapshot", snapshot)]))
    }

    /// ADOPT: join charter `version` of `cid`, inheriting the predecessors' bindings from
    /// `snapshots` (the FREEZE evidence of the members that signed it), exactly as the
    /// reference's `Witness.adopt`. Only verifiable evidence counts: a binding needs a valid
    /// owner authorisation and a release a valid death proof, so a lying predecessor can omit
    /// evidence (covered by the union) but never invent it. Malformed parts (a snapshot that is
    /// not an object, a log that is not a list, an entry that is not an object) are skipped.
    pub fn adopt(&self, cid: &Json, version: &Json, snapshots: &[Json]) -> Outcome {
        let mut st = self.state.lock().expect("state lock");
        let r = self.adopt_locked(&mut st, cid, version, snapshots);
        drop(st);
        (r, self.store.last_submitted())
    }

    /// `/v0/adopt`: ADOPT once, on a witness that has not joined any charter version. A retry
    /// for the version already adopted answers the same; anything else is refused.
    pub fn adopt_once(&self, cid: &Json, version: &Json, snapshots: &[Json]) -> Outcome {
        let mut st = self.state.lock().expect("state lock");
        let r = match &st.member {
            Some((c, v)) => {
                if cid.as_str() == Some(c.as_str()) && version.as_int() == Some(*v) {
                    Ok(obj([("constellation", Json::str(c)), ("version", Json::Int(*v))]))
                } else {
                    rejected("already a member of a charter version: ADOPT runs once, on a fresh witness")
                }
            }
            None => self.adopt_locked(&mut st, cid, version, snapshots),
        };
        drop(st);
        (r, self.store.last_submitted())
    }

    fn adopt_locked(&self, st: &mut State, cid: &Json, version: &Json, snapshots: &[Json]) -> Result<Json, Error> {
        let registry = self.registry();
        let not_member = || Error::BadRequest("not a member of this charter".into());
        let (Some(cid), Some(version)) = (cid.as_str(), version.as_int()) else { return Err(not_member()) };
        match registry.charter(cid, version) {
            Some(c) if c.is_member(&self.pk) => {}
            _ => return Err(not_member()),
        }
        let batch = self.batch_verify;
        let mut evidence: OrderedMap<String, Vec<Json>> = OrderedMap::new();
        for snap in snapshots {
            let Some(m) = snap.as_obj() else { continue };
            for (sigil, log) in m {
                if let Some(log) = log.as_arr() {
                    evidence
                        .get_mut_or_insert_with(sigil.clone(), Vec::new)
                        .extend(log.iter().filter(|e| e.as_obj().is_some()).cloned());
                }
            }
        }
        let mut records: Vec<(String, Record)> = Vec::with_capacity(evidence.items.len());
        for (sigil, log) in evidence.items {
            let sigil_j = Json::str(&sigil);
            let mut binds: OrderedMap<(i128, String), Json> = OrderedMap::new(); // (gen, tid) -> header
            let mut dead: HashSet<String> = HashSet::new(); // tids proven unsealable
            let mut own: OrderedMap<(i128, String), Json> = OrderedMap::new(); // votes our key cast
            if let Some(prior) = st.records.get(&sigil) {
                for v in &prior.votes {
                    if let Some(k) = vote_key(v) {
                        own.insert(k, v.clone());
                    }
                }
            }
            for e in &log {
                match e.get("kind").and_then(Json::as_str) {
                    Some("vote") => {
                        let Some(v) = e.get("vote") else { continue };
                        let is = |k: &str, want: &str| v.get(k).and_then(Json::as_str) == Some(want);
                        if is("witness", &self.pk) && is("sigil", &sigil) && is("constellation", cid) && verify_vote(v) {
                            if let Some(k) = vote_key(v) {
                                own.insert(k, v.clone());
                            }
                        }
                    }
                    Some("bind") => {
                        let auth = e.get("auth").cloned().unwrap_or(Json::Obj(Default::default()));
                        // A non-object unlock (`Err`) is never bound by an honest witness.
                        if let Ok(Some(b)) = authorises(&sigil_j, &auth, None, batch) {
                            binds.insert(b, auth.get("header").cloned().unwrap_or(Json::Null));
                        }
                    }
                    Some("release") => {
                        let null = Json::Null;
                        let h = e.get("header").unwrap_or(&null);
                        let Some(t) = e.get("tid").and_then(Json::as_str) else { continue };
                        if transition_id(h) == t && proves_dead(h, t, e.get("proof").unwrap_or(&null), &registry, batch) {
                            dead.insert(t.to_string());
                        }
                    }
                    _ => {}
                }
            }
            let floor = binds.items.iter().map(|((g, t), _)| if dead.contains(t) { g + 1 } else { *g }).fold(0, i128::max);
            // A death proof is a timeless fact about a transition, so it retires that binding
            // wherever it was reported.
            let alive: Vec<&((i128, String), Json)> = binds.items.iter().filter(|((_, t), _)| !dead.contains(t)).collect();
            let mut rec = Record { gen: floor, log, votes: own.items.iter().map(|(_, v)| v.clone()).collect(), ..Default::default() };
            // Two tids bound at one generation mean the owner equivocated there, and the log
            // cannot show which one (if either) a quorum sealed. So a lone live binding is
            // inherited only if it had no sibling at its generation, dead or alive.
            let lone = alive.len() == 1 && binds.items.iter().filter(|((g, _), _)| *g == alive[0].0 .0).count() == 1;
            if lone {
                let ((g, t), h) = alive[0];
                rec.gen = *g;
                rec.tid = Some(t.clone());
                rec.header = Some(h.clone());
                // Inheriting a binding never makes our key sign a second tid at g.
                rec.abstain = own.items.iter().any(|((og, ot), _)| og == g && ot != t);
            } else if alive.is_empty() && !own.items.is_empty() {
                let top = own.items.iter().map(|((og, _), _)| *og).max().expect("non-empty");
                rec.gen = floor.max(top + 1); // skipping our own generations is abstention
            } else if !alive.is_empty() {
                // Contested: never vote; released once every candidate is proven dead.
                rec.tid = Some(CONTESTED.to_string());
                let mut c: Vec<Candidate> = alive.iter().map(|((g, t), h)| (*g, t.clone(), h.clone())).collect();
                c.sort_by(|a, b| (a.0, &a.1).cmp(&(b.0, &b.1)));
                rec.candidates = c;
            }
            records.push((sigil, rec));
        }
        // Membership and inherited records land in one atomic batch: a crash must never leave
        // us active but missing a binding.
        let mut batch_entries: Vec<Entry> = Vec::with_capacity(records.len() + 1);
        batch_entries.push(("member".into(), String::new(), Json::Arr(vec![Json::str(cid), Json::Int(version)])));
        batch_entries.extend(records.iter().map(|(s, r)| ("record".to_string(), s.clone(), r.to_json())));
        self.store.submit(batch_entries);
        st.member = Some((cid.to_string(), version));
        for (s, r) in records {
            st.records.insert(s, r);
        }
        Ok(obj([("constellation", Json::str(cid)), ("version", Json::Int(version))]))
    }

    // -------------------------------------------------------------------------- gossip

    /// `/v0/gossip`: admit what verifies; the registry learns new charter versions.
    pub fn gossip(&self, msg: &Json) -> Outcome {
        if let Err(e) = check_message(msg) {
            return (Err(Error::BadRequest(e)), 0);
        }
        let mut g = self.gossip.lock().expect("gossip lock");
        let base = self.registry();
        let mut reg = CowRegistry::new(&base);
        let out = g.merge(&mut reg, msg, self.batch_verify).map_err(Error::BadRequest);
        if let Some(changed) = reg.into_changed() {
            *self.registry.write().expect("registry lock") = Arc::new(changed);
        }
        (out, 0)
    }

    /// `/v0/proofs`: `{proofs, forks}`.
    pub fn proofs(&self) -> Json {
        self.gossip.lock().expect("gossip lock").snapshot_json()
    }

    /// `/v0/info`.
    pub fn info(&self) -> Json {
        let st = self.state.lock().expect("state lock");
        let (cid, version) = match &st.member {
            Some((c, v)) => (Json::str(c), Json::Int(*v)),
            None => (Json::Null, Json::Null),
        };
        obj([
            ("pk", Json::str(&self.pk)),
            ("constellation", cid),
            ("version", version),
            ("frozen", Json::Bool(st.frozen)),
            ("stamps", self.stamps.as_ref().map(StampKey::public_json).unwrap_or(Json::Null)),
        ])
    }

    pub fn record_count(&self) -> usize {
        self.state.lock().expect("state lock").records.len()
    }
}

fn release_entry(gen: i128, tid: &str, header: Json, proof: &Json) -> Json {
    obj([
        ("kind", "release".into()),
        ("gen", Json::Int(gen)),
        ("tid", Json::str(tid)),
        ("header", header),
        ("proof", proof.clone()),
    ])
}

/// `(v["gen"], v["tid"])` of one of our votes.
fn vote_key(v: &Json) -> Option<(i128, String)> {
    Some((v.get("gen")?.as_int()?, v.get("tid")?.as_str()?.to_string()))
}
