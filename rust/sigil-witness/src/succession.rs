//! Successor committees (SPEC §3.7, §5.5): standby members who mirror a charter version and
//! succeed it. Mirrors `sigil/succession.py`.
//!
//! A charter may name a successor committee. Its members are *standby members*: while the
//! version lives they store every binding a client asks them to (MIRROR) and answer with a
//! signed *mirror ack*; a witness of the version creates a vote only with acks from a quorum of
//! the committee (SPEC §5.1). When the version is to be replaced (cooperatively, because its
//! members froze and signed the next charter, or after a dead-man period of silence) a standby
//! member signs the next charter and *fences*: it never stores anything for that version again.
//! The new version's members ADOPT from the signing standby members' mirror logs, so they
//! inherit every binding behind every vote the old version ever cast, even if that version was
//! only partitioned and comes back. Safety needs no clock: the dead-man period only decides when
//! an honest standby member is willing to sign without the version's cooperation.
//!
//! Every state change is submitted to the store before the call returns, and the caller waits
//! for it to be durable before it answers (as for the witness). A restart starts a new
//! observation window, so a member never declares a version dead because of heartbeats it
//! missed while down.
//!
//! What one client can make a member store is bounded like a witness's records: MIRROR takes an
//! authorisation of at most [`MAX_AUTH_BYTES`], only below generation [`MAX_GEN`], and at most
//! [`MAX_MIRROR_TIDS`] transitions per sigil and generation; a release entry needs a death proof
//! of at most [`MAX_PROOF_BYTES`] for a binding the member holds. Each refusal only withholds an
//! ack (no ack, no vote), which costs liveness, never safety. The handover of STANDBY, like
//! ADOPT, keeps every entry it is given, each distinct one once.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, RwLock};

use crate::charter::{charter_hash, quorum, short, Registry, Successor, MAX_CHARTER_BYTES, MAX_WITNESSES};
use crate::crypto::{verify, KeyPair};
use crate::gossip::{check_message, CowRegistry, GossipStore};
use crate::json::{obj, Json};
use crate::model::{ack_payload, transition_id};
use crate::proofs::{proves_dead, verify_heartbeat};
use crate::store::{Entry, Loaded, Store};
use crate::witness::{authorises, Clock, Error, Outcome, MAX_AUTH_BYTES, MAX_GEN, MAX_PROOF_BYTES};

/// Distinct transitions a member mirrors per (sigil, generation) (`succession.MAX_MIRROR_TIDS`).
/// Only the owner can authorise its sigil, so the cap only ever limits an owner flooding its own
/// sigil.
pub const MAX_MIRROR_TIDS: usize = 4;

fn rejected<T>(msg: &str) -> Result<T, Error> {
    Err(Error::Rejected(msg.to_string()))
}

fn bad<T>(msg: &str) -> Result<T, Error> {
    Err(Error::BadRequest(msg.to_string()))
}

struct State {
    /// `(cid, version)` stood by for (`None` while awaiting STANDBY).
    member: Option<(String, i128)>,
    /// sigil -> log entries (handover evidence + mirrored).
    mirror: HashMap<String, Vec<Json>>,
    /// `(sigil, gen, tid)` of every verified binding stored.
    mirrored: HashSet<(String, i128, String)>,
    /// `(sigil, gen)` -> how many of them.
    tids: HashMap<(String, i128), usize>,
    /// sigil -> `(gen, tid)` of its mirrored bindings, for STATUS.
    by_sigil: HashMap<String, HashSet<(i128, String)>>,
    /// The hash of the one successor we signed (we fenced for it).
    fenced_for: Option<String>,
    /// member pk -> when it last answered one of our challenges.
    heard: HashMap<String, i128>,
    /// The start of our observation window.
    since: i128,
}

impl State {
    fn set_mirrored(&mut self, binds: HashSet<(String, i128, String)>) {
        self.mirrored.clear();
        self.tids.clear();
        self.by_sigil.clear();
        for (s, g, t) in binds {
            self.add_mirrored(s, g, t);
        }
    }

    fn add_mirrored(&mut self, sigil: String, gen: i128, tid: String) {
        let key = (sigil.clone(), gen);
        if self.mirrored.insert((sigil.clone(), gen, tid.clone())) {
            *self.tids.entry(key).or_insert(0) += 1;
            self.by_sigil.entry(sigil).or_default().insert((gen, tid));
        }
    }
}

/// `_members_snapshot_union`: the union of snapshot logs as ADOPT reads it. Malformed parts (a
/// snapshot that is not an object, a log that is not a list, an entry that is not an object) are
/// skipped, and each distinct entry (by its canonical encoding) is kept once, in the order first
/// seen per sigil.
fn snapshot_union(snapshots: &[Json]) -> HashMap<String, Vec<Json>> {
    let mut out: HashMap<String, (Vec<Json>, HashSet<Vec<u8>>)> = HashMap::new();
    for snap in snapshots {
        let Some(m) = snap.as_obj() else { continue };
        for (sigil, log) in m {
            let Some(log) = log.as_arr() else { continue };
            let (kept, seen) = out.entry(sigil.clone()).or_default();
            for e in log.iter().filter(|e| e.as_obj().is_some()) {
                if seen.insert(e.canonical()) {
                    kept.push(e.clone());
                }
            }
        }
    }
    out.into_iter().map(|(s, (log, _))| (s, log)).collect()
}

/// `_bindings`: the `(sigil, gen, tid)` of every bind entry of a mirror log that verifies.
fn bindings(mirror: &HashMap<String, Vec<Json>>, batch: bool) -> HashSet<(String, i128, String)> {
    let mut out = HashSet::new();
    for (sigil, log) in mirror {
        let sigil_j = Json::str(sigil);
        for e in log {
            if e.get("kind").and_then(Json::as_str) != Some("bind") {
                continue;
            }
            let auth = e.get("auth").cloned().unwrap_or(Json::Obj(Default::default()));
            if let Ok(Some((g, t))) = authorises(&sigil_j, &auth, None, batch) {
                out.insert((sigil.clone(), g, t));
            }
        }
    }
    out
}

/// The reference's `next_charter == charter_body(...)` with string witness keys: exactly the
/// keys `name, version, witnesses, prev` and an optional valid `successor`, and a non-empty list
/// of at most [`MAX_WITNESSES`] distinct string keys.
pub(crate) fn well_formed_body(b: &Json) -> bool {
    let Some(m) = b.as_obj() else { return false };
    const KEYS: [&str; 4] = ["name", "version", "witnesses", "prev"];
    if !KEYS.iter().all(|k| m.contains_key(*k)) {
        return false;
    }
    for (k, v) in m {
        if !KEYS.contains(&k.as_str()) && (k != "successor" || Successor::parse(v).is_err()) {
            return false;
        }
    }
    let Some(ws) = m["witnesses"].as_arr() else { return false };
    let mut keys = Vec::with_capacity(ws.len());
    for w in ws {
        match w.as_str() {
            Some(s) => keys.push(s),
            None => return false,
        }
    }
    let n = keys.len();
    keys.sort_unstable();
    keys.dedup();
    n > 0 && keys.len() == n && n <= MAX_WITNESSES
}

/// One member of a successor committee, standing by for one charter version at a time.
pub struct Standby {
    kp: KeyPair,
    pub pk: String,
    /// The charter registry; gossip replaces it with a longer one (copy on write).
    registry: RwLock<Arc<Registry>>,
    gossip: Mutex<GossipStore>,
    state: Mutex<State>,
    pub store: Arc<Store>,
    clock: Clock,
    /// Use Ed25519 batch verification for death proofs and gossip.
    pub batch_verify: bool,
}

impl Standby {
    /// Restore a standby member from its store, exactly like `sigil.witnessd.build_standby`: a
    /// fresh store stands by for version 0 at once if the key is in version 0's committee and
    /// the constellation has not rotated; otherwise (or with `wait`) it waits for `/v0/standby`
    /// with the handover of a later version.
    pub fn open(kp: KeyPair, registry: Registry, cid: &str, store: Arc<Store>, loaded: Loaded, clock: Clock, wait: bool) -> Result<Standby, String> {
        if !registry.contains(cid) {
            return Err(format!("constellation {cid} is not in the registry"));
        }
        match &loaded.pk {
            None => {
                let seq = store.submit(vec![("pk".into(), String::new(), Json::str(&kp.pk))]);
                store.wait(seq);
            }
            Some(pk) if *pk != kp.pk => return Err("store belongs to a different key".into()),
            _ => {}
        }
        let now = clock();
        let mut st = State {
            member: None,
            mirror: HashMap::new(),
            mirrored: HashSet::new(),
            tids: HashMap::new(),
            by_sigil: HashMap::new(),
            fenced_for: None,
            heard: HashMap::new(),
            since: now,
        };
        if let Some(sb) = &loaded.standby {
            let c = sb.get("constellation").and_then(Json::as_str).ok_or("corrupt standby entry")?;
            let v = sb.get("version").and_then(Json::as_int).ok_or("corrupt standby entry")?;
            let since = sb.get("since").and_then(Json::as_int).ok_or("corrupt standby entry")?;
            if c != cid {
                return Err(format!("store belongs to constellation {c}, not {cid}"));
            }
            // A restart starts a new observation window.
            st.since = since.max(now);
            let prefix = format!("{v}|");
            for (k, log) in &loaded.mirror {
                if let Some(sigil) = k.strip_prefix(&prefix) {
                    st.mirror.insert(sigil.to_string(), log.as_arr().ok_or("corrupt mirror entry")?.clone());
                }
            }
            let binds = bindings(&st.mirror, true);
            st.set_mirrored(binds);
            if let Some(f) = &loaded.fenced {
                if f.get("constellation").and_then(Json::as_str) == Some(c) && f.get("version").and_then(Json::as_int) == Some(v) {
                    st.fenced_for = f.get("charter").and_then(Json::as_str).map(str::to_string);
                }
            }
            st.member = Some((c.to_string(), v));
        }
        let fresh = st.member.is_none();
        let s = Standby {
            pk: kp.pk.clone(),
            kp,
            registry: RwLock::new(Arc::new(registry)),
            gossip: Mutex::new(GossipStore::default()),
            state: Mutex::new(st),
            store,
            clock,
            batch_verify: true,
        };
        if fresh && !wait {
            let reg = s.registry();
            let chain = reg.chain(cid);
            let in_committee = chain.first().and_then(|c| c.successor.as_ref()).is_some_and(|k| k.is_member(&s.pk));
            if !in_committee {
                return Err(format!("{} is not in the successor committee of {} version 0", short(&s.pk), short(cid)));
            }
            if chain.len() > 1 {
                return Err(format!("{} has rotated past version 0: start with --wait for /v0/standby", short(cid)));
            }
            let (r, seq) = s.enter(&Json::str(cid), &Json::Int(0), &[]);
            r.map_err(|e| format!("{e:?}"))?;
            s.store.wait(seq);
        }
        Ok(s)
    }

    pub fn now(&self) -> i128 {
        (self.clock)()
    }

    /// The current charter registry (a snapshot: gossip may replace it later).
    pub fn registry(&self) -> Arc<Registry> {
        self.registry.read().expect("registry lock").clone()
    }

    /// The `(cid, version)` stood by for, if any.
    pub fn member(&self) -> Option<(String, i128)> {
        self.state.lock().expect("state lock").member.clone()
    }

    pub fn fenced(&self) -> bool {
        self.state.lock().expect("state lock").fenced_for.is_some()
    }

    /// STANDBY: stand by for `(cid, version)` with the evidence its members adopt (SPEC §5.5):
    /// the freezing members' and previous committee's snapshots for a rotation, the signing
    /// standby members' for a succession, none for version 0. A member only moves forward, and
    /// acts for one version at a time; a retry for the version it stands by for changes nothing.
    pub fn enter(&self, cid: &Json, version: &Json, snapshots: &[Json]) -> Outcome {
        let r = self.enter_inner(cid, version, snapshots);
        (r, self.store.last_submitted())
    }

    fn enter_inner(&self, cid: &Json, version: &Json, snapshots: &[Json]) -> Result<Json, Error> {
        let Json::Int(version) = *version else { return bad("version must be an integer") };
        let Some(cid) = cid.as_str() else { return bad("not a member of this version's successor committee") };
        let registry = self.registry();
        let in_committee = registry.charter(cid, version).and_then(|c| c.successor.as_ref()).is_some_and(|k| k.is_member(&self.pk));
        if !in_committee {
            return bad("not a member of this version's successor committee");
        }
        let answer = obj([("constellation", Json::str(cid)), ("version", Json::Int(version))]);
        let mut st = self.state.lock().expect("state lock");
        if let Some((c, v)) = &st.member {
            if c == cid && *v == version {
                return Ok(answer); // a retried STANDBY
            }
            if c != cid || version <= *v {
                return rejected("already standing by for another version");
            }
        }
        // Like ADOPT, the handover keeps every entry it is given whatever its size: dropping
        // evidence could lose a sealed binding.
        let mirror = snapshot_union(snapshots);
        let since = self.now();
        let mut entries: Vec<Entry> = Vec::with_capacity(mirror.len() + 1);
        entries.push((
            "standby".into(),
            String::new(),
            obj([("constellation", Json::str(cid)), ("version", Json::Int(version)), ("since", Json::Int(since))]),
        ));
        entries.extend(mirror.iter().map(|(s, log)| ("mirror".to_string(), format!("{version}|{s}"), Json::Arr(log.clone()))));
        self.store.submit(entries);
        let binds = bindings(&mirror, self.batch_verify);
        st.member = Some((cid.to_string(), version));
        st.since = since;
        st.mirror = mirror;
        st.fenced_for = None;
        st.heard.clear();
        st.set_mirrored(binds);
        Ok(answer)
    }

    /// `_active`: standing by, and not fenced.
    fn active(st: &State) -> Result<(String, i128), Error> {
        let Some(m) = st.member.clone() else { return rejected("not standing by") };
        if st.fenced_for.is_some() {
            return rejected("fenced: this member signed a successor of the version");
        }
        Ok(m)
    }

    /// MIRROR: store an owner-authorised binding and answer a signed mirror ack. `req` is a SPEND
    /// request (`sigil, header, home, lock, salt, unlock`) plus the `version` it is for. The ack
    /// attests that the binding is in our mirror log, durably, before it leaves.
    pub fn mirror_bind(&self, req: &Json) -> Outcome {
        let r = self.mirror_inner(req);
        (r, self.store.last_submitted())
    }

    fn mirror_inner(&self, req: &Json) -> Result<Json, Error> {
        let (cid, version) = Self::active(&self.state.lock().expect("state lock"))?;
        if req.as_obj().is_none() {
            return rejected("malformed request");
        }
        if req.get("home").and_then(Json::as_str) != Some(cid.as_str()) || !matches!(req.get("version"), Some(Json::Int(v)) if *v == version) {
            return rejected("not standing by for this constellation version");
        }
        let null = Json::Null;
        let sigil_v = req.get("sigil").unwrap_or(&null);
        let auth = obj(["home", "lock", "salt", "unlock", "header"].map(|k| (k, req.get(k).cloned().unwrap_or(Json::Null))));
        if auth.canonical().len() > MAX_AUTH_BYTES {
            return rejected("authorisation too large");
        }
        // Verified outside the lock (owner signatures).
        let Ok(Some((gen, tid))) = authorises(sigil_v, &auth, None, self.batch_verify) else {
            return rejected("malformed request or lock not satisfied");
        };
        let sigil = sigil_v.as_str().expect("authorised sigil is a string").to_string();
        let mut st = self.state.lock().expect("state lock");
        if Self::active(&st)? != (cid.clone(), version) {
            return rejected("not standing by for this constellation version"); // moved on since we looked
        }
        if !st.mirrored.contains(&(sigil.clone(), gen, tid.clone())) {
            // A binding already stored is acknowledged again whatever these say: it costs nothing.
            if gen >= MAX_GEN {
                return rejected("generation limit reached for this sigil");
            }
            if st.tids.get(&(sigil.clone(), gen)).copied().unwrap_or(0) >= MAX_MIRROR_TIDS {
                return rejected("too many transitions mirrored at this generation");
            }
            let mut log = st.mirror.get(&sigil).cloned().unwrap_or_default();
            log.push(obj([("kind", "bind".into()), ("gen", Json::Int(gen)), ("auth", auth)]));
            // Durable before the ack leaves (the caller waits).
            self.store.submit(vec![("mirror".into(), format!("{version}|{sigil}"), Json::Arr(log.clone()))]);
            st.mirror.insert(sigil.clone(), log);
            st.add_mirrored(sigil.clone(), gen, tid.clone());
        }
        drop(st);
        let mut a = obj([
            ("constellation", Json::str(&cid)),
            ("version", Json::Int(version)),
            ("member", Json::str(&self.pk)),
            ("sigil", Json::str(&sigil)),
            ("gen", Json::Int(gen)),
            ("tid", Json::str(&tid)),
        ]);
        let sig = self.kp.sign("mirror", &ack_payload(&a).expect("complete ack"));
        if let Json::Obj(m) = &mut a {
            m.insert("sig".into(), Json::Str(sig));
        }
        Ok(a)
    }

    /// Store a release entry whose death proof verifies, for a binding we hold. Releases need no
    /// ack (they are not needed for safety); they let a successor see that a binding died
    /// instead of finding the record contested. Answers whether the entry was new.
    pub fn note_release(&self, sigil: &Json, entry: &Json) -> Outcome {
        let r = self.release_inner(sigil, entry);
        (r, self.store.last_submitted())
    }

    fn release_inner(&self, sigil: &Json, entry: &Json) -> Result<Json, Error> {
        let (cid, version) = Self::active(&self.state.lock().expect("state lock"))?;
        let invalid = || rejected("invalid release evidence");
        let (Some(h), Some(t), Some(proof)) = (entry.get("header"), entry.get("tid"), entry.get("proof")) else {
            return invalid();
        };
        let (Some(sigil), Some(Json::Int(gen)), Some(t)) = (sigil.as_str(), entry.get("gen"), t.as_str()) else {
            return invalid();
        };
        let gen = *gen;
        let listed = h
            .get("inputs")
            .and_then(Json::as_arr)
            .is_some_and(|ins| ins.contains(&Json::Arr(vec![Json::str(sigil), Json::Int(gen)])));
        let held = self.state.lock().expect("state lock").mirrored.contains(&(sigil.to_string(), gen, t.to_string()));
        if entry.get("kind").and_then(Json::as_str) != Some("release") || transition_id(h) != t || !listed || !held {
            return invalid();
        }
        if proof.canonical().len() > MAX_PROOF_BYTES {
            return rejected("death proof too large");
        }
        if !proves_dead(h, t, proof, &self.registry(), self.batch_verify) {
            return invalid();
        }
        let mut st = self.state.lock().expect("state lock");
        if Self::active(&st)? != (cid, version) {
            return rejected("not standing by for this constellation version");
        }
        let mut log = st.mirror.get(sigil).cloned().unwrap_or_default();
        if log.iter().any(|e| e.get("kind").and_then(Json::as_str) == Some("release") && e.get("tid").and_then(Json::as_str) == Some(t)) {
            return Ok(Json::Bool(false));
        }
        log.push(obj([
            ("kind", "release".into()),
            ("gen", Json::Int(gen)),
            ("tid", Json::str(t)),
            ("header", h.clone()),
            ("proof", proof.clone()),
        ]));
        self.store.submit(vec![("mirror".into(), format!("{version}|{sigil}"), Json::Arr(log.clone()))]);
        st.mirror.insert(sigil.to_string(), log);
        Ok(Json::Bool(true))
    }

    /// Record a member's answer to our `challenge`; true if it counted.
    pub fn observe(&self, heartbeat: &Json, challenge: &str) -> bool {
        let Some((cid, version)) = self.member() else { return false };
        let registry = self.registry();
        let Some(body) = registry.charter(&cid, version) else { return false };
        let str_is = |k: &str, want: &str| heartbeat.get(k).and_then(Json::as_str) == Some(want);
        let Some(witness) = heartbeat.get("witness").and_then(Json::as_str) else { return false };
        let ok = str_is("constellation", &cid)
            && matches!(heartbeat.get("version"), Some(Json::Int(v)) if *v == version)
            && str_is("challenge", challenge)
            && body.is_member(witness)
            && verify_heartbeat(heartbeat);
        if ok {
            let now = self.now();
            self.state.lock().expect("state lock").heard.insert(witness.to_string(), now);
        }
        ok
    }

    /// The dead-man condition (SPEC §5.5): for the last `dead_man` seconds we have stood by,
    /// fewer than a quorum of the version's members have answered.
    pub fn dead(&self) -> bool {
        let st = self.state.lock().expect("state lock");
        self.dead_locked(&st)
    }

    fn dead_locked(&self, st: &State) -> bool {
        let Some((cid, version)) = &st.member else { return false };
        let registry = self.registry();
        let Some(body) = registry.charter(cid, *version) else { return false };
        let Some(d) = body.successor.as_ref().map(|k| k.dead_man) else { return false };
        let now = self.now();
        let alive = st.heard.values().filter(|t| now - **t <= d).count();
        now - st.since >= d && alive < quorum(body.witnesses.len())
    }

    /// SUCCEED: sign the next charter version and fence; answers `{sig, snapshot}`. Signs only a
    /// well-formed successor of the version we stand by for, at most one, and only cooperatively
    /// (`sigs` holds a quorum of the version's members' signatures on it) or once the dead-man
    /// condition holds. Asked again for the same successor, answers the same.
    pub fn succeed(&self, next: &Json, sigs: Option<&Json>) -> Outcome {
        let r = self.succeed_inner(next, sigs);
        (r, self.store.last_submitted())
    }

    fn succeed_inner(&self, next: &Json, sigs: Option<&Json>) -> Result<Json, Error> {
        let mut st = self.state.lock().expect("state lock");
        let Some((cid, version)) = st.member.clone() else { return rejected("not standing by") };
        let registry = self.registry();
        let cur = registry.charter(&cid, version).ok_or_else(|| Error::Rejected("own charter version unknown".into()))?;
        if !well_formed_body(next) {
            return bad("malformed charter body");
        }
        if obj([("body", next.clone()), ("sigs", Json::Obj(Default::default()))]).canonical().len() > MAX_CHARTER_BYTES {
            // Never valid (SPEC §3.7): fencing for it would leave us unable to sign any successor.
            return rejected("charter too large");
        }
        if next.get("prev").and_then(Json::as_str) != Some(charter_hash(&cur.body).as_str())
            || !matches!(next.get("version"), Some(Json::Int(v)) if *v == version + 1)
        {
            return rejected("charter does not extend the version we stand by for");
        }
        let h = charter_hash(next);
        match &st.fenced_for {
            Some(f) if *f != h => return rejected("already signed a different successor"),
            Some(_) => {}
            None => {
                let signers = sigs
                    .and_then(Json::as_obj)
                    .map(|m| {
                        m.iter()
                            .filter(|(pk, sig)| cur.is_member(pk) && sig.as_str().is_some_and(|s| verify(pk, "charter", next, s)))
                            .count()
                    })
                    .unwrap_or(0);
                let cooperative = signers >= quorum(cur.witnesses.len());
                if !cooperative && !self.dead_locked(&st) {
                    return rejected("the version is alive: no quorum of its members asked, and the dead-man period has not passed");
                }
                self.store.submit(vec![(
                    "fenced".into(),
                    String::new(),
                    obj([("constellation", Json::str(&cid)), ("version", Json::Int(version)), ("charter", Json::str(&h))]),
                )]);
                st.fenced_for = Some(h);
            }
        }
        let snapshot = Self::snapshot_locked(&st);
        drop(st);
        Ok(obj([("sig", Json::str(self.kp.sign("charter", next))), ("snapshot", snapshot)]))
    }

    fn snapshot_locked(st: &State) -> Json {
        Json::Obj(st.mirror.iter().map(|(s, log)| (s.clone(), Json::Arr(log.clone()))).collect())
    }

    /// Our mirror log, in FREEZE snapshot format (SPEC §5.4).
    pub fn snapshot(&self) -> Json {
        Self::snapshot_locked(&self.state.lock().expect("state lock"))
    }

    /// Challenge each member at `urls` for a heartbeat (outside any lock); count valid answers.
    pub fn probe(&self, urls: &[String]) -> usize {
        let mut n = 0;
        for url in urls {
            let challenge = hex::encode(rand::random::<[u8; 16]>());
            let body = obj([("challenge", Json::str(&challenge))]);
            if let Ok(hb) = crate::client::post(url, "heartbeat", &body, std::time::Duration::from_secs(5)) {
                n += self.observe(&hb, &challenge) as usize;
            }
        }
        n
    }

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

    /// STATUS: the `[gen, tid]` of every binding of `sigil` in our mirror log, so a holder can
    /// see a binding a successor would inherit before it concludes an expired pledge bound
    /// nothing (SPEC §4 rule 3).
    pub fn status(&self, sigil: &Json) -> Outcome {
        if matches!(sigil, Json::Arr(_) | Json::Obj(_)) {
            return (Err(Error::BadRequest("unhashable sigil".into())), 0);
        }
        let st = self.state.lock().expect("state lock");
        let mut binds: Vec<(i128, String)> =
            sigil.as_str().and_then(|s| st.by_sigil.get(s)).map(|b| b.iter().cloned().collect()).unwrap_or_default();
        binds.sort();
        let out = obj([(
            "bindings",
            Json::Arr(binds.into_iter().map(|(g, t)| Json::Arr(vec![Json::Int(g), Json::str(&t)])).collect()),
        )]);
        let seq = self.store.last_submitted();
        (Ok(out), seq)
    }

    /// `/v0/info`, as the reference's `StandbyServer.info`.
    pub fn info(&self) -> Json {
        let st = self.state.lock().expect("state lock");
        let (cid, version) = match &st.member {
            Some((c, v)) => (Json::str(c), Json::Int(*v)),
            None => (Json::Null, Json::Null),
        };
        obj([
            ("pk", Json::str(&self.pk)),
            ("role", Json::str("standby")),
            ("constellation", cid),
            ("version", version),
            ("fenced", Json::Bool(st.fenced_for.is_some())),
            ("dead", Json::Bool(self.dead_locked(&st))),
            ("frozen", Json::Bool(false)),
            ("stamps", Json::Null),
        ])
    }
}
