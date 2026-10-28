//! A small, fixed world to drive a real `Witness` in: three constellations, a few sigils and a
//! table of transition headers, all with real keys, hashes and signatures.
//!
//! * `C` (index 0): 4 members, quorum 3. Member 0 is the witness under test, `w0`; the
//!   harness holds the keys of members 1..3 and signs whatever it likes with them.
//! * `D` (index 1): 1 member, quorum 1 (a second home, so transitions can span two homes).
//! * `R` (index 2): 1 member, quorum 1, a "rogue" constellation that homes no sigil.
//!
//! Sigils `a`, `b` are homed at C (`w0` serves them), `c` at D (`w0` must refuse it).

use std::collections::{HashMap, HashSet};

use sigil_witness::charter::{constellation_id, quorum};
use sigil_witness::crypto::{digest, KeyPair};
use sigil_witness::json::{obj, Json, Map};
use sigil_witness::model::{sigil_of, transition_id, unlock_message, vote_payload};

pub const NOW: i128 = 1_000;
pub const EXPIRES_OK: i128 = 5_000;
pub const EXPIRES_PAST: i128 = 500;
pub const C: usize = 0;
pub const D: usize = 1;
pub const R: usize = 2;
pub const PHANTOM_TID: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

pub struct Cons {
    pub cid: String,
    pub body: Json,
    pub keys: Vec<KeyPair>,
    pub q: usize,
}

pub struct SigilInfo {
    pub name: &'static str,
    pub home: usize,
    pub lock: Json,
    pub salt: Json,
    pub sigil: String,
}

pub struct HeaderInfo {
    pub inputs: Vec<(usize, i128)>,
    pub header: Json,
    pub tid: String,
}

pub struct World {
    pub cons: Vec<Cons>,
    pub registry: Json,
    pub owner: KeyPair,
    pub intruder: KeyPair,
    pub sigils: Vec<SigilInfo>,
    pub headers: Vec<HeaderInfo>,
}

pub fn seed(tag: u8, i: u8) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[0] = tag;
    s[1] = i;
    s[31] = 0x5a;
    s
}

/// The default header table: the shapes of formal/MC.tla (same-generation conflict,
/// multi-input with a foreign home, release to generation 1, jump to generation 2) plus a few
/// more. Each entry is a list of `(sigil index, generation)`.
pub fn default_headers() -> Vec<Vec<(usize, i128)>> {
    vec![
        vec![(0, 0)],         // t0: a@0
        vec![(0, 0)],         // t1: a@0 (another body): conflicts with t0
        vec![(0, 0), (2, 0)], // t2: a@0 + c@0 (c homed at D)
        vec![(0, 1)],         // t3: a@1
        vec![(0, 2), (1, 0)], // t4: a@2 + b@0 (jump)
        vec![(1, 0)],         // t5: b@0
        vec![(1, 1), (0, 1)], // t6: b@1 + a@1
    ]
}

impl World {
    pub fn new(header_spec: &[Vec<(usize, i128)>]) -> World {
        let mk = |tag: u8, name: &str, n: u8| -> Cons {
            let keys: Vec<KeyPair> = (0..n).map(|i| KeyPair::from_seed(&seed(tag, i))).collect();
            let body = obj([
                ("name", Json::str(name)),
                ("version", Json::Int(0)),
                ("witnesses", Json::Arr(keys.iter().map(|k| Json::str(&k.pk)).collect())),
                ("prev", Json::Null),
            ]);
            Cons { cid: constellation_id(&body), body, q: quorum(keys.len()), keys }
        };
        let cons = vec![mk(1, "C", 4), mk(2, "D", 1), mk(3, "R", 1)];
        let mut reg = Map::new();
        for c in &cons {
            let body = c.body.clone();
            reg.insert(c.cid.clone(), Json::Arr(vec![obj([("body", body), ("sigs", Json::Obj(Map::new()))])]));
        }
        let owner = KeyPair::from_seed(&seed(9, 0));
        let intruder = KeyPair::from_seed(&seed(9, 1));
        let lock = obj([("op", "sig".into()), ("pk", Json::str(&owner.pk))]);
        let mut sigils = Vec::new();
        for (name, home) in [("a", C), ("b", C), ("c", D)] {
            let salt = Json::str(format!("salt-{name}"));
            let home_cid = Json::str(&cons[home].cid);
            let sigil = sigil_of(&home_cid, &lock, &salt);
            sigils.push(SigilInfo { name, home, lock: lock.clone(), salt, sigil });
        }
        let headers = header_spec
            .iter()
            .enumerate()
            .map(|(i, inputs)| {
                let header = obj([
                    (
                        "inputs",
                        Json::Arr(
                            inputs
                                .iter()
                                .map(|(s, g)| Json::Arr(vec![Json::str(&sigils[*s].sigil), Json::Int(*g)]))
                                .collect(),
                        ),
                    ),
                    ("body", Json::str(digest("body", &Json::Int(i as i128)))),
                ]);
                let tid = transition_id(&header);
                HeaderInfo { inputs: inputs.clone(), header, tid }
            })
            .collect();
        World { cons, registry: Json::Obj(reg), owner, intruder, sigils, headers }
    }

    pub fn w0_key(&self) -> KeyPair {
        KeyPair::from_seed(&seed(1, 0))
    }

    pub fn cid(&self, c: usize) -> &str {
        &self.cons[c].cid
    }

    pub fn sigil_index(&self, s: &str) -> Option<usize> {
        self.sigils.iter().position(|x| x.sigil == s)
    }

    pub fn parcel(&self, si: usize) -> Json {
        let s = &self.sigils[si];
        obj([("home", Json::str(&self.cons[s.home].cid)), ("lock", s.lock.clone()), ("salt", s.salt.clone())])
    }

    /// A SPEND request for sigil `si` in header `hi`. `lock_ok = false` signs with a key the
    /// lock does not name; `expired` makes `unlock.expires` lie before [`NOW`].
    pub fn spend_request(&self, si: usize, hi: usize, lock_ok: bool, expired: bool) -> Json {
        let s = &self.sigils[si];
        let h = &self.headers[hi];
        let expires = if expired { EXPIRES_PAST } else { EXPIRES_OK };
        let signer = if lock_ok { &self.owner } else { &self.intruder };
        let sig = signer.sign("unlock", &unlock_message(&s.sigil, &h.tid, Json::Int(expires)));
        let unlock = obj([
            ("sigs", Json::Obj([(self.owner.pk.clone(), Json::Str(sig))].into_iter().collect())),
            ("preimages", Json::Obj(Map::new())),
            ("equivocations", Json::Arr(vec![])),
            ("expires", Json::Int(expires)),
        ]);
        obj([
            ("sigil", Json::str(&s.sigil)),
            ("header", h.header.clone()),
            ("home", Json::str(&self.cons[s.home].cid)),
            ("lock", s.lock.clone()),
            ("salt", s.salt.clone()),
            ("unlock", unlock),
        ])
    }

    /// What the witness's authorisation check should conclude (oracle, from SPEC §5.1 steps
    /// 2-3): the request is for a sigil homed at C, named once in the header, with the owner's
    /// signature.
    pub fn authorised(&self, si: usize, hi: usize, lock_ok: bool) -> bool {
        lock_ok
            && self.sigils[si].home == C
            && self.headers[hi].inputs.iter().filter(|(s, _)| *s == si).count() == 1
    }

    pub fn gen_in(&self, si: usize, hi: usize) -> Option<i128> {
        self.headers[hi].inputs.iter().find(|(s, _)| *s == si).map(|(_, g)| *g)
    }
}

/// A signed vote, as a witness would send it.
pub fn signed_vote(k: &KeyPair, cid: &str, version: i128, sigil: &str, gen: i128, tid: &str, time: i128) -> Json {
    let mut v = obj([
        ("constellation", Json::str(cid)),
        ("version", Json::Int(version)),
        ("witness", Json::str(&k.pk)),
        ("sigil", Json::str(sigil)),
        ("gen", Json::Int(gen)),
        ("tid", Json::str(tid)),
        ("time", Json::Int(time)),
    ]);
    let sig = k.sign("vote", &vote_payload(&v).expect("complete"));
    if let Json::Obj(m) = &mut v {
        m.insert("sig".into(), Json::Str(sig));
    }
    v
}

/// The set of votes that were genuinely signed (by the harness, or by `w0` and observed in its
/// replies). Under the cryptographic assumption (Ed25519 is unforgeable) these are the only
/// votes whose signatures can verify. Keyed by `enc(payload) ‖ sig`.
#[derive(Default, Clone)]
pub struct Genuine {
    set: HashSet<String>,
}

impl Genuine {
    fn key(v: &Json) -> Option<String> {
        let p = vote_payload(v)?;
        let sig = v.get("sig")?.as_str()?;
        Some(format!("{}|{}", p.canonical_string(), sig))
    }
    pub fn add(&mut self, v: &Json) {
        if let Some(k) = Genuine::key(v) {
            self.set.insert(k);
        }
    }
    pub fn contains(&self, v: &Json) -> bool {
        Genuine::key(v).is_some_and(|k| self.set.contains(&k))
    }
}

/// Shape of a death proof the harness builds (the release alphabet).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Src {
    Home,
    Rogue,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UChoice {
    Header(usize),
    Same,
    Phantom,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProofSpec {
    /// Which input of the bound header the proof names (taken modulo its length).
    pub k: usize,
    pub seal: bool,
    pub src: Src,
    pub u: UChoice,
    /// All harness-held members of the source constellation sign; otherwise one fewer.
    pub full: bool,
    /// Also include `w0`'s own votes at the named `(sigil, gen)`.
    pub with_w0: bool,
    pub wrong_parcel: bool,
}

impl World {
    /// Build the death proof described by `spec`, against header `ht` (the bound one). Signs
    /// the votes it needs and records them in `genuine`. `w0_votes` are `w0`'s votes from
    /// STATUS of the named sigil.
    pub fn build_proof(&self, spec: &ProofSpec, ht: usize, w0_votes: &dyn Fn(usize) -> Vec<Json>, genuine: &mut Genuine) -> Json {
        let h = &self.headers[ht];
        let (si, g) = h.inputs[spec.k % h.inputs.len()];
        let s = &self.sigils[si];
        let src = match spec.src {
            Src::Home => s.home,
            Src::Rogue => R,
            Src::Other => {
                if s.home == C {
                    D
                } else {
                    C
                }
            }
        };
        let u_tid = match spec.u {
            UChoice::Header(i) => self.headers[i % self.headers.len()].tid.clone(),
            UChoice::Same => h.tid.clone(),
            UChoice::Phantom => PHANTOM_TID.to_string(),
        };
        let cons = &self.cons[src];
        // Harness-held members: all of D and R; members 1.. of C (member 0 is w0).
        let held: Vec<&KeyPair> = cons.keys.iter().skip(if src == C { 1 } else { 0 }).collect();
        let n = if spec.full { held.len() } else { held.len().saturating_sub(1) };
        let mut votes: Vec<Json> = held[..n]
            .iter()
            .map(|k| {
                let v = signed_vote(k, &cons.cid, 0, &s.sigil, g, &u_tid, NOW);
                genuine.add(&v);
                v
            })
            .collect();
        if spec.with_w0 {
            for v in w0_votes(si) {
                if v.get("gen").and_then(Json::as_int) == Some(g) {
                    votes.push(v);
                }
            }
        }
        let parcel = if spec.wrong_parcel { self.parcel((si + 1) % self.sigils.len()) } else { self.parcel(si) };
        let mut p = Map::new();
        p.insert("kind".into(), Json::str(if spec.seal { "seal" } else { "votes" }));
        p.insert("sigil".into(), Json::str(&s.sigil));
        p.insert("gen".into(), Json::Int(g));
        p.insert("parcel".into(), parcel);
        if spec.seal {
            let entries = votes
                .iter()
                .map(|v| {
                    obj([
                        ("witness", v.get("witness").cloned().unwrap_or(Json::Null)),
                        ("time", v.get("time").cloned().unwrap_or(Json::Null)),
                        ("sig", v.get("sig").cloned().unwrap_or(Json::Null)),
                    ])
                })
                .collect();
            p.insert(
                "seal".into(),
                obj([
                    ("constellation", Json::str(&cons.cid)),
                    ("version", Json::Int(0)),
                    ("sigil", Json::str(&s.sigil)),
                    ("gen", Json::Int(g)),
                    ("tid", Json::str(&u_tid)),
                    ("votes", Json::Arr(entries)),
                ]),
            );
        } else {
            p.insert("votes".into(), Json::Arr(votes));
        }
        Json::Obj(p)
    }

    /// Spec-level oracle for SPEC §3.9 (written from the spec, not from proofs.rs): is `proof`
    /// a valid death proof for transition `tid` with `header`, counting only genuine votes?
    /// Returns `(valid, strict_valid)`: `strict_valid` additionally requires seal entries to be
    /// exactly `{witness, time, sig}` (the Rust witness's deliberate strictness).
    pub fn oracle_dead(&self, header: &Json, tid: &str, proof: &Json, genuine: &Genuine) -> (bool, bool) {
        let r = (|| -> Option<(bool, bool)> {
            let target = proof.get("sigil")?.as_str()?;
            let gen = proof.get("gen")?.as_int()?;
            let named = header.get("inputs")?.as_arr()?.iter().any(|x| {
                x.as_arr().is_some_and(|a| a.len() == 2 && a[0].as_str() == Some(target) && a[1].as_int() == Some(gen))
            });
            if !named {
                return Some((false, false));
            }
            let p = proof.get("parcel")?;
            if sigil_of(p.get("home")?, p.get("lock")?, p.get("salt")?) != target {
                return Some((false, false));
            }
            let home = p.get("home")?.as_str()?;
            let cons = self.cons.iter().find(|c| c.cid == home)?;
            let members: HashSet<&str> = cons.keys.iter().map(|k| k.pk.as_str()).collect();
            let (votes, strict): (Vec<Json>, bool) = match proof.get("kind")?.as_str()? {
                "seal" => {
                    let seal = proof.get("seal")?;
                    let st = seal.get("tid")?.as_str()?;
                    if seal.get("sigil")?.as_str()? != target
                        || seal.get("gen")?.as_int()? != gen
                        || st == tid
                        || seal.get("constellation")?.as_str()? != home
                    {
                        return Some((false, false));
                    }
                    let mut out = Vec::new();
                    let mut strict = true;
                    for e in seal.get("votes")?.as_arr()? {
                        let em = e.as_obj()?;
                        strict &= em.len() == 3;
                        let mut v = Map::new();
                        for k in ["constellation", "version", "sigil", "gen", "tid"] {
                            v.insert(k.into(), seal.get(k)?.clone());
                        }
                        for k in ["witness", "time", "sig"] {
                            v.insert(k.into(), em.get(k)?.clone());
                        }
                        out.push(Json::Obj(v));
                    }
                    (out, strict)
                }
                "votes" => {
                    let vs = proof.get("votes")?.as_arr()?.clone();
                    for v in &vs {
                        if v.get("sigil")?.as_str()? != target
                            || v.get("gen")?.as_int()? != gen
                            || v.get("tid")?.as_str()? == tid
                            || v.get("constellation")?.as_str()? != home
                        {
                            return Some((false, false));
                        }
                    }
                    (vs, true)
                }
                _ => return Some((false, false)),
            };
            if votes.is_empty() || votes.iter().any(|v| v.get("version") != Some(&Json::Int(0))) {
                return Some((false, false));
            }
            let counted: HashSet<String> = votes
                .iter()
                .filter(|v| genuine.contains(v))
                .filter_map(|v| v.get("witness").and_then(Json::as_str).map(str::to_string))
                .filter(|w| members.contains(w.as_str()))
                .collect();
            let ok = counted.len() >= cons.q;
            Some((ok, ok && strict))
        })();
        r.unwrap_or((false, false))
    }

    /// Spec-level oracle for SPEC §3.6: at least q distinct members of the named charter
    /// have genuine votes, each rebuilt from the seal's own fields plus the entry's
    /// `witness, time, sig` (other entry keys are ignored, as the spec says).
    pub fn oracle_seal(&self, seal: &Json, genuine: &Genuine) -> bool {
        (|| -> Option<bool> {
            let cid = seal.get("constellation")?.as_str()?;
            if seal.get("version")? != &Json::Int(0) {
                return Some(false);
            }
            let cons = self.cons.iter().find(|c| c.cid == cid)?;
            let members: HashSet<&str> = cons.keys.iter().map(|k| k.pk.as_str()).collect();
            let mut counted = HashSet::new();
            for e in seal.get("votes")?.as_arr()? {
                let mut v = Map::new();
                for k in ["constellation", "version", "sigil", "gen", "tid"] {
                    v.insert(k.into(), seal.get(k)?.clone());
                }
                for k in ["witness", "time", "sig"] {
                    v.insert(k.into(), e.get(k)?.clone());
                }
                let v = Json::Obj(v);
                let w = v.get("witness")?.as_str()?.to_string();
                if genuine.contains(&v) && members.contains(w.as_str()) {
                    counted.insert(w);
                }
            }
            Some(counted.len() >= cons.q)
        })()
        .unwrap_or(false)
    }

    /// Map a tid string to its abstract id: header index, or a stable id for others.
    pub fn tid_index(&self, t: &str, extra: &mut HashMap<String, u32>) -> u32 {
        if let Some(i) = self.headers.iter().position(|h| h.tid == t) {
            return i as u32;
        }
        if t == sigil_witness::witness::CONTESTED {
            return crate::model_rust::CONTESTED;
        }
        let n = extra.len() as u32;
        *extra.entry(t.to_string()).or_insert(10_000 + n)
    }
}
