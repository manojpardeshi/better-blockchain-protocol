//! Structured inputs for the fuzz targets (rust/sigil-witness/fuzz), shared with the replay
//! tools that feed fuzz corpora to the Python reference.

use arbitrary::Arbitrary;
use sigil_witness::crypto::{hash_preimage, KeyPair};
use sigil_witness::json::{obj, Json, Map};
use sigil_witness::model::unlock_message;

use crate::world::{seed, signed_vote, World};

// ------------------------------------------------------------------ JSON values and mutations

#[derive(Arbitrary, Debug, Clone)]
pub enum FVal {
    Null,
    Bool(bool),
    Small(i8),
    Big(i128),
    Float(f64),
    Pool(u8),
    Text(String),
    Arr(Vec<FVal>),
    Obj(Vec<(u8, FVal)>),
}

/// Strings worth putting anywhere: protocol words, keys and ids of the world.
pub struct Pool {
    pub strs: Vec<String>,
}

impl Pool {
    pub fn new(world: &World) -> Pool {
        let mut strs: Vec<String> = [
            "", "sig", "multi", "after", "before", "hash", "equivocation", "all", "any", "never", "op", "pk", "k",
            "pks", "t", "h", "of", "witness", "seal", "votes", "kind", "sigil", "gen", "tid", "parcel", "home",
            "lock", "salt", "header", "inputs", "body", "unlock", "sigs", "preimages", "equivocations", "expires",
            "constellation", "version", "time", "a", "b", "!contested", "\u{e9}", "\\u",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        for c in &world.cons {
            strs.push(c.cid.clone());
            strs.extend(c.keys.iter().map(|k| k.pk.clone()));
        }
        strs.extend(world.sigils.iter().map(|s| s.sigil.clone()));
        strs.extend(world.headers.iter().map(|h| h.tid.clone()));
        strs.push(world.owner.pk.clone());
        Pool { strs }
    }

    pub fn s(&self, i: u8) -> String {
        self.strs[i as usize % self.strs.len()].clone()
    }

    pub fn json(&self, v: &FVal, depth: usize) -> Json {
        match v {
            FVal::Null => Json::Null,
            FVal::Bool(b) => Json::Bool(*b),
            FVal::Small(i) => Json::Int(*i as i128),
            FVal::Big(i) => Json::Int(*i),
            FVal::Float(f) if f.is_finite() => Json::Float(*f),
            FVal::Float(_) => Json::Float(0.5),
            FVal::Pool(i) => Json::Str(self.s(*i)),
            FVal::Text(s) => Json::Str(s.clone()),
            FVal::Arr(a) if depth < 4 => Json::Arr(a.iter().take(8).map(|x| self.json(x, depth + 1)).collect()),
            FVal::Obj(m) if depth < 4 => {
                Json::Obj(m.iter().take(8).map(|(k, x)| (self.s(*k), self.json(x, depth + 1))).collect())
            }
            _ => Json::Null,
        }
    }
}

#[derive(Arbitrary, Debug, Clone)]
pub enum Action {
    Replace(FVal),
    Remove,
    Insert(u8, FVal),
    DupElem,
    SwapWithPool(u8),
}

#[derive(Arbitrary, Debug, Clone)]
pub struct Mutation {
    pub path: Vec<u8>,
    pub action: Action,
}

/// Apply `m` at the node `m.path` leads to (each byte picks a child, modulo the arity).
pub fn mutate(v: &mut Json, m: &Mutation, pool: &Pool) {
    fn go(v: &mut Json, path: &[u8], a: &Action, pool: &Pool) {
        if let Some((&b, rest)) = path.split_first() {
            match v {
                Json::Obj(map) if !map.is_empty() => {
                    let key = map.keys().nth(b as usize % map.len()).cloned().expect("non-empty");
                    if rest.is_empty() {
                        match a {
                            Action::Remove => {
                                map.remove(&key);
                                return;
                            }
                            Action::Insert(k, x) => {
                                map.insert(pool.s(*k), pool.json(x, 0));
                                return;
                            }
                            _ => {}
                        }
                    }
                    go(map.get_mut(&key).expect("key"), rest, a, pool);
                    return;
                }
                Json::Arr(arr) if !arr.is_empty() => {
                    let i = b as usize % arr.len();
                    if rest.is_empty() {
                        match a {
                            Action::Remove => {
                                arr.remove(i);
                                return;
                            }
                            Action::DupElem => {
                                let x = arr[i].clone();
                                arr.insert(i, x);
                                return;
                            }
                            Action::Insert(_, x) => {
                                arr.insert(i, pool.json(x, 0));
                                return;
                            }
                            _ => {}
                        }
                    }
                    go(&mut arr[i], rest, a, pool);
                    return;
                }
                _ => {}
            }
        }
        match a {
            Action::Replace(x) => *v = pool.json(x, 0),
            Action::SwapWithPool(i) => *v = Json::Str(pool.s(*i)),
            Action::Insert(k, x) => {
                if let Json::Obj(map) = v {
                    map.insert(pool.s(*k), pool.json(x, 0));
                }
            }
            _ => {}
        }
    }
    go(v, &m.path, &m.action, pool);
}

// --------------------------------------------------------------------------------- locks

pub const LOCK_SIGIL: &str = "5151515151515151515151515151515151515151515151515151515151515151";
pub const LOCK_TID: &str = "7474747474747474747474747474747474747474747474747474747474747474";
pub const PREIMAGES: [&str; 4] = ["", "00", "c0ffee", "0123456789abcdef"];

pub fn lock_keys() -> Vec<KeyPair> {
    (0..6).map(|i| KeyPair::from_seed(&seed(20, i))).collect()
}

#[derive(Arbitrary, Debug, Clone)]
pub enum FLock {
    Sig(u8),
    Multi(u8, Vec<u8>),
    After(i16),
    Before(i16),
    Hash(u8),
    Equiv(u8),
    All(Vec<FLock>),
    Any(Vec<FLock>),
    Never,
    /// Anything at all (usually ill formed).
    Raw(FVal),
    /// A well-shaped node with one extra key (ill formed).
    Extra(Box<FLock>, u8, FVal),
}

#[derive(Arbitrary, Debug, Clone, Copy, PartialEq)]
pub enum SigKind {
    Good,
    WrongTid,
    WrongExpires,
    Garbage,
    NotStr,
}

#[derive(Arbitrary, Debug, Clone, Copy, PartialEq)]
pub enum EqKind {
    Valid,
    SameTid,
    OtherGen,
    BadSig,
    OtherWitnessInA,
}

#[derive(Arbitrary, Debug, Clone)]
pub struct FUnlock {
    pub sigs: Vec<(u8, SigKind)>,
    pub preimages: Vec<(u8, bool)>,
    pub equivs: Vec<(u8, EqKind)>,
    pub expires: i16,
    pub expires_raw: Option<FVal>,
    pub drop_field: Option<u8>,
}

#[derive(Arbitrary, Debug, Clone)]
pub struct LockCase {
    pub lock: FLock,
    pub unlock: FUnlock,
    pub now: Option<i16>,
}

pub struct LockCtx {
    pub keys: Vec<KeyPair>,
    pub pool: Pool,
}

impl LockCtx {
    pub fn new(world: &World) -> LockCtx {
        LockCtx { keys: lock_keys(), pool: Pool::new(world) }
    }

    fn pk(&self, i: u8) -> String {
        self.keys[i as usize % self.keys.len()].pk.clone()
    }

    fn hash_of(i: u8) -> String {
        hash_preimage(PREIMAGES[i as usize % PREIMAGES.len()]).expect("hex")
    }

    pub fn lock_json(&self, l: &FLock, depth: usize) -> Json {
        let node = |op: &str, rest: Vec<(&str, Json)>| {
            let mut m = Map::new();
            m.insert("op".into(), Json::str(op));
            for (k, v) in rest {
                m.insert(k.into(), v);
            }
            Json::Obj(m)
        };
        match l {
            FLock::Sig(k) => node("sig", vec![("pk", Json::str(self.pk(*k)))]),
            FLock::Multi(k, ks) => node(
                "multi",
                vec![("k", Json::Int(*k as i128 % 5)), ("pks", Json::Arr(ks.iter().take(7).map(|i| Json::str(self.pk(*i))).collect()))],
            ),
            FLock::After(t) => node("after", vec![("t", Json::Int(*t as i128))]),
            FLock::Before(t) => node("before", vec![("t", Json::Int(*t as i128))]),
            FLock::Hash(i) => node("hash", vec![("h", Json::str(LockCtx::hash_of(*i)))]),
            FLock::Equiv(k) => node("equivocation", vec![("witness", Json::str(self.pk(*k)))]),
            FLock::All(of) | FLock::Any(of) if depth < 10 => node(
                if matches!(l, FLock::All(_)) { "all" } else { "any" },
                vec![("of", Json::Arr(of.iter().take(70).map(|x| self.lock_json(x, depth + 1)).collect()))],
            ),
            FLock::All(_) | FLock::Any(_) => node("never", vec![]),
            FLock::Never => node("never", vec![]),
            FLock::Raw(v) => self.pool.json(v, 0),
            FLock::Extra(inner, k, v) => {
                let mut j = self.lock_json(inner, depth);
                if let Json::Obj(m) = &mut j {
                    m.insert(self.pool.s(*k), self.pool.json(v, 0));
                }
                j
            }
        }
    }

    fn eq_proof(&self, k: u8, kind: EqKind) -> Json {
        let key = &self.keys[k as usize % self.keys.len()];
        let other = &self.keys[(k as usize + 1) % self.keys.len()];
        let a = signed_vote(key, "C", 0, "q", 0, "t1", 1);
        let b = match kind {
            EqKind::Valid | EqKind::OtherWitnessInA => signed_vote(key, "C", 0, "q", 0, "t2", 1),
            EqKind::SameTid => a.clone(),
            EqKind::OtherGen => signed_vote(key, "C", 0, "q", 1, "t2", 1),
            EqKind::BadSig => {
                let mut b = signed_vote(key, "C", 0, "q", 0, "t2", 1);
                if let (Json::Obj(m), Some(s)) = (&mut b, a.get("sig").cloned()) {
                    m.insert("sig".into(), s);
                }
                b
            }
        };
        let a = if kind == EqKind::OtherWitnessInA { signed_vote(other, "C", 0, "q", 0, "t1", 1) } else { a };
        obj([("a", a), ("b", b)])
    }

    pub fn unlock_json(&self, u: &FUnlock, sigil: &str, tid: &str) -> Json {
        let expires = match &u.expires_raw {
            Some(v) => self.pool.json(v, 0),
            None => Json::Int(u.expires as i128),
        };
        let mut sigs = Map::new();
        for (k, kind) in u.sigs.iter().take(8) {
            let key = &self.keys[*k as usize % self.keys.len()];
            let v = match kind {
                SigKind::Good => Json::Str(key.sign("unlock", &unlock_message(sigil, tid, expires.clone()))),
                SigKind::WrongTid => Json::Str(key.sign("unlock", &unlock_message(sigil, "other", expires.clone()))),
                SigKind::WrongExpires => Json::Str(key.sign("unlock", &unlock_message(sigil, tid, Json::Int(-12345)))),
                SigKind::Garbage => Json::str("00".repeat(64)),
                SigKind::NotStr => Json::Int(7),
            };
            sigs.insert(key.pk.clone(), v);
        }
        let mut pre = Map::new();
        for (i, good) in u.preimages.iter().take(4) {
            let h = LockCtx::hash_of(*i);
            let p = if *good { PREIMAGES[*i as usize % PREIMAGES.len()] } else { "ff" };
            pre.insert(h, Json::str(p));
        }
        let eqs: Vec<Json> = u.equivs.iter().take(4).map(|(k, kind)| self.eq_proof(*k, *kind)).collect();
        let mut m = Map::new();
        m.insert("sigs".into(), Json::Obj(sigs));
        m.insert("preimages".into(), Json::Obj(pre));
        m.insert("equivocations".into(), Json::Arr(eqs));
        m.insert("expires".into(), expires);
        if let Some(d) = u.drop_field {
            let k = ["sigs", "preimages", "equivocations", "expires"][d as usize % 4];
            m.remove(k);
        }
        Json::Obj(m)
    }

    /// Independent oracle: the meaning SPEC §3.5 gives a lock built from `l`: `Some(false)` if
    /// it is not well formed (shape rules, depth 8, 64 nodes), else its value. `None` when the
    /// case contains raw JSON (whose shape the oracle does not model).
    pub fn expected(&self, l: &FLock, u: &FUnlock, now: Option<i128>) -> Option<bool> {
        if u.expires_raw.is_some() || u.drop_field.is_some() {
            return None;
        }
        Some(self.expected_wf(l)? && self.ev(l, u, now))
    }

    pub fn expected_wf(&self, l: &FLock) -> Option<bool> {
        if has_raw(l) {
            return None;
        }
        let mut nodes = 0usize;
        let wf = self.wf(l, 0, &mut nodes);
        Some(wf && nodes <= 64)
    }

    fn wf(&self, l: &FLock, depth: usize, nodes: &mut usize) -> bool {
        *nodes += 1;
        if depth > 8 {
            return false;
        }
        match l {
            FLock::Multi(k, ks) => {
                let ks: Vec<String> = ks.iter().take(7).map(|i| self.pk(*i)).collect();
                let mut d = ks.clone();
                d.sort();
                d.dedup();
                let k = *k as usize % 5;
                k >= 1 && k <= ks.len() && d.len() == ks.len()
            }
            FLock::All(of) | FLock::Any(of) => {
                !of.is_empty() && of.iter().take(70).all(|x| self.wf(x, depth + 1, nodes))
            }
            FLock::Raw(_) | FLock::Extra(..) => false,
            _ => true,
        }
    }

    fn has_sig(&self, u: &FUnlock, pk: &str) -> bool {
        // The last entry for a key wins (it is a JSON object).
        u.sigs.iter().take(8).filter(|(k, _)| self.pk(*k) == pk).last().is_some_and(|(_, kind)| *kind == SigKind::Good)
    }

    fn ev(&self, l: &FLock, u: &FUnlock, now: Option<i128>) -> bool {
        match l {
            FLock::Sig(k) => self.has_sig(u, &self.pk(*k)),
            FLock::Multi(k, ks) => {
                let n = ks.iter().take(7).filter(|i| self.has_sig(u, &self.pk(**i))).count();
                n >= *k as usize % 5
            }
            FLock::After(t) => now.map_or(true, |n| n >= *t as i128),
            FLock::Before(t) => now.map_or(true, |n| n < *t as i128),
            FLock::Hash(i) => {
                let h = LockCtx::hash_of(*i);
                u.preimages
                    .iter()
                    .take(4)
                    .filter(|(j, _)| LockCtx::hash_of(*j) == h)
                    .last()
                    .is_some_and(|(_, good)| *good)
            }
            FLock::Equiv(k) => {
                let pk = self.pk(*k);
                u.equivs.iter().take(4).any(|(j, kind)| *kind == EqKind::Valid && self.pk(*j) == pk)
            }
            FLock::All(of) => of.iter().take(70).all(|x| self.ev(x, u, now)),
            FLock::Any(of) => of.iter().take(70).any(|x| self.ev(x, u, now)),
            _ => false,
        }
    }
}

fn has_raw(l: &FLock) -> bool {
    match l {
        FLock::Raw(_) | FLock::Extra(..) => true,
        FLock::All(of) | FLock::Any(of) => of.iter().take(70).any(has_raw),
        _ => false,
    }
}

/// Inputs that hit the known `json::parse` panic (a `\\u` escape followed by non-ASCII bytes
/// within its four hex digits; see docs/VERIFY_RUST.md, bug 1). Conservative.
pub fn hits_known_parser_panic(data: &[u8]) -> bool {
    data.windows(2).enumerate().any(|(i, w)| w == b"\\u" && data[i + 2..].iter().take(4).any(|b| *b >= 0x80))
}
