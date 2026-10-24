//! Real recursive proofs (proof-carrying data) over a *toy* Sigil transition DAG.
//!
//! One Plonky2 circuit proves one transition and, recursively, its whole
//! ancestry: it verifies up to two child proofs of the *same* circuit
//! (cyclic recursion), so a proof's size and verification time do not depend
//! on how long or how wide the history is. Merges (fan-in 2) are native,
//! which is what Sigil's transition DAG needs.
//!
//! What the toy statement covers (see docs/research/RECURSIVE_PROOFS.md):
//!   * parcel commitments  cm = Poseidon(asset, amount, owner, home, salt);
//!   * a transition id     tid = Poseidon(kind, input cms, output openings, supply, nonce);
//!   * genesis: asset id = tid, outputs sum to the declared supply;
//!   * spend: every input opening matches an output commitment of a valid
//!     child proof, inputs are distinct, amounts are 32-bit, positive and
//!     conserved;
//!   * owner authorisation: knowledge of `secret` with owner = Poseidon(secret)
//!     (a stand-in for the Ed25519 unlock signature);
//!   * the set of homes whose seals the history relies on, as a 32-bit mask
//!     (a stand-in for the charter-set accumulator), so the *verifier*
//!     applies its own trust policy;
//!   * a diagnostic count of transitions in the ancestry tree (a production
//!     statement would not reveal it).
//!
//! What it does NOT cover: witness seals (Ed25519 quorum signatures), the
//! lock language, mint rights, multi-asset transitions, BLAKE2b and the
//! canonical JSON encoding. Those are what make the real statement
//! expensive; research/rv32_cycles measures them.
//!
//! Run:  cargo +nightly run --release            (zero-knowledge proofs)
//!       cargo +nightly run --release -- --no-zk (not hiding; faster)
//!       add --hops N to change the length of the payment chain.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Instant;

use anyhow::{anyhow, ensure, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::constant::ConstantGate;
use plonky2::gates::gate::GateRef;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitTarget};
use plonky2::plonk::config::{GenericConfig, Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;
type Proof = ProofWithPublicInputs<F, C, D>;

const AMOUNT_BITS: usize = 32;
const HOME_BITS: usize = 5; // homes are indices 0..32 in this toy
const N_HOMES: usize = 1 << HOME_BITS;

// Public-input layout (the cyclic verifier data follows).
const PI_ASSET: usize = 0;
const PI_OUT: usize = 4; // two hashes: outputs 0 and 1
const PI_TID: usize = 12;
const PI_MASK: usize = 16;
const PI_COUNT: usize = 17;

// ------------------------------------------------------------- native model

#[derive(Clone, Copy, Debug, PartialEq)]
struct Parcel {
    asset: HashOut<F>,
    amount: u64,
    owner: HashOut<F>,
    home: u64,
    salt: u64,
}

fn h(xs: &[F]) -> HashOut<F> {
    PoseidonHash::hash_no_pad(xs)
}

fn f(x: u64) -> F {
    F::from_canonical_u64(x)
}

fn owner_of(secret: [F; 4]) -> HashOut<F> {
    h(&secret)
}

fn commit(p: &Parcel) -> HashOut<F> {
    let mut v = p.asset.elements.to_vec();
    v.push(f(p.amount));
    v.extend(p.owner.elements);
    v.push(f(p.home));
    v.push(f(p.salt));
    h(&v)
}

#[derive(Clone, Copy)]
struct Output {
    amount: u64,
    owner: HashOut<F>,
    home: u64,
    salt: u64,
}

/// A spendable input: the parcel, the secret that owns it, and the proof of
/// the transition that created it (at output `index`).
#[derive(Clone)]
struct Coin {
    parcel: Parcel,
    secret: [F; 4],
    proof: Proof,
    index: usize,
}

// ------------------------------------------------------------------ circuit

struct InputTargets {
    proof: ProofWithPublicInputsTarget<D>,
    // Verified instead of `proof` when the slot is unused. Nothing from it
    // is ever read, so its circuit is irrelevant to soundness; it only has
    // to share the step circuit's shape (see `filler_circuit`).
    other: ProofWithPublicInputsTarget<D>,
    other_vd: VerifierCircuitTarget,
    sel: BoolTarget, // which child output: false = 0, true = 1
    amount: Target,
    secret: [Target; 4],
    home: Target,
    salt: Target,
}

struct OutputTargets {
    amount: Target,
    owner: HashOutTarget,
    home: Target,
    salt: Target,
}

struct Pcd {
    data: CircuitData<F, C, D>,
    common: CommonCircuitData<F, D>,
    is_spend: BoolTarget,
    has_in1: BoolTarget,
    asset: HashOutTarget,
    supply: Target,
    nonce: Target,
    inputs: [InputTargets; 2],
    outputs: [OutputTargets; 2],
    vd: VerifierCircuitTarget,
    filler: Option<Filler>,
    gates_before_padding: usize,
}

/// Proofs used to fill unused input slots.
struct Filler {
    data: CircuitData<F, C, D>,
    proof: Proof,        // a real proof of the filler circuit (verified when a slot is unused)
    cyclic_pad: Proof,   // the same, with the step circuit's verifier data in its public inputs
}

/// A circuit with exactly the step circuit's `CommonCircuitData` that proves
/// nothing. plonky2's own `dummy_circuit` refuses zero-knowledge configs, so
/// this searches for the padding that reproduces the target shape.
fn filler_circuit(common: &CommonCircuitData<F, D>) -> Result<CircuitData<F, C, D>> {
    let build = |noops: usize, commit: bool| {
        let mut b = CircuitBuilder::<F, D>::new(common.config.clone());
        for _ in 0..noops {
            b.add_gate(NoopGate, vec![]);
        }
        for g in &common.gates {
            b.add_gate_to_gate_set(g.clone());
        }
        for _ in 0..common.num_public_inputs {
            b.add_virtual_public_input();
        }
        b.build_with_options::<C>(commit)
    };
    let target = common.degree_bits();
    let (mut lo, mut hi) = (0usize, 1usize << target);
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if build(mid, false).common.degree_bits() <= target { lo = mid } else { hi = mid }
    }
    let data = build(lo, true);
    ensure!(data.common == *common, "filler circuit does not match the step circuit's shape");
    Ok(data)
}

fn make_filler(pcd: &Pcd) -> Result<Filler> {
    let data = filler_circuit(&pcd.common)?;
    let mut pw = PartialWitness::new();
    for &t in &data.prover_only.public_inputs {
        pw.set_target(t, F::ZERO)?;
    }
    let proof = data.prove(pw)?;
    // Unused slots still have their verifier-data public inputs connected to
    // the step circuit's own (that is how cyclic recursion pins the circuit).
    let mut cyclic_pad = proof.clone();
    let cap = pcd.common.config.fri_config.num_cap_elements();
    let start = pcd.common.num_public_inputs - 4 - 4 * cap;
    let vk = &pcd.data.verifier_only;
    cyclic_pad.public_inputs[start..start + 4].copy_from_slice(&vk.circuit_digest.elements);
    for i in 0..cap {
        let s = start + 4 + 4 * i;
        cyclic_pad.public_inputs[s..s + 4].copy_from_slice(&vk.constants_sigmas_cap.0[i].elements);
    }
    Ok(Filler { data, proof, cyclic_pad })
}

fn select_hash(b: &mut CircuitBuilder<F, D>, c: BoolTarget, x: HashOutTarget, y: HashOutTarget) -> HashOutTarget {
    HashOutTarget { elements: core::array::from_fn(|i| b.select(c, x.elements[i], y.elements[i])) }
}

fn commit_t(b: &mut CircuitBuilder<F, D>, asset: HashOutTarget, amount: Target, owner: HashOutTarget, home: Target, salt: Target) -> HashOutTarget {
    let mut v = asset.elements.to_vec();
    v.push(amount);
    v.extend(owner.elements);
    v.push(home);
    v.push(salt);
    b.hash_n_to_hash_no_pad::<PoseidonHash>(v)
}

/// `CommonCircuitData` of a circuit that verifies `n_verify` proofs, padded
/// to `2^degree_bits` gates: the first guess for the cyclic circuit.
fn seed_common(config: &CircuitConfig, degree_bits: usize, n_verify: usize) -> CommonCircuitData<F, D> {
    let data = CircuitBuilder::<F, D>::new(config.clone()).build::<C>();
    let mut b = CircuitBuilder::<F, D>::new(config.clone());
    let p = b.add_virtual_proof_with_pis(&data.common);
    let vd = b.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    b.verify_proof::<C>(&p, &vd, &data.common);
    let data = b.build::<C>();
    let mut b = CircuitBuilder::<F, D>::new(config.clone());
    for _ in 0..n_verify {
        let p = b.add_virtual_proof_with_pis(&data.common);
        let vd = b.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
        b.verify_proof::<C>(&p, &vd, &data.common);
    }
    while b.num_gates() < 1 << degree_bits {
        b.add_gate(NoopGate, vec![]);
    }
    b.build::<C>().common
}

/// Build the step circuit against a guess of its own common data; the bool
/// says whether the guess was right.
fn build_step(config: &CircuitConfig, goal: &CommonCircuitData<F, D>) -> Result<(Pcd, bool)> {
    let mut b = CircuitBuilder::<F, D>::new(config.clone());
    let zero = b.zero();
    let one = b.one();

    let is_spend = b.add_virtual_bool_target_safe();
    let has_in1_raw = b.add_virtual_bool_target_safe();
    let has_in1 = b.and(is_spend, has_in1_raw);
    let is_genesis = b.not(is_spend);

    // Public inputs first: none may be registered after the verifier data.
    let asset = b.add_virtual_hash();
    b.register_public_inputs(&asset.elements);
    let out_pub: [HashOutTarget; 2] = core::array::from_fn(|_| b.add_virtual_hash());
    for o in &out_pub {
        b.register_public_inputs(&o.elements);
    }
    let tid_pub = b.add_virtual_hash();
    b.register_public_inputs(&tid_pub.elements);
    let mask_pub = b.add_virtual_target();
    b.register_public_input(mask_pub);
    let count_pub = b.add_virtual_target();
    b.register_public_input(count_pub);
    let vd = b.add_verifier_data_public_inputs();
    let mut common = goal.clone();
    common.num_public_inputs = b.num_public_inputs();

    // Outputs: well-formed, committed, summed.
    let outputs: [OutputTargets; 2] = core::array::from_fn(|_| OutputTargets {
        amount: b.add_virtual_target(),
        owner: b.add_virtual_hash(),
        home: b.add_virtual_target(),
        salt: b.add_virtual_target(),
    });
    let mut sum_out = zero;
    for (o, pub_cm) in outputs.iter().zip(out_pub.iter()) {
        b.range_check(o.amount, AMOUNT_BITS);
        b.inverse(o.amount); // amount > 0: zero has no inverse, so no witness exists
        b.range_check(o.home, HOME_BITS);
        let cm = commit_t(&mut b, asset, o.amount, o.owner, o.home, o.salt);
        b.connect_hashes(cm, *pub_cm);
        sum_out = b.add(sum_out, o.amount);
    }

    // Inputs and the child proofs that vouch for them.
    let conds = [is_spend, has_in1];
    let cap_height = common.config.fri_config.cap_height;
    let inputs: [InputTargets; 2] = core::array::from_fn(|_| InputTargets {
        proof: b.add_virtual_proof_with_pis(&common),
        other: b.add_virtual_proof_with_pis(&common),
        other_vd: b.add_virtual_verifier_data(cap_height),
        sel: b.add_virtual_bool_target_safe(),
        amount: b.add_virtual_target(),
        secret: core::array::from_fn(|_| b.add_virtual_target()),
        home: b.add_virtual_target(),
        salt: b.add_virtual_target(),
    });
    let zero_hash = HashOutTarget { elements: [zero; 4] };
    let mut in_cms = [zero_hash; 2];
    let mut sum_in = zero;
    let mut count = one;
    let mut mask_bits: Vec<BoolTarget> = (0..N_HOMES).map(|_| b._false()).collect();
    for (k, inp) in inputs.iter().enumerate() {
        let cond = conds[k];
        b.range_check(inp.amount, AMOUNT_BITS);
        b.range_check(inp.home, HOME_BITS);
        // Owner authorisation (toy): knowing the preimage of the owner hash.
        let owner = b.hash_n_to_hash_no_pad::<PoseidonHash>(inp.secret.to_vec());
        let cm = commit_t(&mut b, asset, inp.amount, owner, inp.home, inp.salt);
        let pis = &inp.proof.public_inputs;
        let child_out0 = HashOutTarget { elements: core::array::from_fn(|i| pis[PI_OUT + i]) };
        let child_out1 = HashOutTarget { elements: core::array::from_fn(|i| pis[PI_OUT + 4 + i]) };
        let expected = select_hash(&mut b, inp.sel, child_out1, child_out0);
        for i in 0..4 {
            // The input exists: it is an output of a valid child transition.
            b.conditional_assert_eq(cond.target, cm.elements[i], expected.elements[i]);
        }
        in_cms[k] = select_hash(&mut b, cond, cm, zero_hash);
        sum_in = b.mul_add(cond.target, inp.amount, sum_in);
        count = b.mul_add(cond.target, pis[PI_COUNT], count);
        // Homes relied on: each child's set, plus each consumed input's home
        // (whose seal a real statement checks).
        let child_mask = b.select(cond, pis[PI_MASK], zero);
        let child_bits = b.split_le(child_mask, N_HOMES);
        for (j, bit) in mask_bits.iter_mut().enumerate() {
            let jc = b.constant(F::from_canonical_usize(j));
            let here = b.is_equal(inp.home, jc);
            let here = b.and(here, cond);
            let t = b.or(*bit, child_bits[j]);
            *bit = b.or(t, here);
        }
    }
    // Distinct inputs (toy: compares one limb of the two commitments).
    let diff = b.sub(in_cms[0].elements[0], in_cms[1].elements[0]);
    let diff_or_one = b.select(has_in1, diff, one);
    b.inverse(diff_or_one);

    // Conservation. Amounts are < 2^32, so the sums cannot wrap the field.
    let supply = b.add_virtual_target();
    b.range_check(supply, AMOUNT_BITS + 1);
    b.conditional_assert_eq(is_spend.target, sum_in, sum_out);
    b.conditional_assert_eq(is_genesis.target, supply, sum_out);

    // Transition id; for a genesis the asset id *is* the transition id.
    let nonce = b.add_virtual_target();
    let mut tid_in = vec![is_spend.target];
    tid_in.extend(in_cms[0].elements);
    tid_in.extend(in_cms[1].elements);
    for o in &outputs {
        tid_in.push(o.amount);
        tid_in.extend(o.owner.elements);
        tid_in.push(o.home);
        tid_in.push(o.salt);
    }
    let supply_or_zero = b.select(is_genesis, supply, zero);
    tid_in.push(supply_or_zero);
    tid_in.push(nonce);
    let tid = b.hash_n_to_hash_no_pad::<PoseidonHash>(tid_in);
    b.connect_hashes(tid, tid_pub);
    for i in 0..4 {
        b.conditional_assert_eq(is_genesis.target, asset.elements[i], tid.elements[i]);
    }
    let mask = b.le_sum(mask_bits.iter());
    b.connect(mask, mask_pub);
    b.connect(count, count_pub);

    // Recursion: verify each active child (a proof of this very circuit),
    // or a filler proof for an unused slot.
    for (k, inp) in inputs.iter().enumerate() {
        b.conditionally_verify_cyclic_proof::<C>(conds[k], &inp.proof, &inp.other, &inp.other_vd, &common)?;
    }
    // The filler circuit always carries a ConstantGate; keep the gate sets equal.
    b.add_gate_to_gate_set(GateRef::new(ConstantGate::new(config.num_constants)));

    let gates_before_padding = b.num_gates();
    let (data, ok) = b.try_build_with_options::<C>(true);
    Ok((
        Pcd {
            data, common, is_spend, has_in1: has_in1_raw, asset, supply, nonce, inputs, outputs, vd,
            filler: None, gates_before_padding,
        },
        ok,
    ))
}

fn build_pcd(zk: bool) -> Result<Pcd> {
    let mut config = CircuitConfig::standard_recursion_config();
    config.zero_knowledge = zk;
    let mut goal = seed_common(&config, 13, 2);
    for attempt in 0..8 {
        // Cyclic recursion needs a fixed point: the circuit's own common
        // data must equal the guess it was built against.
        let (mut pcd, ok) = build_step(&config, &goal)?;
        if ok {
            eprintln!("cyclic circuit: fixed point after {attempt} refinement(s)");
            pcd.filler = Some(make_filler(&pcd)?);
            return Ok(pcd);
        }
        goal = pcd.data.common.clone();
    }
    Err(anyhow!("no fixed point for the cyclic circuit's common data"))
}

// ------------------------------------------------------------------ proving

fn native_tid(is_spend: bool, in_cms: [HashOut<F>; 2], outs: &[Output; 2], supply: u64, nonce: u64) -> HashOut<F> {
    let mut v = vec![f(is_spend as u64)];
    v.extend(in_cms[0].elements);
    v.extend(in_cms[1].elements);
    for o in outs {
        v.push(f(o.amount));
        v.extend(o.owner.elements);
        v.push(f(o.home));
        v.push(f(o.salt));
    }
    v.push(f(if is_spend { 0 } else { supply }));
    v.push(f(nonce));
    h(&v)
}

struct Step {
    proof: Proof,
    parcels: [Parcel; 2],
    prove_s: f64,
}

/// Prove a genesis (no inputs) or a spend of one or two coins.
fn prove(pcd: &Pcd, inputs: &[Coin], outs: [Output; 2], supply: u64, nonce: u64) -> Result<Step> {
    prove_with(pcd, inputs, outs, supply, nonce, None)
}

/// `asset_override` lets the negative tests claim an asset id the honest
/// prover would not use.
fn prove_with(pcd: &Pcd, inputs: &[Coin], outs: [Output; 2], supply: u64, nonce: u64,
              asset_override: Option<HashOut<F>>) -> Result<Step> {
    ensure!(inputs.len() <= 2, "toy circuit has at most two inputs");
    let is_spend = !inputs.is_empty();
    let zero_hash = HashOut { elements: [F::ZERO; 4] };
    let asset = asset_override.unwrap_or_else(|| if is_spend {
        inputs[0].parcel.asset
    } else {
        native_tid(false, [zero_hash; 2], &outs, supply, nonce)
    });
    let mut pw = PartialWitness::new();
    pw.set_bool_target(pcd.is_spend, is_spend)?;
    pw.set_bool_target(pcd.has_in1, inputs.len() == 2)?;
    pw.set_hash_target(pcd.asset, asset)?;
    pw.set_target(pcd.supply, f(if is_spend { 0 } else { supply }))?;
    pw.set_target(pcd.nonce, f(nonce))?;
    pw.set_verifier_data_target(&pcd.vd, &pcd.data.verifier_only)?;
    for (o, t) in outs.iter().zip(pcd.outputs.iter()) {
        pw.set_target(t.amount, f(o.amount))?;
        pw.set_hash_target(t.owner, o.owner)?;
        pw.set_target(t.home, f(o.home))?;
        pw.set_target(t.salt, f(o.salt))?;
    }
    let filler = pcd.filler.as_ref().expect("built");
    for (k, t) in pcd.inputs.iter().enumerate() {
        pw.set_proof_with_pis_target(&t.other, &filler.proof)?;
        pw.set_verifier_data_target(&t.other_vd, &filler.data.verifier_only)?;
        match inputs.get(k) {
            Some(c) => {
                pw.set_proof_with_pis_target(&t.proof, &c.proof)?;
                pw.set_bool_target(t.sel, c.index == 1)?;
                pw.set_target(t.amount, f(c.parcel.amount))?;
                for i in 0..4 {
                    pw.set_target(t.secret[i], c.secret[i])?;
                }
                pw.set_target(t.home, f(c.parcel.home))?;
                pw.set_target(t.salt, f(c.parcel.salt))?;
            }
            None => {
                pw.set_proof_with_pis_target(&t.proof, &filler.cyclic_pad)?;
                pw.set_bool_target(t.sel, false)?;
                pw.set_target(t.amount, F::ZERO)?;
                for i in 0..4 {
                    pw.set_target(t.secret[i], F::ZERO)?;
                }
                pw.set_target(t.home, F::ZERO)?;
                pw.set_target(t.salt, F::ZERO)?;
            }
        }
    }
    let t0 = Instant::now();
    // An unsatisfiable witness makes plonky2's generators fail or panic;
    // either way, no proof exists.
    let proof = match catch_unwind(AssertUnwindSafe(|| pcd.data.prove(pw))) {
        Ok(r) => r?,
        Err(_) => return Err(anyhow!("no valid witness (prover panicked)")),
    };
    let prove_s = t0.elapsed().as_secs_f64();
    let parcels = outs.map(|o| Parcel { asset, amount: o.amount, owner: o.owner, home: o.home, salt: o.salt });
    Ok(Step { proof, parcels, prove_s })
}

// ----------------------------------------------------------------- verifier

/// What a holder checks: the proof (constant size and time), that it is a
/// proof of *this* circuit, that the parcel it was handed is output `index`,
/// and that every home the history relied on is in its own trust policy.
fn holder_accepts(pcd: &Pcd, proof: &Proof, parcel: &Parcel, index: usize, trusted: u64) -> Result<()> {
    check_cyclic_proof_verifier_data(proof, &pcd.data.verifier_only, &pcd.data.common)?;
    pcd.data.verify(proof.clone())?;
    let pis = &proof.public_inputs;
    let cm = commit(parcel);
    ensure!(pis[PI_OUT + 4 * index..PI_OUT + 4 * index + 4] == cm.elements, "parcel is not an output of this transition");
    ensure!(pis[PI_ASSET..PI_ASSET + 4] == parcel.asset.elements, "asset mismatch");
    let mask = pis[PI_MASK].to_canonical_u64();
    ensure!(mask & !trusted == 0, "history relies on untrusted homes {:#x}", mask & !trusted);
    ensure!(trusted >> parcel.home & 1 == 1, "parcel lives in an untrusted home");
    Ok(())
}

// --------------------------------------------------------------------- demo

struct Party {
    secret: [F; 4],
}

impl Party {
    fn new(seed: u64) -> Self {
        Party { secret: [f(seed), f(seed + 1), f(seed + 2), f(seed + 3)] }
    }
    fn owner(&self) -> HashOut<F> {
        owner_of(self.secret)
    }
    fn coin(&self, step: &Step, index: usize) -> Coin {
        Coin { parcel: step.parcels[index], secret: self.secret, proof: step.proof.clone(), index }
    }
}

fn out(to: &Party, amount: u64, home: u64, salt: u64) -> Output {
    Output { amount, owner: to.owner(), home, salt }
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    xs[xs.len() / 2]
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let zk = !args.iter().any(|a| a == "--no-zk");
    let hops: usize = args.iter().position(|a| a == "--hops").map(|i| args[i + 1].parse().unwrap()).unwrap_or(4);

    let t0 = Instant::now();
    let pcd = build_pcd(zk)?;
    let build_s = t0.elapsed().as_secs_f64();
    let degree_bits = pcd.data.common.degree_bits();
    println!("circuit: zk={zk} gates={} (padded 2^{degree_bits}), public inputs={}, build {:.1}s",
             pcd.gates_before_padding, pcd.data.common.num_public_inputs, build_s);

    let (alice, bob, erin, frank, mallory) =
        (Party::new(20), Party::new(30), Party::new(40), Party::new(50), Party::new(60));
    let mut prove_times = vec![];
    let mut nonce = 0u64;
    let mut next = || { nonce += 1; nonce };

    // Genesis: 1000 units, 600 to alice (home 1), 400 to bob (home 2).
    let g = prove(&pcd, &[], [out(&alice, 600, 1, 11), out(&bob, 400, 2, 12)], 1000, next())?;
    println!("genesis proved in {:.2}s", g.prove_s);
    prove_times.push(("genesis", g.prove_s));

    // A chain of `hops` payments: each hop pays 1 unit less on, change to self.
    let mut coin = alice.coin(&g, 0);
    let mut owner = &alice;
    let people: Vec<Party> = (0..hops).map(|i| Party::new(1000 + 10 * i as u64)).collect();
    let mut last = None;
    for (i, p) in people.iter().enumerate() {
        let amt = coin.parcel.amount - 1;
        let s = prove(&pcd, &[coin.clone()], [out(p, amt, 3 + (i as u64 % 5), 100 + i as u64), out(owner, 1, coin.parcel.home, 200 + i as u64)], 0, next())?;
        prove_times.push(("hop", s.prove_s));
        coin = p.coin(&s, 0);
        owner = p;
        last = Some(s);
    }
    let chain = last.expect("hops >= 1");
    println!("{hops} hops proved; last in {:.2}s", chain.prove_s);

    // Erin collects the end of the chain and a payment from bob, then merges (fan-in 2).
    let to_erin = prove(&pcd, &[coin.clone()], [out(&erin, coin.parcel.amount - 5, 4, 300), out(owner, 5, coin.parcel.home, 301)], 0, next())?;
    let from_bob = prove(&pcd, &[bob.coin(&g, 1)], [out(&erin, 300, 5, 302), out(&bob, 100, 2, 303)], 0, next())?;
    let e1 = erin.coin(&to_erin, 0);
    let e2 = erin.coin(&from_bob, 0);
    let total = e1.parcel.amount + e2.parcel.amount;
    let merge = prove(&pcd, &[e1.clone(), e2.clone()], [out(&frank, total - 50, 6, 400), out(&erin, 50, 4, 401)], 0, next())?;
    prove_times.push(("merge", merge.prove_s));
    println!("merge (2 child proofs) proved in {:.2}s", merge.prove_s);

    // Frank, the holder, verifies a constant-size proof of the whole DAG.
    let all_homes: u64 = (1u64 << N_HOMES) - 1;
    let mut verify_times = vec![];
    for _ in 0..10 {
        let t = Instant::now();
        holder_accepts(&pcd, &merge.proof, &merge.parcels[0], 0, all_homes)?;
        verify_times.push(t.elapsed().as_secs_f64());
    }
    let pis = &merge.proof.public_inputs;
    let bytes = merge.proof.to_bytes().len();
    let compressed = merge.proof.clone().compress(&pcd.data.verifier_only.circuit_digest, &pcd.data.common)?.to_bytes().len();
    println!("holder accepts: transitions in ancestry tree = {}, homes mask = {:#b}, tid = {:x}…",
             pis[PI_COUNT].to_canonical_u64(), pis[PI_MASK].to_canonical_u64(), pis[PI_TID].to_canonical_u64());

    // ---- negative cases: each must fail to prove or fail to verify.
    // (An unsatisfiable witness can make plonky2 panic; keep that quiet here.)
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks: Vec<(&str, bool)> = vec![];
    let f1 = frank.coin(&merge, 0);
    // 1. inflation
    checks.push(("inflation is unprovable",
        prove(&pcd, &[f1.clone()], [out(&mallory, f1.parcel.amount, 1, 1), out(&mallory, 1, 1, 2)], 0, next()).is_err()));
    // 2. spending someone else's parcel (wrong secret)
    let stolen = Coin { secret: mallory.secret, ..f1.clone() };
    checks.push(("spend without the owner's key is unprovable",
        prove(&pcd, &[stolen], [out(&mallory, f1.parcel.amount - 1, 1, 3), out(&mallory, 1, 1, 4)], 0, next()).is_err()));
    // 3. the same input twice in one transition
    checks.push(("duplicate input is unprovable",
        prove(&pcd, &[f1.clone(), f1.clone()], [out(&frank, f1.parcel.amount, 1, 5), out(&frank, f1.parcel.amount, 1, 6)], 0, next()).is_err()));
    // 4. a parcel that is not an output of the proven child (forged opening)
    let forged = Coin { parcel: Parcel { amount: f1.parcel.amount + 1000, ..f1.parcel }, ..f1.clone() };
    checks.push(("input not created by the child proof is unprovable",
        prove(&pcd, &[forged], [out(&frank, f1.parcel.amount + 999, 1, 7), out(&frank, 1, 1, 8)], 0, next()).is_err()));
    // 5. a holder handed a parcel that is not in the proof
    let wrong = Parcel { amount: merge.parcels[0].amount + 1, ..merge.parcels[0] };
    checks.push(("holder rejects a parcel not committed by the proof",
        holder_accepts(&pcd, &merge.proof, &wrong, 0, all_homes).is_err()));
    // 6. tampered public inputs (claim a different output commitment)
    let mut tampered = merge.proof.clone();
    tampered.public_inputs[PI_OUT] += F::ONE;
    checks.push(("tampered public inputs fail verification", pcd.data.verify(tampered).is_err()));
    // 7. a holder who does not trust bob's home (2), which sealed part of the history
    let no_home2 = all_homes & !(1 << 2);
    checks.push(("holder policy rejects untrusted homes in the ancestry",
        holder_accepts(&pcd, &merge.proof, &merge.parcels[0], 0, no_home2).is_err()));
    // ...while the chain branch alone never touched home 2.
    checks.push(("same policy accepts a history that avoids that home",
        holder_accepts(&pcd, &to_erin.proof, &to_erin.parcels[0], 0, no_home2).is_ok()));
    // 8. a "genesis" mid-history that mints more of an existing asset
    checks.push(("minting an existing asset via a fake genesis is unprovable",
        prove_with(&pcd, &[], [out(&mallory, 999, 1, 9), out(&mallory, 1, 1, 10)], 1000, next(),
                   Some(g.parcels[0].asset)).is_err()));
    // 9. an input with no valid proof behind it (missing ancestry)
    let orphan = Coin { proof: pcd.filler.as_ref().expect("built").cyclic_pad.clone(), ..f1.clone() };
    checks.push(("input without a valid ancestry proof is unprovable",
        prove(&pcd, &[orphan], [out(&frank, f1.parcel.amount - 1, 1, 11), out(&frank, 1, 1, 12)], 0, next()).is_err()));
    std::panic::set_hook(default_hook);

    let mut all_ok = true;
    for (name, ok) in &checks {
        println!("  [{}] {name}", if *ok { "ok" } else { "FAIL" });
        all_ok &= ok;
    }
    let hop_times: Vec<f64> = prove_times.iter().filter(|(k, _)| *k == "hop").map(|(_, t)| *t).collect();
    println!(
        "RESULT {{\"zk\": {zk}, \"degree_bits\": {degree_bits}, \"gates\": {}, \"build_s\": {:.2}, \"prove_genesis_s\": {:.2}, \
\"prove_hop_median_s\": {:.2}, \"prove_merge_s\": {:.2}, \"proof_bytes\": {bytes}, \"compressed_bytes\": {compressed}, \
\"verify_ms_median\": {:.2}, \"ancestry_transitions\": {}, \"hops\": {hops}, \"negative_checks_passed\": {all_ok}}}",
        pcd.gates_before_padding, build_s, g.prove_s, median(hop_times), merge.prove_s, 1e3 * median(verify_times),
        pis[PI_COUNT].to_canonical_u64()
    );
    ensure!(all_ok, "a negative check failed");
    Ok(())
}
