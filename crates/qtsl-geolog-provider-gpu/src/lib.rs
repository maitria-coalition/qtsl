//! qtsl-geolog-provider-gpu — the GPU build of the provider's batch
//! verification (the combination families' Phase V), as a thin
//! consumer of the `maitria-kernels` rnsfold + roweq families.
//!
//! ## Shape
//!
//! [`pack`] lowers the provider's [`CsrBatch`] planes into the
//! kernels repository's [`RnsFoldBatch`] descriptor under the L-int
//! scaling (per attempt: a common denominator $D$ over every fold
//! participant; $\hat\lambda = \lambda_{\text{num}} \cdot D/\mathrm{den}$;
//! vehicle multipliers $D/\mathrm{den}$; conclusion multipliers
//! $(D/\mathrm{den}) \cdot D$ — integer equality at scale $D^2$ iff
//! rational equality, for ANY common multiple $D$, so verdicts do not
//! depend on which valid $D$ the packer picks). [`pack_membership`]
//! lowers the same batch's membership problem (every vehicle row
//! equals some candidate row) into the kernels [`RowEqBatch`]
//! descriptor — structural row equality over numerator limb planes
//! plus per-attempt interned denominator ids, which is exactly the
//! provider's own exact-plane membership predicate (canonical
//! rationals compare structurally).
//!
//! Two verification paths ride those descriptors:
//!
//! - the ORIGINAL path ([`verify_batch_rns`] /
//!   [`gpu::GpuBatchVerifier::verify_batch`]): fold on a kernels
//!   lane, every value-independent gate host-side on the exact plane
//!   ([`attempt_gates_exact`]).
//! - the FULL path ([`verify_batch_rns_full`] /
//!   [`gpu::GpuBatchVerifier::verify_batch_full`]): fold AND
//!   membership on kernels lanes; the host's residual per-attempt
//!   work reads only index planes and packed λ signs — no bignum is
//!   touched on the host after packing (malformedness is a packed
//!   boolean; λ-sign is the packed $\hat\lambda$ sign, valid because
//!   the multiplier $D/\mathrm{den}$ is positive).
//!
//! Dispatch guidance (membership-lane receipts, measured 2026-07-21):
//! for host-resident batches the ORIGINAL path with [`pack_par`] is
//! the measured Pareto point — the membership lane's packing tax
//! (BigInt→limb planes for every candidate) exceeds the entire host
//! gate cost at every measured shape, so the FULL path ships
//! conformance-gated but UN-DISPATCHED (the kernels repo's
//! receipts-before-dispatch law). Its regime is feeds whose values
//! arrive as limb planes already (descriptor-emitting columnar feed /
//! device-resident corpora), where the packing tax vanishes by
//! construction.
//!
//! Packing itself parallelizes at attempt grain (`parallel` feature:
//! [`pack`]'s columnar passes past [`PACK_PAR_MIN_NNZ`], plus the
//! splice spellings [`pack_par`], [`pack_membership_par`]) —
//! descriptor output is byte-identical across every spelling
//! (attempt parts are self-contained; splicing is associative offset
//! fixup; the columnar feed writes the same bytes windowed), and the
//! batteries assert those equalities. [`pack`] is the columnar feed:
//! a two-pass counting-sort lowering that emits the
//! descriptor's planes directly — no per-slot limb `Vec`s, no nested
//! column staging, no splice copy (the "skip the nested
//! intermediate" lesson, one level up).
//!
//! ## Verdict discipline (the lane law, inherited)
//!
//! Per attempt: `gates && fold_ok`, exactly the structure of the
//! provider's own exact lanes; per instance: OR over attempts. An
//! attempt the channel plan refuses (prime table exhausted — ~4032
//! bits of bound headroom) is routed whole to the provider's exact
//! path ([`verify_attempt_exact`]), never guessed. The membership
//! lane has no refusal surface (structural equality is always
//! decidable). A lane may change cost, never verdicts; `tests/`
//! gates verdict-identity against the provider's own lowerings on
//! generated corpora and mutants.
//!
//! ## Trust statement
//!
//! Untrusted producer-side tooling, like everything in the provider:
//! a wrong verdict here yields a certificate that fails independent
//! checking, never a false verdict in the trusted path. Do not
//! promote into any trusted computing base.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};
use qtsl_geolog_provider::blcsr::{
    attempt_gates_exact, verify_attempt_exact, BatchOutcome, CsrBatch,
};
use qtsl_geolog_provider::qq::QQ;
use std::collections::HashMap;

pub use maitria_kernels::rnsfold::batch::{RnsFoldBatch, RnsFoldOutcome, ABSENT};
pub use maitria_kernels::roweq::batch::{RowEqBatch, RowEqOutcome};

fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

fn lcm(a: &BigUint, b: &BigUint) -> BigUint {
    if a.is_zero() || b.is_zero() {
        return BigUint::zero();
    }
    (a / gcd(a.clone(), b.clone())) * b
}

fn sign_of(v: &BigInt) -> i8 {
    match v.sign() {
        Sign::NoSign => 0,
        Sign::Plus => 1,
        Sign::Minus => -1,
    }
}

/// Measured end-to-end dispatch floor for the device lane, re-pinned
/// by the lane-B receipts (2026-07-21, RTX 5090 shed box, after the
/// pack/assemble/host-walk levers): route combination attempts at
/// bignum tiers (≥ ~2 limbs) to the device lane from this many fold
/// entries, when a device is bound. The t-sweep at the 600-bit tier
/// measured LintBig ahead at T=4 (447 µs vs ~600–730 µs e2e — the
/// device call's fixed latency, not pack, is now the whole gap) and
/// the device ahead from T=8 (521–538 µs vs 802–810 µs), so the
/// opener's T ≥ 8 floor stands unchanged; what moved is the margin
/// above it (X1-syzygy e2e 5.2× → 22–30×). Fixture-class batches stay
/// on the provider's measured CPU dispatch as before.
pub const DEVICE_MIN_FOLD_ENTRIES: usize = 8;

/// Number of source nnz below which the host walks ([`pack`]'s two
/// passes, and per-attempt adjudication inside assembly) run serially
/// rather than on the rayon pool (`parallel` feature; without it every
/// walk is serial and this constant is inert) (fork-join overhead vs. work; the
/// value is measured, not minted — lane-B receipts: at fixture-class
/// shapes (~1k nnz) the whole serial pack is 3–5 µs and any
/// parallelism is pure overhead; at the T=16 t-sweep row (~16k nnz,
/// right at this floor) serial and parallel are within noise of each
/// other (~70–76 µs/inst), so the exact value is uncritical within
/// ~8k–32k; from T=32 (~32k nnz) the pool wins outright. Thread
/// scaling at the X1-batch shape: 11.3 ms → 0.67–0.76 ms/inst from
/// 1 → 24 threads on a 15.3-core cgroup quota).
pub const PACK_PAR_MIN_NNZ: usize = 16_384;

/// Per-attempt pass-1 plan: extents plus the attempt-local semantic
/// products (distinct denominators, common denominator $D$, cofactor
/// multipliers, scaled $\hat\lambda$s, per-column occupancy) —
/// everything computable with no knowledge of any global offset.
/// Deliberately O(T + dict + m) per attempt, never O(nnz): the
/// nnz-proportional planes are written exactly once, directly into
/// their final home, in pass 2 (the "skip the nested
/// intermediate" lesson, applied one level up).
struct AttemptPlan<'b> {
    /// Dense column extent (0 for malformed attempts — they own no
    /// acols; gates decide them host-side).
    m: usize,
    n_lams: usize,
    n_veh: usize,
    n_concl: usize,
    /// Max limb count over this attempt's slot magnitudes.
    max_limbs: usize,
    /// Distinct denominators, first-occurrence order (deterministic —
    /// mult ids are reproducible run to run).
    dens: Vec<&'b BigUint>,
    /// Overflow index for pathological dictionaries (see
    /// [`DenTable`]); `None` in the certificate-real regime.
    den_map: Option<HashMap<&'b BigUint, u32>>,
    /// Per distinct den: the vehicle cofactor $D/\mathrm{den}$.
    veh_cofs: Vec<BigUint>,
    /// Per distinct den: the conclusion cofactor $(D/\mathrm{den}) \cdot D$.
    concl_cofs: Vec<BigUint>,
    /// $\hat\lambda_e = \lambda_{\text{num}} \cdot D/\lambda_{\text{den}}$, per entry.
    lam_hats: Vec<BigInt>,
    /// Per column: vehicle-nnz count (the counting-sort histogram).
    col_counts: Vec<u32>,
}

/// Distinct-denominator table: linear scan while small (the
/// certificate-real regime — the X3 audit measured 98.2% denominator
/// repeats over tiny dictionaries, where a probe is a couple of
/// limb-compares and beats any hash of the limbs), spilling to a
/// borrowed-key hash map beyond [`DenTable::LINEAR_MAX`] so a
/// pathological pairwise-random draw (the kind the channel plan
/// refuses anyway) stays O(nnz) instead of O(nnz · dict).
struct DenTable<'b> {
    dens: Vec<&'b BigUint>,
    map: Option<HashMap<&'b BigUint, u32>>,
}

impl<'b> DenTable<'b> {
    const LINEAR_MAX: usize = 32;

    fn new() -> Self {
        DenTable {
            dens: Vec::new(),
            map: None,
        }
    }

    fn index_or_insert(&mut self, d: &'b BigUint) -> u32 {
        if let Some(map) = &mut self.map {
            let next = self.dens.len() as u32;
            let idx = *map.entry(d).or_insert(next);
            if idx == next {
                self.dens.push(d);
            }
            return idx;
        }
        if let Some(i) = self.dens.iter().position(|x| *x == d) {
            return i as u32;
        }
        let idx = self.dens.len() as u32;
        self.dens.push(d);
        if self.dens.len() > Self::LINEAR_MAX {
            self.map = Some(
                self.dens
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (*x, i as u32))
                    .collect(),
            );
        }
        idx
    }

    /// Lookup-only (pass 2; every den was inserted in pass 1).
    fn index(dens: &[&'b BigUint], map: &Option<HashMap<&'b BigUint, u32>>, d: &BigUint) -> u32 {
        if let Some(map) = map {
            map[d]
        } else {
            dens.iter().position(|x| **x == *d).expect("pass-1 den") as u32
        }
    }
}

/// Pass 1 for one attempt.
fn plan_attempt<'b>(b: &'b CsrBatch, a: usize) -> AttemptPlan<'b> {
    let empty = |m: usize| AttemptPlan {
        m,
        n_lams: 0,
        n_veh: 0,
        n_concl: 0,
        max_limbs: 0,
        dens: Vec::new(),
        den_map: None,
        veh_cofs: Vec::new(),
        concl_cofs: Vec::new(),
        lam_hats: Vec::new(),
        col_counts: vec![0; m],
    };
    if b.malformed[a] {
        // no acols; gates decide false host-side.
        return empty(0);
    }
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    let n_entries = e1 - e0;
    let m = b.n_monos[a] as usize;
    let veh_rows = b.row_base[a]..b.row_base[a] + n_entries as u32;
    let concl_row = b.row_base[a] + n_entries as u32 + b.cand_count[a];
    let nnz_of = |row: u32| {
        (
            b.row_ptr[row as usize] as usize,
            b.row_ptr[row as usize + 1] as usize,
        )
    };

    // distinct denominators of every fold participant, first-occurrence
    // order (dedupe BEFORE any lcm: the den dictionary is tiny on real
    // certificates, and per-value gcd at large operands is the measured
    // canonicalization tax this lane exists to avoid).
    let mut dt = DenTable::new();
    let mut max_limbs = 0usize;
    let mut n_veh = 0usize;
    let mut col_counts = vec![0u32; m];
    for e in e0..e1 {
        dt.index_or_insert(b.exact[b.lam_slot[e] as usize].den());
    }
    for row in veh_rows.clone() {
        let (n0, n1) = nnz_of(row);
        n_veh += n1 - n0;
        for i in n0..n1 {
            let q = &b.exact[b.nnz_slot[i] as usize];
            dt.index_or_insert(q.den());
            max_limbs = max_limbs.max(q.num().bits().div_ceil(64) as usize);
            col_counts[b.nnz_col[i] as usize] += 1;
        }
    }
    let (c0, c1) = nnz_of(concl_row);
    for i in c0..c1 {
        let q = &b.exact[b.nnz_slot[i] as usize];
        dt.index_or_insert(q.den());
        max_limbs = max_limbs.max(q.num().bits().div_ceil(64) as usize);
    }
    let mut d_big = BigUint::one();
    for den in &dt.dens {
        d_big = lcm(&d_big, den);
    }
    let veh_cofs: Vec<BigUint> = dt.dens.iter().map(|den| &d_big / *den).collect();
    let concl_cofs: Vec<BigUint> = veh_cofs.iter().map(|cof| cof * &d_big).collect();
    // λ̂ = λnum * (D / λden), via the cached cofactor of λ's den.
    let lam_hats: Vec<BigInt> = (e0..e1)
        .map(|e| {
            let q = &b.exact[b.lam_slot[e] as usize];
            let di = DenTable::index(&dt.dens, &dt.map, q.den());
            q.num() * BigInt::from(veh_cofs[di as usize].clone())
        })
        .collect();
    AttemptPlan {
        m,
        n_lams: n_entries,
        n_veh,
        n_concl: c1 - c0,
        max_limbs,
        dens: dt.dens,
        den_map: dt.map,
        veh_cofs,
        concl_cofs,
        lam_hats,
        col_counts,
    }
}

/// One attempt's pass-2 write set: its disjoint slices of every
/// output plane (`mag` as one slice per limb plane), plus the global
/// bases pass 2 needs to mint absolute ids.
struct AttemptTask<'b, 'o> {
    a: usize,
    plan: AttemptPlan<'b>,
    lam_base: u32,
    mult_base: u32,
    slot_base: u32,
    csc_base: u32,
    lams: &'o mut [(i8, Vec<u64>)],
    mults: &'o mut [Vec<u64>],
    sign: &'o mut [i8],
    mult_id: &'o mut [u32],
    mag: Vec<&'o mut [u64]>,
    csc_lam: &'o mut [u32],
    csc_slot: &'o mut [u32],
    /// Entries `acol_base+1 ..= acol_base+m` of the global `csc_ptr`.
    csc_ptr: &'o mut [u32],
    concl_slot: &'o mut [u32],
}

/// Write one value slot: sign, multiplier id, and magnitude limbs
/// straight into the (pre-zeroed) limb planes — no per-slot `Vec`, no
/// transpose copy.
fn write_slot(
    sign: &mut [i8],
    mult_id: &mut [u32],
    mag: &mut [&mut [u64]],
    local: usize,
    q: &QQ,
    mid: u32,
) {
    sign[local] = sign_of(q.num());
    mult_id[local] = mid;
    for (l, limb) in q.num().magnitude().iter_u64_digits().enumerate() {
        mag[l][local] = limb;
    }
}

/// Pass 2 for one attempt: counting-sort placement of the CSC pairs
/// (cursor per column — SAM's co-iteration resolved host-side, as the
/// architecture doc records) and direct limb writes into the shared
/// magnitude planes. No allocation is proportional to nnz.
fn fill_attempt(b: &CsrBatch, t: AttemptTask<'_, '_>) {
    let AttemptTask {
        a,
        plan,
        lam_base,
        mult_base,
        slot_base,
        csc_base,
        lams,
        mults,
        sign,
        mult_id,
        mut mag,
        csc_lam,
        csc_slot,
        csc_ptr,
        concl_slot,
    } = t;
    if b.malformed[a] {
        return; // no acols, no lams, no slots — gates decide false.
    }
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    let n_entries = e1 - e0;
    let veh_rows = b.row_base[a]..b.row_base[a] + n_entries as u32;
    let concl_row = b.row_base[a] + n_entries as u32 + b.cand_count[a];
    let nnz_of = |row: u32| {
        (
            b.row_ptr[row as usize] as usize,
            b.row_ptr[row as usize + 1] as usize,
        )
    };

    // λ̂ and multiplier planes (variable-width; one small Vec each —
    // these are the descriptor's own shapes, O(T + dict) per attempt).
    for (j, lh) in plan.lam_hats.iter().enumerate() {
        lams[j] = (sign_of(lh), lh.magnitude().to_u64_digits());
    }
    for (di, (vc, cc)) in plan.veh_cofs.iter().zip(&plan.concl_cofs).enumerate() {
        mults[2 * di] = vc.to_u64_digits();
        mults[2 * di + 1] = cc.to_u64_digits();
    }

    // csc_ptr for this attempt's acols + per-column write cursors
    // (exclusive prefix of the pass-1 histogram).
    let mut cursor = vec![0u32; plan.m];
    let mut run = 0u32;
    for c in 0..plan.m {
        cursor[c] = run;
        run += plan.col_counts[c];
        csc_ptr[c] = csc_base + run;
    }

    // vehicle slots + counting-sort CSC placement (rows in entry
    // order, so each column's pairs land in ascending λ order — the
    // reference packer's order exactly).
    let mut s_local = 0usize;
    for (kk, row) in veh_rows.enumerate() {
        let (n0, n1) = nnz_of(row);
        for i in n0..n1 {
            let q = &b.exact[b.nnz_slot[i] as usize];
            let di = DenTable::index(&plan.dens, &plan.den_map, q.den());
            write_slot(sign, mult_id, &mut mag, s_local, q, mult_base + 2 * di);
            let c = b.nnz_col[i] as usize;
            let pos = cursor[c] as usize;
            cursor[c] += 1;
            csc_lam[pos] = lam_base + kk as u32;
            csc_slot[pos] = slot_base + s_local as u32;
            s_local += 1;
        }
    }
    // conclusion slots
    let (c0, c1) = nnz_of(concl_row);
    for (cl, i) in (c0..c1).enumerate() {
        let q = &b.exact[b.nnz_slot[i] as usize];
        let di = DenTable::index(&plan.dens, &plan.den_map, q.den());
        let local = plan.n_veh + cl;
        write_slot(sign, mult_id, &mut mag, local, q, mult_base + 2 * di + 1);
        concl_slot[b.nnz_col[i] as usize] = slot_base + local as u32;
    }
}

/// Split `slice` into consecutive parts of the given lengths (the
/// disjoint per-attempt write windows — safe parallelism with no
/// unsafe anywhere, per the crate-level `forbid`).
fn split_by<T>(slice: &mut [T], counts: impl Iterator<Item = usize>) -> Vec<&mut [T]> {
    let mut out = Vec::new();
    let mut rest = slice;
    for c in counts {
        let (h, tail) = rest.split_at_mut(c);
        out.push(h);
        rest = tail;
    }
    out
}

/// Pass-1 driver (the `parallel` feature's only pass-1 seam).
#[cfg(feature = "parallel")]
fn compute_plans(b: &CsrBatch, parallel: bool) -> Vec<AttemptPlan<'_>> {
    if parallel {
        use rayon::prelude::*;
        (0..b.attempts())
            .into_par_iter()
            .map(|a| plan_attempt(b, a))
            .collect()
    } else {
        (0..b.attempts()).map(|a| plan_attempt(b, a)).collect()
    }
}
#[cfg(not(feature = "parallel"))]
fn compute_plans(b: &CsrBatch, _parallel: bool) -> Vec<AttemptPlan<'_>> {
    (0..b.attempts()).map(|a| plan_attempt(b, a)).collect()
}

/// Pass-2 driver (disjoint windows make the parallel arm safe with
/// no unsafe anywhere).
#[cfg(feature = "parallel")]
fn run_fill(b: &CsrBatch, tasks: Vec<AttemptTask<'_, '_>>, parallel: bool) {
    if parallel {
        use rayon::prelude::*;
        tasks.into_par_iter().for_each(|t| fill_attempt(b, t));
    } else {
        for t in tasks {
            fill_attempt(b, t);
        }
    }
}
#[cfg(not(feature = "parallel"))]
fn run_fill(b: &CsrBatch, tasks: Vec<AttemptTask<'_, '_>>, _parallel: bool) {
    for t in tasks {
        fill_attempt(b, t);
    }
}

// ------------------------------------------------------------------
// attempt-grain packing parts (shared by the serial and parallel
// packers; the serial packer is the byte-level spec, the parallel one
// must splice to the identical descriptor)
// ------------------------------------------------------------------

/// One attempt's contribution to the rnsfold descriptor, all ids
/// attempt-local (λ ids from 0, slot ids from 0, mult ids from 0 in
/// denominator first-encounter order — global id = 1 + offset + local,
/// since global mult 0 is the conventional `[1]`).
#[derive(Default)]
struct FoldPart {
    mults: Vec<Vec<u64>>,
    lams: Vec<(i8, Vec<u64>)>,
    slots: Vec<(i8, Vec<u64>, u32)>,
    csc_lam: Vec<u32>,
    csc_slot: Vec<u32>,
    csc_len: Vec<u32>,
    concl_slot: Vec<u32>,
}

fn pack_fold_attempt(b: &CsrBatch, a: usize) -> FoldPart {
    let mut part = FoldPart::default();
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    let n_entries = e1 - e0;
    if b.malformed[a] {
        // no acols; gates decide false host-side.
        return part;
    }
    let veh_rows = b.row_base[a]..b.row_base[a] + n_entries as u32;
    let concl_row = b.row_base[a] + n_entries as u32 + b.cand_count[a];
    let nnz_of = |row: u32| {
        (
            b.row_ptr[row as usize] as usize,
            b.row_ptr[row as usize + 1] as usize,
        )
    };

    // ---- distinct denominators of every fold participant ----
    // (dedupe BEFORE any lcm: the den dictionary is tiny on real
    // certificates, and per-value gcd at large operands is the
    // measured canonicalization tax this lane exists to avoid.
    // First-encounter order — deterministic, so the parallel packer
    // splices to identical bytes and repeated runs agree.)
    let mut den_ix: HashMap<Vec<u64>, u32> = HashMap::new();
    let mut dens: Vec<BigUint> = Vec::new();
    let mut note_den = |d: &BigUint, dens: &mut Vec<BigUint>| {
        den_ix.entry(d.to_u64_digits()).or_insert_with(|| {
            dens.push(d.clone());
            (dens.len() - 1) as u32
        });
    };
    for e in e0..e1 {
        note_den(b.exact[b.lam_slot[e] as usize].den(), &mut dens);
    }
    for row in veh_rows.clone() {
        let (n0, n1) = nnz_of(row);
        for i in n0..n1 {
            note_den(b.exact[b.nnz_slot[i] as usize].den(), &mut dens);
        }
    }
    let (c0, c1) = nnz_of(concl_row);
    for i in c0..c1 {
        note_den(b.exact[b.nnz_slot[i] as usize].den(), &mut dens);
    }
    let mut d_big = BigUint::one();
    for den in &dens {
        d_big = lcm(&d_big, den);
    }

    // per-distinct-den multiplier ids, local, in den first-encounter
    // order: vehicles get D/den (local 2j), conclusions (D/den)*D
    // (local 2j+1).
    for den in &dens {
        let cof = &d_big / den;
        part.mults.push(cof.to_u64_digits());
        part.mults.push((cof * &d_big).to_u64_digits());
    }
    let den_ix = den_ix; // frozen
    let veh_mult = |key: &Vec<u64>| 2 * den_ix[key];
    let concl_mult = |key: &Vec<u64>| 2 * den_ix[key] + 1;

    // ---- λ̂ = λnum * (D / λden) ----
    for e in e0..e1 {
        let q = &b.exact[b.lam_slot[e] as usize];
        let lam_hat = q.num() * BigInt::from(&d_big / q.den());
        part.lams
            .push((sign_of(&lam_hat), lam_hat.magnitude().to_u64_digits()));
    }

    // ---- CSC over the attempt's dense column space ----
    let m = b.n_monos[a] as usize;
    let mut cols: Vec<Vec<(u32, u32)>> = vec![Vec::new(); m];
    for (k, row) in veh_rows.clone().enumerate() {
        let (n0, n1) = nnz_of(row);
        for i in n0..n1 {
            let q = &b.exact[b.nnz_slot[i] as usize];
            let slot = part.slots.len() as u32;
            part.slots.push((
                sign_of(q.num()),
                q.num().magnitude().to_u64_digits(),
                veh_mult(&q.den().to_u64_digits()),
            ));
            cols[b.nnz_col[i] as usize].push((k as u32, slot));
        }
    }
    let mut concl = vec![ABSENT; m];
    for i in c0..c1 {
        let q = &b.exact[b.nnz_slot[i] as usize];
        let slot = part.slots.len() as u32;
        part.slots.push((
            sign_of(q.num()),
            q.num().magnitude().to_u64_digits(),
            concl_mult(&q.den().to_u64_digits()),
        ));
        concl[b.nnz_col[i] as usize] = slot;
    }
    for col in 0..m {
        for &(l, s) in &cols[col] {
            part.csc_lam.push(l);
            part.csc_slot.push(s);
        }
        part.csc_len.push(cols[col].len() as u32);
        part.concl_slot.push(concl[col]);
    }
    part
}

fn splice_fold(parts: Vec<FoldPart>) -> RnsFoldBatch {
    let mut out = RnsFoldBatch {
        mults: vec![vec![1u64]],
        ..Default::default()
    };
    out.acol_ptr.push(0);
    out.csc_ptr.push(0);
    let mut slots: Vec<(i8, Vec<u64>, u32)> = Vec::new();
    for part in parts {
        let lam_base = out.lams.len() as u32;
        let slot_base = slots.len() as u32;
        let mult_base = out.mults.len() as u32;
        out.mults.extend(part.mults);
        out.lams.extend(part.lams);
        slots.extend(
            part.slots
                .into_iter()
                .map(|(s, m, mi)| (s, m, mult_base + mi)),
        );
        let mut nnz = 0usize;
        for (acol, len) in part.csc_len.iter().enumerate() {
            for _ in 0..*len {
                out.csc_lam.push(lam_base + part.csc_lam[nnz]);
                out.csc_slot.push(slot_base + part.csc_slot[nnz]);
                nnz += 1;
            }
            out.csc_ptr.push(out.csc_lam.len() as u32);
            out.concl_slot.push(match part.concl_slot[acol] {
                ABSENT => ABSENT,
                s => slot_base + s,
            });
        }
        out.acol_ptr.push(out.concl_slot.len() as u32);
    }

    // ---- slot planes at uniform k ----
    out.n_slots = slots.len();
    out.k = slots
        .iter()
        .map(|(_, m, _)| m.len())
        .max()
        .unwrap_or(0)
        .max(1);
    out.sign = slots.iter().map(|(s, _, _)| *s).collect();
    out.mult_id = slots.iter().map(|(_, _, m)| *m).collect();
    out.mag = vec![0u64; out.k * out.n_slots];
    for (i, (_, mlimbs, _)) in slots.iter().enumerate() {
        for (l, limb) in mlimbs.iter().enumerate() {
            out.mag[l * out.n_slots + i] = *limb;
        }
    }
    out
}

/// Lower a [`CsrBatch`] into the rnsfold descriptor. Attempt indices
/// align one-to-one with the source batch's attempts; malformed
/// attempts pack with an empty column range (their verdict is decided
/// by the host gates, never by the fold).
///
/// This is the **columnar feed**: a two-pass counting-sort pack that
/// emits the descriptor's planes directly — pass 1
/// computes per-attempt extents and the attempt-local arithmetic
/// (denominator dictionary, cofactors, $\hat\lambda$s, column
/// histograms), a serial prefix-sum turns extents into disjoint plane
/// windows, and pass 2 writes every plane in place: no per-slot limb
/// `Vec`s, no nested column staging, no transpose copy (the same
/// "skip the nested intermediate" lesson, one level up).
/// Both passes run at attempt grain on the rayon pool when the
/// `parallel` feature is on and the batch clears [`PACK_PAR_MIN_NNZ`]. Plane-for-plane equal to
/// [`pack_reference`] — `tests/` pins structural equality, not merely
/// verdict agreement.
pub fn pack(b: &CsrBatch) -> RnsFoldBatch {
    let n = b.attempts();
    let parallel = cfg!(feature = "parallel") && b.nnz_col.len() >= PACK_PAR_MIN_NNZ;

    // ---- pass 1: plans (the per-attempt arithmetic) ----
    let plans: Vec<AttemptPlan> = compute_plans(b, parallel);

    // ---- prefix sums: global bases + plane extents ----
    let mut acol_ptr = Vec::with_capacity(n + 1);
    acol_ptr.push(0u32);
    let (mut lam_base, mut mult_base, mut slot_base, mut csc_base) = (0u32, 1u32, 0u32, 0u32);
    let mut bases = Vec::with_capacity(n);
    let mut k = 1usize;
    for p in &plans {
        bases.push((lam_base, mult_base, slot_base, csc_base));
        lam_base += p.n_lams as u32;
        mult_base += 2 * p.dens.len() as u32;
        slot_base += (p.n_veh + p.n_concl) as u32;
        csc_base += p.n_veh as u32;
        k = k.max(p.max_limbs);
        acol_ptr.push(acol_ptr.last().unwrap() + p.m as u32);
    }
    let (n_lams, n_mults, n_slots, n_csc) = (
        lam_base as usize,
        mult_base as usize,
        slot_base as usize,
        csc_base as usize,
    );
    let n_acols = *acol_ptr.last().unwrap() as usize;

    // ---- allocate final planes ----
    let mut out = RnsFoldBatch {
        k,
        n_slots,
        sign: vec![0i8; n_slots],
        mag: vec![0u64; k * n_slots],
        mult_id: vec![0u32; n_slots],
        mults: {
            let mut m = vec![Vec::new(); n_mults];
            m[0] = vec![1u64];
            m
        },
        lams: vec![(0i8, Vec::new()); n_lams],
        acol_ptr,
        csc_ptr: vec![0u32; n_acols + 1],
        csc_lam: vec![0u32; n_csc],
        csc_slot: vec![0u32; n_csc],
        concl_slot: vec![ABSENT; n_acols],
    };

    // ---- carve disjoint per-attempt windows ----
    let lam_parts = split_by(&mut out.lams, plans.iter().map(|p| p.n_lams));
    let mult_parts = split_by(&mut out.mults[1..], plans.iter().map(|p| 2 * p.dens.len()));
    let sign_parts = split_by(&mut out.sign, plans.iter().map(|p| p.n_veh + p.n_concl));
    let multid_parts = split_by(&mut out.mult_id, plans.iter().map(|p| p.n_veh + p.n_concl));
    let csclam_parts = split_by(&mut out.csc_lam, plans.iter().map(|p| p.n_veh));
    let cscslot_parts = split_by(&mut out.csc_slot, plans.iter().map(|p| p.n_veh));
    let cscptr_parts = split_by(&mut out.csc_ptr[1..], plans.iter().map(|p| p.m));
    let concl_parts = split_by(&mut out.concl_slot, plans.iter().map(|p| p.m));
    let mut mag_parts: Vec<Vec<&mut [u64]>> = (0..n).map(|_| Vec::with_capacity(k)).collect();
    if n_slots > 0 {
        for plane in out.mag.chunks_mut(n_slots) {
            for (a, part) in split_by(plane, plans.iter().map(|p| p.n_veh + p.n_concl))
                .into_iter()
                .enumerate()
            {
                mag_parts[a].push(part);
            }
        }
    }

    let tasks: Vec<AttemptTask> = plans
        .into_iter()
        .zip(bases)
        .zip(
            lam_parts.into_iter().zip(mult_parts).zip(
                sign_parts
                    .into_iter()
                    .zip(multid_parts)
                    .zip(csclam_parts.into_iter().zip(cscslot_parts)),
            ),
        )
        .zip(cscptr_parts.into_iter().zip(concl_parts).zip(mag_parts))
        .enumerate()
        .map(
            |(
                a,
                (
                    ((plan, base), ((lams, mults), ((sign, mult_id), (csc_lam, csc_slot)))),
                    ((csc_ptr, concl_slot), mag),
                ),
            )| {
                AttemptTask {
                    a,
                    plan,
                    lam_base: base.0,
                    mult_base: base.1,
                    slot_base: base.2,
                    csc_base: base.3,
                    lams,
                    mults,
                    sign,
                    mult_id,
                    mag,
                    csc_lam,
                    csc_slot,
                    csc_ptr,
                    concl_slot,
                }
            },
        )
        .collect();

    // ---- pass 2: fill, disjoint windows, no further allocation ----
    run_fill(b, tasks, parallel);
    out
}

/// The reference packer — the serial parts-and-splice spelling
/// (byte-level spec of the descriptor; deterministic: multiplier ids
/// follow denominator first-encounter order per attempt). The
/// battery pins [`pack`] == `pack_reference` == [`pack_par`]
/// plane-for-plane, so the columnar feed, the splice spellings, and
/// the parallel arms all cross-check one another.
pub fn pack_reference(b: &CsrBatch) -> RnsFoldBatch {
    splice_fold((0..b.attempts()).map(|a| pack_fold_attempt(b, a)).collect())
}

/// [`pack`] at attempt-grain parallelism (byte-identical output; the
/// battery asserts it).
#[cfg(feature = "parallel")]
pub fn pack_par(b: &CsrBatch) -> RnsFoldBatch {
    use rayon::prelude::*;
    splice_fold(
        (0..b.attempts())
            .into_par_iter()
            .map(|a| pack_fold_attempt(b, a))
            .collect(),
    )
}

// ------------------------------------------------------------------
// membership packing (the roweq descriptor)
// ------------------------------------------------------------------

/// One attempt's contribution to the roweq descriptor (slot ids
/// attempt-local; den ids attempt-scoped by construction).
#[derive(Default)]
struct MemberPart {
    /// (sign, numerator limbs, den id) per slot.
    slots: Vec<(i8, Vec<u64>, u32)>,
    /// nnz (col, local slot) in row-major order.
    nnz: Vec<(u32, u32)>,
    /// nnz count per row (vehicles then candidates).
    row_len: Vec<u32>,
    /// number of query (vehicle) rows.
    n_queries: u32,
}

fn pack_member_attempt(b: &CsrBatch, a: usize) -> MemberPart {
    let mut part = MemberPart::default();
    if b.malformed[a] {
        // host gates decide false; nothing to compare.
        return part;
    }
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    let n_entries = (e1 - e0) as u32;
    part.n_queries = n_entries;
    let rows = b.row_base[a]..b.row_base[a] + n_entries + b.cand_count[a];
    let mut den_ix: HashMap<Vec<u64>, u32> = HashMap::new();
    for row in rows {
        let (n0, n1) = (
            b.row_ptr[row as usize] as usize,
            b.row_ptr[row as usize + 1] as usize,
        );
        for i in n0..n1 {
            let q = &b.exact[b.nnz_slot[i] as usize];
            let next = den_ix.len() as u32;
            let den = *den_ix.entry(q.den().to_u64_digits()).or_insert(next);
            let slot = part.slots.len() as u32;
            part.slots
                .push((sign_of(q.num()), q.num().magnitude().to_u64_digits(), den));
            part.nnz.push((b.nnz_col[i], slot));
        }
        part.row_len.push((n1 - n0) as u32);
    }
    part
}

fn splice_member(parts: Vec<MemberPart>) -> RowEqBatch {
    let mut out = RowEqBatch::default();
    out.arow_ptr.push(0);
    out.row_ptr.push(0);
    let mut slots: Vec<(i8, Vec<u64>, u32)> = Vec::new();
    for part in parts {
        let slot_base = slots.len() as u32;
        let mut nnz = 0usize;
        for len in &part.row_len {
            for _ in 0..*len {
                let (col, s) = part.nnz[nnz];
                out.nnz_col.push(col);
                out.nnz_slot.push(slot_base + s);
                nnz += 1;
            }
            out.row_ptr.push(out.nnz_col.len() as u32);
        }
        slots.extend(part.slots);
        let arow0 = *out.arow_ptr.last().unwrap();
        out.split.push(arow0 + part.n_queries);
        out.arow_ptr.push(arow0 + part.row_len.len() as u32);
    }
    out.n_slots = slots.len();
    out.k = slots.iter().map(|(_, m, _)| m.len()).max().unwrap_or(0);
    out.sign = slots.iter().map(|(s, _, _)| *s).collect();
    out.den_id = slots.iter().map(|(_, _, d)| *d).collect();
    out.mag = vec![0u64; out.k * out.n_slots];
    for (i, (_, mlimbs, _)) in slots.iter().enumerate() {
        for (l, limb) in mlimbs.iter().enumerate() {
            out.mag[l * out.n_slots + i] = *limb;
        }
    }
    out
}

/// Lower a [`CsrBatch`]'s membership problem into the roweq
/// descriptor: per attempt, query rows = vehicle rows, pool rows =
/// candidate rows, values as (numerator sign + limb planes,
/// attempt-interned denominator id). Structural equality on this
/// descriptor coincides with the provider's exact-plane membership
/// predicate because the provider's values are canonical rationals
/// and den ids are injective per attempt by dictionary construction.
/// Malformed attempts pack empty (their verdict is the host gate's).
pub fn pack_membership(b: &CsrBatch) -> RowEqBatch {
    splice_member(
        (0..b.attempts())
            .map(|a| pack_member_attempt(b, a))
            .collect(),
    )
}

/// [`pack_membership`] at attempt-grain parallelism (byte-identical
/// output; the battery asserts it).
#[cfg(feature = "parallel")]
pub fn pack_membership_par(b: &CsrBatch) -> RowEqBatch {
    use rayon::prelude::*;
    splice_member(
        (0..b.attempts())
            .into_par_iter()
            .map(|a| pack_member_attempt(b, a))
            .collect(),
    )
}

// ------------------------------------------------------------------
// outcome assembly
// ------------------------------------------------------------------

/// Assemble the provider-shaped [`BatchOutcome`] from a fold-lane
/// outcome, with host-side exact gates: per attempt
/// `gates && fold_ok` (refusals routed to the provider's exact path),
/// per instance OR over attempts — the same verdict structure as the
/// provider's own lowerings.
/// [`assemble`], public for phase-level benches (pack / lane /
/// assembly timed separately); the composed paths are
/// [`verify_batch_rns`] and the device verifier.
pub fn assemble_outcome(b: &CsrBatch, lane_out: &RnsFoldOutcome) -> BatchOutcome {
    assemble(b, lane_out)
}

fn assemble(b: &CsrBatch, lane_out: &RnsFoldOutcome) -> BatchOutcome {
    // Per-attempt adjudication first (gates dominate host cost at
    // certificate scale — the lane-B phase receipts measured ~3.5
    // ms/inst of membership checking at the X1 shape, more than pack
    // and the device lane combined — and attempts are independent, so
    // the same attempt-grain parallelism applies above the same
    // measured threshold, under the `parallel` feature). The instance
    // fold below is order-identical to the serial spelling, and the
    // counters are sums of the same flags — bit-identical outcomes.
    let adjudicate = |a: usize| -> (bool, bool) {
        if lane_out.refused[a] {
            (verify_attempt_exact(b, a), true)
        } else {
            (attempt_gates_exact(b, a) && lane_out.fold_ok[a], false)
        }
    };
    #[cfg(feature = "parallel")]
    let atts: Vec<(bool, bool)> = if b.nnz_col.len() >= PACK_PAR_MIN_NNZ {
        use rayon::prelude::*;
        (0..b.attempts()).into_par_iter().map(adjudicate).collect()
    } else {
        (0..b.attempts()).map(adjudicate).collect()
    };
    #[cfg(not(feature = "parallel"))]
    let atts: Vec<(bool, bool)> = (0..b.attempts()).map(adjudicate).collect();
    let mut out = BatchOutcome::default();
    for inst in 0..b.instances() {
        let (a0, a1) = (b.inst_ptr[inst] as usize, b.inst_ptr[inst + 1] as usize);
        let mut verdict = false;
        for &(att, deferred) in &atts[a0..a1] {
            if deferred {
                out.attempts_deferred += 1;
            } else {
                out.attempts_fast += 1;
            }
            verdict |= att;
        }
        out.verdicts.push(verdict);
    }
    out
}

/// Assemble from BOTH lane outcomes (fold + membership): the host's
/// per-attempt residual reads only the malformed plane, the packed
/// λ̂ signs (sign(λ̂) = sign(λ): the multiplier is positive), and the
/// two lane verdicts — no exact-plane value is touched except for
/// attempts the fold plan refused, which route whole to the
/// provider's exact path.
fn assemble_full(
    b: &CsrBatch,
    rns: &RnsFoldBatch,
    fold_out: &RnsFoldOutcome,
    memb_out: &RowEqOutcome,
) -> BatchOutcome {
    let mut out = BatchOutcome::default();
    // per-attempt λ ranges: the packer pushes entry-count λs for every
    // non-malformed attempt, in attempt order.
    let mut lam_pos = 0usize;
    for inst in 0..b.instances() {
        let (a0, a1) = (b.inst_ptr[inst] as usize, b.inst_ptr[inst + 1] as usize);
        let mut verdict = false;
        for a in a0..a1 {
            let att = if b.malformed[a] {
                out.attempts_fast += 1;
                false
            } else {
                let n_entries = (b.entry_ptr[a + 1] - b.entry_ptr[a]) as usize;
                let lams = &rns.lams[lam_pos..lam_pos + n_entries];
                lam_pos += n_entries;
                if fold_out.refused[a] {
                    out.attempts_deferred += 1;
                    verify_attempt_exact(b, a)
                } else {
                    out.attempts_fast += 1;
                    lams.iter().all(|(s, _)| *s >= 0)
                        && memb_out.member_ok[a]
                        && fold_out.fold_ok[a]
                }
            };
            verdict |= att;
        }
        out.verdicts.push(verdict);
    }
    out
}

// ------------------------------------------------------------------
// CPU-lane entry points (the always-available lowerings, and the
// conformance anchors for the device lanes)
// ------------------------------------------------------------------

/// Verify a batch on the kernels **reference** fold lane (CPU residue
/// channels), gates host-side on the exact plane — the original
/// lowering this crate adds, and the conformance anchor for the
/// device fold lane.
pub fn verify_batch_rns(b: &CsrBatch) -> BatchOutcome {
    let rns = pack(b);
    let lane_out = maitria_kernels::rnsfold::reference::verify(&rns)
        .expect("packer emitted an invalid descriptor — a bug in this crate, never in the data");
    assemble(b, &lane_out)
}

/// Verify a batch on the kernels **reference** lanes for BOTH the
/// fold and the membership gate — the full path's CPU twin, and the
/// conformance anchor for [`gpu::GpuBatchVerifier::verify_batch_full`].
pub fn verify_batch_rns_full(b: &CsrBatch) -> BatchOutcome {
    let rns = pack(b);
    let req = pack_membership(b);
    let fold_out = maitria_kernels::rnsfold::reference::verify(&rns)
        .expect("packer emitted an invalid descriptor — a bug in this crate, never in the data");
    let memb_out = maitria_kernels::roweq::reference::verify(&req)
        .expect("packer emitted an invalid descriptor — a bug in this crate, never in the data");
    assemble_full(b, &rns, &fold_out, &memb_out)
}

/// The CUDA build: a reusable device verifier.
#[cfg(feature = "cuda")]
pub mod gpu {
    use super::*;
    pub use maitria_kernels_cuda::{GpuError, RnsFoldGpu, RowEqGpu};

    /// Device-lane batch verifier (context + compiled kernels held
    /// across calls).
    pub struct GpuBatchVerifier {
        lane: RnsFoldGpu,
        member: RowEqGpu,
    }

    impl GpuBatchVerifier {
        /// Bind device 0 and compile the fold + membership kernels.
        pub fn new() -> Result<Self, GpuError> {
            Ok(Self {
                lane: RnsFoldGpu::new()?,
                member: RowEqGpu::new()?,
            })
        }

        /// One line of device identification for receipts.
        pub fn device_summary(&self) -> Result<String, GpuError> {
            self.lane.device_summary()
        }

        /// Verify a batch with the fold on device and the gates
        /// host-side on the exact plane. Verdict-identical to the
        /// provider's own lowerings and to [`verify_batch_rns`].
        pub fn verify_batch(&self, b: &CsrBatch) -> Result<BatchOutcome, GpuError> {
            let rns = pack(b);
            let lane_out = self.lane.verify(&rns)?;
            Ok(assemble(b, &lane_out))
        }

        /// Verify a batch with the fold AND the membership gate on
        /// device; host residual = malformed plane + packed λ̂ signs.
        /// Verdict-identical to the provider's own lowerings and to
        /// [`verify_batch_rns_full`].
        pub fn verify_batch_full(&self, b: &CsrBatch) -> Result<BatchOutcome, GpuError> {
            let rns = pack(b);
            let req = pack_membership(b);
            let fold_out = self.lane.verify(&rns)?;
            let memb_out = self.member.verify(&req)?;
            Ok(assemble_full(b, &rns, &fold_out, &memb_out))
        }

        /// Split verification for measurement: pack once, run the
        /// device fold, assemble (host gates). Returns the lane
        /// outcome too so benches can report channel counts.
        pub fn verify_packed(
            &self,
            b: &CsrBatch,
            rns: &RnsFoldBatch,
        ) -> Result<(BatchOutcome, RnsFoldOutcome), GpuError> {
            let lane_out = self.lane.verify(rns)?;
            Ok((assemble(b, &lane_out), lane_out))
        }

        /// Split FULL verification for measurement: both descriptors
        /// pre-packed; device fold + device membership + host
        /// assembly.
        pub fn verify_packed_full(
            &self,
            b: &CsrBatch,
            rns: &RnsFoldBatch,
            req: &RowEqBatch,
        ) -> Result<BatchOutcome, GpuError> {
            let fold_out = self.lane.verify(rns)?;
            let memb_out = self.member.verify(req)?;
            Ok(assemble_full(b, rns, &fold_out, &memb_out))
        }

        /// Device membership alone (for lane-level timing).
        pub fn member_only(&self, req: &RowEqBatch) -> Result<RowEqOutcome, GpuError> {
            self.member.verify(req)
        }

        /// Device fold alone (for lane-level timing).
        pub fn fold_only(&self, rns: &RnsFoldBatch) -> Result<RnsFoldOutcome, GpuError> {
            self.lane.verify(rns)
        }
    }
}
