//! the batch-CSR kernel (verification — Phase V — over a flattened batch).
//!
//! [`CsrBatch`] is the flattened form of a `Vec<ComboExtract>` — the
//! attempt tensors of `blbatch` laid out as CSR planes (row pointers +
//! column indices + value slots) — the custom-call ABI shape: what
//! would cross a host/device boundary is exactly these arrays,
//! nothing richer. [`verify_batch`] evaluates Phase V
//! over the whole batch under a chosen [`Lowering`] — the
//! L-qq / L-int candidate pair, each at a machine-word tier and a
//! bignum tier, plus the layout-isolated exact reference.
//!
//! Boundary adjudication (two-clause admission test, recorded
//! here because this module is the batch-CSR kernel leg's landing):
//! clause 2 passes — no machine-checked lemma names this code; its
//! assurance instrument is the differential battery against the E3
//! evaluator plus the `blbatch` reference. Clause 1 FAILS as a unit —
//! the Phase-V semantics (candidate membership, attempt/instance
//! verdict shape) are downstream consumer semantics, not a structure the
//! producer side shares. So the kernel lands in-tree (geolog-side);
//! the shared substrate underneath (exact-$\mathbb{Q}$ limb-plane
//! batch arithmetic) is already queued for `maitria-coalition/kernels`
//! with its own gate, and this wrapper graduates WITH that substrate
//! if the shared slot kernels arrive — never forked ahead of the
//! queue's own gate.
//!
//! Soundness discipline (the consumer-lane law): **VCARM is
//! vacuous** — there is no floating point anywhere in this module, no
//! rounding mode exists to be careful about. **DATERWI is the
//! architecture**: the machine-word lanes conclude only when every
//! operation fits; any capacity refusal (pack-time misfit, fold-time
//! overflow) routes the attempt to the exact reference path. The fast
//! lanes never produce a verdict the exact path would not — they are
//! accelerators with a standing deferral, not a semantics fork.

use crate::blbatch::ComboExtract;
use crate::qq::QQ;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

/// The flattened batch. Index vocabulary: *instance* → range of
/// *attempts* (`inst_ptr`); *attempt* → range of *entries*
/// (`entry_ptr`), a candidate count, and a base into the *rows* pool;
/// *row* → range of *nnz* (`row_ptr`); *nnz* → (column, value slot).
/// Rows for attempt `a` are laid out contiguously from `row_base[a]`:
/// first one vehicle row per entry, then `cand_count[a]` candidate
/// rows, then the conclusion row.
///
/// `PartialEq` is derived deliberately: [`CsrBuilder`] emits planes in
/// exactly [`CsrBatch::pack`]'s slot/row order, so the feed
/// differential ("direct emission ≡ build-then-pack") is plane-for-
/// plane structural equality, not merely verdict agreement.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CsrBatch {
    /// Instance → attempt range. `len = instances + 1`.
    pub inst_ptr: Vec<u32>,
    /// Per instance: the `decided_false` diagnostic (verdict is
    /// attempt-absence either way; carried for parity with
    /// [`ComboExtract`]).
    pub decided_false: Vec<bool>,

    /// Per attempt: dense column-space extent.
    pub n_monos: Vec<u32>,
    /// Attempt → entry range. `len = attempts + 1`.
    pub entry_ptr: Vec<u32>,
    /// Per attempt: number of candidate rows.
    pub cand_count: Vec<u32>,
    /// Per attempt: first row id (vehicles, candidates, conclusion).
    pub row_base: Vec<u32>,
    /// Per attempt: every value slot fits the small planes — the
    /// machine-word lanes may run (DATERWI eligibility, grain =
    /// attempt, matching the promotion ladder's grain).
    pub small_ok: Vec<bool>,
    /// Per attempt: `lambdas.len() != vehicles.len()` in the source —
    /// verdict false without arithmetic (mirrors the reference).
    pub malformed: Vec<bool>,
    /// Per attempt: common denominator of every fold participant
    /// (lambdas, vehicle values, conclusion values — candidates do not
    /// enter the fold), when it fits `u64`; `0` = not computable at
    /// this width (L-int-small defers).
    pub lint_den: Vec<u64>,

    /// Per entry: value slot of $\lambda_i$.
    pub lam_slot: Vec<u32>,

    /// Row → nnz range. `len = rows + 1`.
    pub row_ptr: Vec<u32>,
    /// Per nnz: column (strictly ascending within a row).
    pub nnz_col: Vec<u32>,
    /// Per nnz: value slot.
    pub nnz_slot: Vec<u32>,

    /// Value pool, exact plane (always populated — the deferral
    /// target and the packing source).
    pub exact: Vec<QQ>,
    /// Value pool, small planes (valid where the owning attempt has
    /// `small_ok`; unspecified elsewhere).
    pub small_num: Vec<i64>,
    pub small_den: Vec<u64>,
}

/// Phase-V lowering choice — the L-qq / L-int candidate pair at
/// two capacity tiers, plus the layout-isolated exact reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lowering {
    /// Exact `QQ` arithmetic over the CSR layout (canonicalizing every
    /// op — the per-op-reduce baseline; must agree with
    /// `blbatch::verify_instance` verbatim).
    CsrRef,
    /// L-qq, machine words: `(i64, u64)` values, `(i128, u128)`
    /// accumulators, deferred normalization, cross-multiplied
    /// equality; overflow defers.
    LqqSmall,
    /// L-int, machine words: per-attempt common denominator (`u64`),
    /// scaled-integer fold in checked `i128`; misfit defers.
    LintSmall,
    /// L-qq, bignum: deferred normalization in `BigInt`/`BigUint`
    /// (no gcd during the fold), cross-multiplied equality — measures
    /// denominator growth against `CsrRef`'s per-op reduction.
    LqqBig,
    /// L-int, bignum: common denominator + pure integer fold — the
    /// design's strictly-cheaper-device-arithmetic candidate at the
    /// tier X1-class instances need.
    LintBig,
}

/// Batch verdicts + the DATERWI receipt.
#[derive(Debug, Clone, Default)]
pub struct BatchOutcome {
    /// Per instance: OR over its attempts (same verdict as the
    /// evaluator's first-success return — exact arithmetic makes
    /// branch order irrelevant).
    pub verdicts: Vec<bool>,
    /// Attempts concluded on the requested lane.
    pub attempts_fast: usize,
    /// Attempts routed to the exact reference path (capacity refusal
    /// at pack or overflow mid-fold — never a wrong verdict).
    pub attempts_deferred: usize,
}

// ---------------------------------------------------------------- pack

fn lcm_u64(a: u64, b: u64) -> Option<u64> {
    fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a
    }
    if a == 0 || b == 0 {
        return None;
    }
    (a / gcd(a, b)).checked_mul(b)
}

impl CsrBatch {
    /// Flatten a slice of extractions. Lossless: the exact plane
    /// carries every value; small planes and `lint_den` are capacity
    /// annotations, computed here so the verify lanes stay branch-lean.
    pub fn pack(extracts: &[ComboExtract]) -> CsrBatch {
        let mut b = CsrBatch::default();
        b.inst_ptr.push(0);
        b.entry_ptr.push(0);
        b.row_ptr.push(0);

        // Push one value; returns its slot. Small-plane misfit is
        // recorded via the returned flag, aggregated per attempt.
        fn push_val(b: &mut CsrBatch, q: &QQ) -> (u32, bool) {
            let slot = b.exact.len() as u32;
            let (sn, sd, fits) = match q.to_small() {
                Some((n, d)) => (n, d, true),
                None => (0, 1, false),
            };
            b.exact.push(q.clone());
            b.small_num.push(sn);
            b.small_den.push(sd);
            (slot, fits)
        }

        fn push_row(b: &mut CsrBatch, v: &[(u32, QQ)]) -> bool {
            let mut fits = true;
            let mut prev: Option<u32> = None;
            for (col, q) in v {
                debug_assert!(prev.is_none_or(|p| *col > p), "columns ascend");
                prev = Some(*col);
                let (slot, f) = push_val(b, q);
                fits &= f;
                b.nnz_col.push(*col);
                b.nnz_slot.push(slot);
            }
            b.row_ptr.push(b.nnz_col.len() as u32);
            fits
        }

        for e in extracts {
            for a in &e.attempts {
                let mut fits = true;
                let mut den_lcm: Option<u64> = Some(1);
                let fold_den = |q: &QQ, den_lcm: &mut Option<u64>| {
                    *den_lcm = den_lcm
                        .and_then(|l| u64::try_from(q.den()).ok().and_then(|d| lcm_u64(l, d)));
                };

                b.n_monos.push(a.n_monos);
                b.row_base.push((b.row_ptr.len() - 1) as u32);
                b.malformed.push(a.lambdas.len() != a.vehicles.len());

                for l in &a.lambdas {
                    let (slot, f) = push_val(&mut b, l);
                    fits &= f;
                    fold_den(l, &mut den_lcm);
                    b.lam_slot.push(slot);
                }
                b.entry_ptr.push(b.lam_slot.len() as u32);

                for v in &a.vehicles {
                    fits &= push_row(&mut b, v);
                    for (_, q) in v {
                        fold_den(q, &mut den_lcm);
                    }
                }
                for c in &a.cand_polys {
                    fits &= push_row(&mut b, c);
                }
                b.cand_count.push(a.cand_polys.len() as u32);
                fits &= push_row(&mut b, &a.conclusion);
                for (_, q) in &a.conclusion {
                    fold_den(q, &mut den_lcm);
                }

                b.small_ok.push(fits);
                b.lint_den.push(den_lcm.unwrap_or(0));
            }
            b.inst_ptr.push(b.n_monos.len() as u32);
            b.decided_false.push(e.decided_false);
        }
        b
    }

    /// Flatten by MOVE — the feed twin of [`CsrBatch::pack`]. Same
    /// planes, zero value clones: the nested extracts are consumed and
    /// every `QQ` moves into the value pool. `pack` stays the
    /// independent clone-based spec; the `from_extracts == pack`
    /// property (proptest + corpus) is the differential between them.
    pub fn from_extracts(extracts: Vec<ComboExtract>) -> CsrBatch {
        let mut b = CsrBuilder::new();
        let mut row_buf: Vec<(u32, QQ)> = Vec::new();
        for e in extracts {
            for a in e.attempts {
                b.begin_attempt();
                for l in a.lambdas {
                    b.push_lambda(l);
                }
                for v in a.vehicles {
                    row_buf.extend(v);
                    b.push_vehicle_row(&mut row_buf);
                }
                for c in a.cand_polys {
                    row_buf.extend(c);
                    b.push_cand_row(&mut row_buf);
                }
                row_buf.extend(a.conclusion);
                b.finish_attempt(&mut row_buf, a.n_monos);
            }
            b.finish_instance(e.decided_false);
        }
        b.finish()
    }

    /// Concatenate a sibling batch onto this one (offset fixup on every
    /// index plane). The composition verb for a SHARDED feed: instance
    /// extraction is embarrassingly parallel, so per-shard builders +
    /// in-order `append` give the batch a rayon story without a shared
    /// mutable builder. Property (proptest): appending split halves
    /// equals packing the whole.
    pub fn append(&mut self, o: CsrBatch) {
        // Hard assert, not debug_assert: a `CsrBatch::default()` receiver
        // (no leading 0) silently mis-splices every +1-sentinel plane in
        // release builds — entry_ptr comes out one short and the first
        // downstream reader panics far from the cause (found live by the
        // M-c X1 run's append-check, 2026-07-20: `len is 128 but the
        // index is 128` at `attempt_exact`, three phases later). append
        // is shard-grain cold; the check is free.
        assert!(
            !self.inst_ptr.is_empty() && !o.inst_ptr.is_empty(),
            "append requires builder/pack-shaped batches (leading 0 present) \
             — seed the fold from the first shard, not CsrBatch::default()"
        );
        let attempts0 = self.n_monos.len() as u32;
        let lam0 = self.lam_slot.len() as u32;
        let rows0 = (self.row_ptr.len() - 1) as u32;
        let nnz0 = self.nnz_col.len() as u32;
        let slots0 = self.exact.len() as u32;

        self.inst_ptr
            .extend(o.inst_ptr.iter().skip(1).map(|p| p + attempts0));
        self.decided_false.extend(o.decided_false);

        self.n_monos.extend(o.n_monos);
        self.entry_ptr
            .extend(o.entry_ptr.iter().skip(1).map(|p| p + lam0));
        self.cand_count.extend(o.cand_count);
        self.row_base.extend(o.row_base.iter().map(|r| r + rows0));
        self.small_ok.extend(o.small_ok);
        self.malformed.extend(o.malformed);
        self.lint_den.extend(o.lint_den);

        self.lam_slot.extend(o.lam_slot.iter().map(|s| s + slots0));

        self.row_ptr
            .extend(o.row_ptr.iter().skip(1).map(|p| p + nnz0));
        self.nnz_col.extend(o.nnz_col);
        self.nnz_slot.extend(o.nnz_slot.iter().map(|s| s + slots0));

        self.exact.extend(o.exact);
        self.small_num.extend(o.small_num);
        self.small_den.extend(o.small_den);
    }

    pub fn instances(&self) -> usize {
        self.inst_ptr.len() - 1
    }

    pub fn attempts(&self) -> usize {
        self.n_monos.len()
    }

    fn nnz_of(&self, row: u32) -> (usize, usize) {
        (
            self.row_ptr[row as usize] as usize,
            self.row_ptr[row as usize + 1] as usize,
        )
    }

    /// Rows equal? Values compared on the plane the caller trusts:
    /// canonical rationals, so positional (col, num, den) equality
    /// decides polynomial equality — same argument as the reference's
    /// `Vec` equality.
    fn rows_eq_small(&self, r1: u32, r2: u32) -> bool {
        let (a0, a1) = self.nnz_of(r1);
        let (b0, b1) = self.nnz_of(r2);
        a1 - a0 == b1 - b0
            && (0..a1 - a0).all(|k| {
                let (i, j) = (a0 + k, b0 + k);
                self.nnz_col[i] == self.nnz_col[j]
                    && self.small_num[self.nnz_slot[i] as usize]
                        == self.small_num[self.nnz_slot[j] as usize]
                    && self.small_den[self.nnz_slot[i] as usize]
                        == self.small_den[self.nnz_slot[j] as usize]
            })
    }

    fn rows_eq_exact(&self, r1: u32, r2: u32) -> bool {
        let (a0, a1) = self.nnz_of(r1);
        let (b0, b1) = self.nnz_of(r2);
        a1 - a0 == b1 - b0
            && (0..a1 - a0).all(|k| {
                let (i, j) = (a0 + k, b0 + k);
                self.nnz_col[i] == self.nnz_col[j]
                    && self.exact[self.nnz_slot[i] as usize]
                        == self.exact[self.nnz_slot[j] as usize]
            })
    }

    /// Membership: every vehicle row equals some candidate row.
    /// Linear scan over the candidate pool — the evaluator's own
    /// access pattern (pool sizes are small at every measured shape).
    fn membership(&self, a: usize, exact_plane: bool) -> bool {
        let (e0, e1) = (self.entry_ptr[a] as usize, self.entry_ptr[a + 1] as usize);
        let n_entries = e1 - e0;
        let base = self.row_base[a];
        let cands = base + n_entries as u32..base + n_entries as u32 + self.cand_count[a];
        (0..n_entries).all(|k| {
            let veh = base + k as u32;
            cands.clone().any(|c| {
                if exact_plane {
                    self.rows_eq_exact(veh, c)
                } else {
                    self.rows_eq_small(veh, c)
                }
            })
        })
    }

    fn concl_row(&self, a: usize) -> u32 {
        let n_entries = self.entry_ptr[a + 1] - self.entry_ptr[a];
        self.row_base[a] + n_entries + self.cand_count[a]
    }
}

// -------------------------------------------------------- the builder

/// Rollback point for [`CsrBuilder::truncate`] — the refusal contract:
/// a Walk refusal mid-instance must drop the WHOLE instance to the
/// evaluator path, leaving the batch as if the instance
/// was never fed.
#[derive(Debug, Clone, Copy)]
pub struct CsrMark {
    inst: usize,
    attempts: usize,
    lam: usize,
    rows: usize,
    nnz: usize,
    slots: usize,
}

/// Streaming plane emission — the feed's write surface. Push order per
/// attempt is fixed (lambdas, vehicle rows, candidate rows, then the
/// conclusion via [`CsrBuilder::finish_attempt`]) and matches
/// [`CsrBatch::pack`]'s slot order exactly, so a builder-fed batch is
/// plane-for-plane EQUAL to packing the nested form of the same data.
/// Values arrive by move; rows arrive as drained scratch buffers so
/// the caller's allocation is reused across rows. Capacity annotations
/// (`small_ok`, `lint_den`) are computed incrementally, mirroring
/// `pack` (both are order-independent: AND-fold and lcm-with-
/// overflow-to-None, whose intermediates all divide the final lcm).
#[derive(Debug, Default)]
pub struct CsrBuilder {
    b: CsrBatch,
    fits: bool,
    den_lcm: Option<u64>,
    n_lambdas: usize,
    n_vehicles: usize,
    attempt_open: bool,
}

impl CsrBuilder {
    pub fn new() -> CsrBuilder {
        let mut b = CsrBatch::default();
        b.inst_ptr.push(0);
        b.entry_ptr.push(0);
        b.row_ptr.push(0);
        CsrBuilder {
            b,
            fits: true,
            den_lcm: Some(1),
            n_lambdas: 0,
            n_vehicles: 0,
            attempt_open: false,
        }
    }

    /// Instances fully fed so far (mark/rollback grain).
    pub fn instances(&self) -> usize {
        self.b.inst_ptr.len() - 1
    }

    pub fn mark(&self) -> CsrMark {
        debug_assert!(!self.attempt_open, "mark between instances only");
        CsrMark {
            inst: self.b.inst_ptr.len(),
            attempts: self.b.n_monos.len(),
            lam: self.b.lam_slot.len(),
            rows: self.b.row_ptr.len(),
            nnz: self.b.nnz_col.len(),
            slots: self.b.exact.len(),
        }
    }

    /// Roll back to `m` — discards every instance (and any half-open
    /// attempt) fed since. O(discarded).
    pub fn truncate(&mut self, m: CsrMark) {
        let b = &mut self.b;
        b.inst_ptr.truncate(m.inst);
        b.decided_false.truncate(m.inst - 1);
        b.n_monos.truncate(m.attempts);
        b.entry_ptr.truncate(m.attempts + 1);
        b.cand_count.truncate(m.attempts);
        b.row_base.truncate(m.attempts);
        b.small_ok.truncate(m.attempts);
        b.malformed.truncate(m.attempts);
        b.lint_den.truncate(m.attempts);
        b.lam_slot.truncate(m.lam);
        b.row_ptr.truncate(m.rows);
        b.nnz_col.truncate(m.nnz);
        b.nnz_slot.truncate(m.nnz);
        b.exact.truncate(m.slots);
        b.small_num.truncate(m.slots);
        b.small_den.truncate(m.slots);
        self.attempt_open = false;
    }

    fn push_val(&mut self, q: QQ) -> u32 {
        let slot = self.b.exact.len() as u32;
        let (sn, sd) = match q.to_small() {
            Some((n, d)) => (n, d),
            None => {
                self.fits = false;
                (0, 1)
            }
        };
        self.b.exact.push(q);
        self.b.small_num.push(sn);
        self.b.small_den.push(sd);
        slot
    }

    fn fold_den(den_lcm: &mut Option<u64>, q: &QQ) {
        *den_lcm = den_lcm.and_then(|l| u64::try_from(q.den()).ok().and_then(|d| lcm_u64(l, d)));
    }

    /// Drain `row` (sorted ascending by column — asserted) into the
    /// nnz planes; returns nothing, the row id is implicit (rows are
    /// consecutive). `fold` = the row's values participate in the
    /// L-int common denominator (vehicles and the conclusion do;
    /// candidates do not).
    fn push_row(&mut self, row: &mut Vec<(u32, QQ)>, fold: bool) {
        let mut prev: Option<u32> = None;
        for (col, q) in row.drain(..) {
            debug_assert!(prev.is_none_or(|p| col > p), "columns ascend");
            prev = Some(col);
            if fold {
                Self::fold_den(&mut self.den_lcm, &q);
            }
            let slot = self.push_val(q);
            self.b.nnz_col.push(col);
            self.b.nnz_slot.push(slot);
        }
        self.b.row_ptr.push(self.b.nnz_col.len() as u32);
    }

    pub fn begin_attempt(&mut self) {
        debug_assert!(!self.attempt_open, "finish the previous attempt first");
        self.attempt_open = true;
        self.fits = true;
        self.den_lcm = Some(1);
        self.n_lambdas = 0;
        self.n_vehicles = 0;
        self.b.row_base.push((self.b.row_ptr.len() - 1) as u32);
    }

    /// Lambdas first — before any row of the attempt.
    pub fn push_lambda(&mut self, l: QQ) {
        debug_assert!(self.attempt_open && self.n_vehicles == 0, "lambdas first");
        Self::fold_den(&mut self.den_lcm, &l);
        let slot = self.push_val(l);
        self.b.lam_slot.push(slot);
        self.n_lambdas += 1;
    }

    /// Vehicle rows, one per entry, after the lambdas.
    pub fn push_vehicle_row(&mut self, row: &mut Vec<(u32, QQ)>) {
        debug_assert!(self.attempt_open);
        self.push_row(row, true);
        self.n_vehicles += 1;
    }

    /// Candidate rows, after the vehicles. Values are membership-only:
    /// they enter `small_ok` (compared on the small plane) but not the
    /// fold's common denominator.
    pub fn push_cand_row(&mut self, row: &mut Vec<(u32, QQ)>) {
        debug_assert!(self.attempt_open);
        self.push_row(row, false);
    }

    /// Conclusion row + the attempt's column extent; closes the attempt.
    pub fn finish_attempt(&mut self, conclusion: &mut Vec<(u32, QQ)>, n_monos: u32) {
        debug_assert!(self.attempt_open);
        let n_cands = (self.b.row_ptr.len() - 1) as u32
            - self.b.row_base[self.b.row_base.len() - 1]
            - self.n_vehicles as u32;
        self.push_row(conclusion, true);
        self.b.n_monos.push(n_monos);
        self.b.entry_ptr.push(self.b.lam_slot.len() as u32);
        self.b.cand_count.push(n_cands);
        self.b.malformed.push(self.n_lambdas != self.n_vehicles);
        self.b.small_ok.push(self.fits);
        self.b.lint_den.push(self.den_lcm.unwrap_or(0));
        self.attempt_open = false;
    }

    /// Close the current instance (its attempts are whatever was fed
    /// since the previous close).
    pub fn finish_instance(&mut self, decided_false: bool) {
        debug_assert!(!self.attempt_open, "finish the open attempt first");
        self.b.inst_ptr.push(self.b.n_monos.len() as u32);
        self.b.decided_false.push(decided_false);
    }

    pub fn finish(self) -> CsrBatch {
        debug_assert!(!self.attempt_open, "finish the open attempt first");
        self.b
    }
}

// ------------------------------------------------------ attempt lanes

/// Scratch reused across attempts (allocated once per batch at the
/// maximum column extent — mechanical sympathy over per-attempt
/// allocation).
struct Scratch {
    qq: Vec<QQ>,
    lqq: Vec<(i128, u128)>,
    lint: Vec<i128>,
    big_qq: Vec<(BigInt, BigUint)>,
    big_int: Vec<BigInt>,
}

impl Scratch {
    fn for_batch(b: &CsrBatch) -> Scratch {
        let m = b.n_monos.iter().copied().max().unwrap_or(0) as usize;
        Scratch {
            qq: vec![QQ::zero(); m],
            lqq: vec![(0, 1); m],
            lint: vec![0; m],
            big_qq: vec![(BigInt::zero(), BigUint::one()); m],
            big_int: vec![BigInt::zero(); m],
        }
    }
}

/// Exact reference over the CSR layout — the deferral target and the
/// layout-isolated twin of `blbatch::verify_attempt`.
fn attempt_csr_ref(b: &CsrBatch, a: usize, s: &mut Scratch) -> bool {
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    if b.malformed[a] {
        return false;
    }
    if !(e0..e1).all(|e| b.exact[b.lam_slot[e] as usize].is_nonneg()) {
        return false;
    }
    if !b.membership(a, true) {
        return false;
    }
    let m = b.n_monos[a] as usize;
    let fold = &mut s.qq[..m];
    fold.fill(QQ::zero());
    for (k, e) in (e0..e1).enumerate() {
        let lam = &b.exact[b.lam_slot[e] as usize];
        let veh = b.row_base[a] + k as u32;
        let (n0, n1) = b.nnz_of(veh);
        for i in n0..n1 {
            let col = b.nnz_col[i] as usize;
            let v = &b.exact[b.nnz_slot[i] as usize];
            fold[col] = fold[col].add(&lam.mul(v));
        }
    }
    let (c0, c1) = b.nnz_of(b.concl_row(a));
    let mut next = c0;
    for (col, f) in fold.iter().enumerate() {
        let ok = if next < c1 && b.nnz_col[next] as usize == col {
            let q = &b.exact[b.nnz_slot[next] as usize];
            next += 1;
            f == q
        } else {
            f.is_zero()
        };
        if !ok {
            return false;
        }
    }
    next == c1
}

/// L-qq at machine width: deferred-normalization rational fold in
/// checked `(i128, u128)`. `None` = capacity refusal (DATERWI).
fn attempt_lqq_small(b: &CsrBatch, a: usize, s: &mut Scratch) -> Option<bool> {
    if !b.small_ok[a] {
        return None;
    }
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    if b.malformed[a] {
        return Some(false);
    }
    if !(e0..e1).all(|e| b.small_num[b.lam_slot[e] as usize] >= 0) {
        return Some(false);
    }
    if !b.membership(a, false) {
        return Some(false);
    }
    let m = b.n_monos[a] as usize;
    let fold = &mut s.lqq[..m];
    fold.fill((0, 1));
    for (k, e) in (e0..e1).enumerate() {
        let ln = b.small_num[b.lam_slot[e] as usize] as i128;
        let ld = b.small_den[b.lam_slot[e] as usize] as u128;
        let veh = b.row_base[a] + k as u32;
        let (n0, n1) = b.nnz_of(veh);
        for i in n0..n1 {
            let col = b.nnz_col[i] as usize;
            let vn = b.small_num[b.nnz_slot[i] as usize] as i128;
            let vd = b.small_den[b.nnz_slot[i] as usize] as u128;
            // term = (ln*vn) / (ld*vd); acc += term, unnormalized.
            let tn = ln.checked_mul(vn)?; // |i64|*|i64| always fits, kept checked for uniformity
            let td = ld.checked_mul(vd)?;
            let (an, ad) = fold[col];
            let tn_ad = tn.checked_mul(i128::try_from(ad).ok()?)?;
            let an_td = an.checked_mul(i128::try_from(td).ok()?)?;
            fold[col] = (an_td.checked_add(tn_ad)?, ad.checked_mul(td)?);
        }
    }
    let (c0, c1) = b.nnz_of(b.concl_row(a));
    let mut next = c0;
    for (col, (an, ad)) in fold.iter().enumerate() {
        let (cn, cd) = if next < c1 && b.nnz_col[next] as usize == col {
            let slot = b.nnz_slot[next] as usize;
            next += 1;
            (b.small_num[slot] as i128, b.small_den[slot] as u128)
        } else {
            (0, 1)
        };
        // an/ad == cn/cd  ⇔  an*cd == cn*ad (dens positive).
        let l = an.checked_mul(i128::try_from(cd).ok()?)?;
        let r = cn.checked_mul(i128::try_from(*ad).ok()?)?;
        if l != r {
            return Some(false);
        }
    }
    Some(next == c1)
}

/// L-int at machine width: scale every fold participant to the
/// attempt's common denominator `D` (pack-computed), fold in pure
/// checked-`i128` integers, compare at scale `D^2`.
fn attempt_lint_small(b: &CsrBatch, a: usize, s: &mut Scratch) -> Option<bool> {
    let d = b.lint_den[a];
    if !b.small_ok[a] || d == 0 {
        return None;
    }
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    if b.malformed[a] {
        return Some(false);
    }
    if !(e0..e1).all(|e| b.small_num[b.lam_slot[e] as usize] >= 0) {
        return Some(false);
    }
    if !b.membership(a, false) {
        return Some(false);
    }
    let m = b.n_monos[a] as usize;
    let fold = &mut s.lint[..m];
    fold.fill(0);
    for (k, e) in (e0..e1).enumerate() {
        let slot = b.lam_slot[e] as usize;
        // λ scaled: num * (D / den) — exact by construction (den | D).
        let ls = (b.small_num[slot] as i128).checked_mul((d / b.small_den[slot]) as i128)?;
        let veh = b.row_base[a] + k as u32;
        let (n0, n1) = b.nnz_of(veh);
        for i in n0..n1 {
            let col = b.nnz_col[i] as usize;
            let vslot = b.nnz_slot[i] as usize;
            let vs = (b.small_num[vslot] as i128).checked_mul((d / b.small_den[vslot]) as i128)?;
            fold[col] = fold[col].checked_add(ls.checked_mul(vs)?)?;
        }
    }
    let (c0, c1) = b.nnz_of(b.concl_row(a));
    let mut next = c0;
    for (col, f) in fold.iter().enumerate() {
        let cs = if next < c1 && b.nnz_col[next] as usize == col {
            let slot = b.nnz_slot[next] as usize;
            next += 1;
            // c scaled to D²: num * (D/den) * D.
            (b.small_num[slot] as i128)
                .checked_mul((d / b.small_den[slot]) as i128)?
                .checked_mul(d as i128)?
        } else {
            0
        };
        if *f != cs {
            return Some(false);
        }
    }
    Some(next == c1)
}

/// L-qq at bignum width: deferred normalization (no gcd anywhere in
/// the fold), cross-multiplied equality at the end. Never defers.
fn attempt_lqq_big(b: &CsrBatch, a: usize, s: &mut Scratch) -> bool {
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    if b.malformed[a] {
        return false;
    }
    if !(e0..e1).all(|e| b.exact[b.lam_slot[e] as usize].is_nonneg()) {
        return false;
    }
    if !b.membership(a, true) {
        return false;
    }
    let m = b.n_monos[a] as usize;
    let fold = &mut s.big_qq[..m];
    for f in fold.iter_mut() {
        *f = (BigInt::zero(), BigUint::one());
    }
    for (k, e) in (e0..e1).enumerate() {
        let lam = &b.exact[b.lam_slot[e] as usize];
        let veh = b.row_base[a] + k as u32;
        let (n0, n1) = b.nnz_of(veh);
        for i in n0..n1 {
            let col = b.nnz_col[i] as usize;
            let v = &b.exact[b.nnz_slot[i] as usize];
            let tn = lam.num() * v.num();
            let td = lam.den() * v.den();
            let (an, ad) = &fold[col];
            fold[col] = (
                an * BigInt::from(td.clone()) + tn * BigInt::from(ad.clone()),
                ad * td,
            );
        }
    }
    let (c0, c1) = b.nnz_of(b.concl_row(a));
    let mut next = c0;
    for (col, (an, ad)) in fold.iter().enumerate() {
        let ok = if next < c1 && b.nnz_col[next] as usize == col {
            let q = &b.exact[b.nnz_slot[next] as usize];
            next += 1;
            an * BigInt::from(q.den().clone()) == q.num() * BigInt::from(ad.clone())
        } else {
            an.is_zero()
        };
        if !ok {
            return false;
        }
    }
    next == c1
}

/// L-int at bignum width: common denominator (computed here — the
/// bignum lane needs no pack-time fit), scaled-integer fold, integer
/// equality. Never defers.
fn attempt_lint_big(b: &CsrBatch, a: usize, s: &mut Scratch) -> bool {
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    if b.malformed[a] {
        return false;
    }
    if !(e0..e1).all(|e| b.exact[b.lam_slot[e] as usize].is_nonneg()) {
        return false;
    }
    if !b.membership(a, true) {
        return false;
    }
    fn gcd_big(mut a: BigUint, mut b: BigUint) -> BigUint {
        while !b.is_zero() {
            let r = &a % &b;
            a = b;
            b = r;
        }
        a
    }
    let mut d = BigUint::one();
    let fold_den = |q: &QQ, d: &mut BigUint| {
        let g = gcd_big(d.clone(), q.den().clone());
        *d = (&*d / g) * q.den();
    };
    for e in e0..e1 {
        fold_den(&b.exact[b.lam_slot[e] as usize], &mut d);
    }
    let n_entries = e1 - e0;
    for k in 0..n_entries {
        let (n0, n1) = b.nnz_of(b.row_base[a] + k as u32);
        for i in n0..n1 {
            fold_den(&b.exact[b.nnz_slot[i] as usize], &mut d);
        }
    }
    let (c0, c1) = b.nnz_of(b.concl_row(a));
    for i in c0..c1 {
        fold_den(&b.exact[b.nnz_slot[i] as usize], &mut d);
    }

    let scale = |q: &QQ, d: &BigUint| -> BigInt { q.num() * BigInt::from(d / q.den()) };
    let m = b.n_monos[a] as usize;
    let fold = &mut s.big_int[..m];
    for f in fold.iter_mut() {
        *f = BigInt::zero();
    }
    for (k, e) in (e0..e1).enumerate() {
        let ls = scale(&b.exact[b.lam_slot[e] as usize], &d);
        let (n0, n1) = b.nnz_of(b.row_base[a] + k as u32);
        for i in n0..n1 {
            let col = b.nnz_col[i] as usize;
            let vs = scale(&b.exact[b.nnz_slot[i] as usize], &d);
            fold[col] += &ls * vs;
        }
    }
    let big_d = BigInt::from(d.clone());
    let mut next = c0;
    for (col, f) in fold.iter().enumerate() {
        let cs = if next < c1 && b.nnz_col[next] as usize == col {
            let q = &b.exact[b.nnz_slot[next] as usize];
            next += 1;
            scale(q, &d) * &big_d
        } else {
            BigInt::zero()
        };
        if *f != cs {
            return false;
        }
    }
    next == c1
}

/// Fold-length crossover between the two exact lanes, from the
/// batch-CSR measurement receipts: deferred-norm
/// L-qq wins short folds decisively (4–50x at 1–2 entries — L-int's
/// lcm + scaling overhead dominates there), integer L-int wins long
/// folds (11x at 238 entries — unnormalized denominators grow one
/// multiplication per addition, a quadratic bit-cost), and the
/// measured crossing at the 600-bit tier sits near 24 entries.
/// Canonicalize-per-op (`CsrRef`) was never the best exact lane at any
/// measured shape (5.8–60x behind) — it stays as the layout-isolated
/// differential reference, not a dispatch target.
pub const EXACT_LQQ_MAX_ENTRIES: usize = 24;

/// The exact adjudication a capacity deferral routes to: the cheaper
/// of the two exact lowerings, dispatched on fold length per the
/// measured crossover.
fn attempt_exact(b: &CsrBatch, a: usize, s: &mut Scratch) -> bool {
    let entries = (b.entry_ptr[a + 1] - b.entry_ptr[a]) as usize;
    if entries <= EXACT_LQQ_MAX_ENTRIES {
        attempt_lqq_big(b, a, s)
    } else {
        attempt_lint_big(b, a, s)
    }
}

// ------------------------------------------- sibling-crate surface

/// The value-independent gates of one attempt, on the exact plane:
/// well-formedness, λ nonnegativity, and candidate membership — the
/// checks every lowering runs before (or beside) its fold. Exposed
/// for the `-gpu` sibling crate, whose device lane computes only the
/// fold; semantics identical to what [`verify_batch`]'s lanes apply.
pub fn attempt_gates_exact(b: &CsrBatch, a: usize) -> bool {
    let (e0, e1) = (b.entry_ptr[a] as usize, b.entry_ptr[a + 1] as usize);
    !b.malformed[a]
        && (e0..e1).all(|e| b.exact[b.lam_slot[e] as usize].is_nonneg())
        && b.membership(a, true)
}

/// Full exact adjudication of one attempt (gates + fold on the exact
/// plane, dispatched per the measured [`EXACT_LQQ_MAX_ENTRIES`]
/// crossover) — the deferral target the `-gpu` sibling routes refused
/// attempts to. Allocates its own scratch; for whole-batch work
/// prefer [`verify_batch`].
pub fn verify_attempt_exact(b: &CsrBatch, a: usize) -> bool {
    let mut s = Scratch::for_batch(b);
    attempt_exact(b, a, &mut s)
}

// ----------------------------------------------------------- batch API

/// Phase V over the whole batch under one lowering. Verdict per
/// instance = OR over its attempts; a machine-width lane's capacity
/// refusal routes that attempt to the exact reference (the DATERWI
/// deferral — counted in the outcome, never guessed through).
pub fn verify_batch(b: &CsrBatch, lane: Lowering) -> BatchOutcome {
    let mut s = Scratch::for_batch(b);
    let mut out = BatchOutcome::default();
    for inst in 0..b.instances() {
        let (a0, a1) = (b.inst_ptr[inst] as usize, b.inst_ptr[inst + 1] as usize);
        let mut verdict = false;
        for a in a0..a1 {
            let att = match lane {
                Lowering::CsrRef => {
                    out.attempts_fast += 1;
                    attempt_csr_ref(b, a, &mut s)
                }
                Lowering::LqqBig => {
                    out.attempts_fast += 1;
                    attempt_lqq_big(b, a, &mut s)
                }
                Lowering::LintBig => {
                    out.attempts_fast += 1;
                    attempt_lint_big(b, a, &mut s)
                }
                Lowering::LqqSmall => match attempt_lqq_small(b, a, &mut s) {
                    Some(v) => {
                        out.attempts_fast += 1;
                        v
                    }
                    None => {
                        out.attempts_deferred += 1;
                        attempt_exact(b, a, &mut s)
                    }
                },
                Lowering::LintSmall => match attempt_lint_small(b, a, &mut s) {
                    Some(v) => {
                        out.attempts_fast += 1;
                        v
                    }
                    None => {
                        out.attempts_deferred += 1;
                        attempt_exact(b, a, &mut s)
                    }
                },
            };
            verdict |= att;
        }
        out.verdicts.push(verdict);
    }
    out
}

/// Every lowering, in measurement order.
pub const ALL_LOWERINGS: [Lowering; 5] = [
    Lowering::CsrRef,
    Lowering::LqqSmall,
    Lowering::LintSmall,
    Lowering::LqqBig,
    Lowering::LintBig,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blbatch::{verify_instance, ComboAttempt, ComboBranch};

    fn q(n: i64) -> QQ {
        QQ::from_int(n)
    }

    fn qd(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn attempt() -> ComboAttempt {
        ComboAttempt {
            branch: ComboBranch::Core,
            n_monos: 2,
            lambdas: vec![qd(1, 2), q(2)],
            vehicles: vec![vec![(0, q(2)), (1, qd(1, 3))], vec![(0, qd(1, 4))]],
            cand_polys: vec![
                vec![(0, q(2)), (1, qd(1, 3))],
                vec![(0, qd(1, 4))],
                vec![(1, q(7))],
            ],
            // 1/2*(2x + y/3) + 2*(x/4) = x + y/6 + x/2 = 3x/2 + y/6.
            conclusion: vec![(0, qd(3, 2)), (1, qd(1, 6))],
        }
    }

    fn extract(attempts: Vec<ComboAttempt>) -> ComboExtract {
        ComboExtract {
            decided_false: attempts.is_empty(),
            attempts,
        }
    }

    #[test]
    fn all_lanes_agree_with_reference() {
        let good = extract(vec![attempt()]);
        let mut bad_lambda = attempt();
        bad_lambda.lambdas[0] = qd(-1, 2);
        let mut bad_concl = attempt();
        bad_concl.conclusion[0].1 = q(4);
        let mut bad_member = attempt();
        bad_member.vehicles[1][0].1 = qd(1, 5);
        let empty = extract(vec![]);
        let extracts = vec![
            good,
            extract(vec![bad_lambda]),
            extract(vec![bad_concl]),
            extract(vec![bad_member]),
            empty,
        ];
        let want: Vec<bool> = extracts.iter().map(verify_instance).collect();
        assert_eq!(want, [true, false, false, false, false]);
        let b = CsrBatch::pack(&extracts);
        for lane in ALL_LOWERINGS {
            let out = verify_batch(&b, lane);
            assert_eq!(out.verdicts, want, "{lane:?}");
            assert_eq!(out.attempts_deferred, 0, "{lane:?} deferred at k=1");
        }
    }

    #[test]
    fn or_semantics_and_zero_columns() {
        // Second attempt accepts; first rejects. Conclusion leaves a
        // column untouched by the fold (must read as zero).
        let mut reject = attempt();
        reject.conclusion[1].1 = q(9);
        let accept = ComboAttempt {
            branch: ComboBranch::WireCoord,
            n_monos: 3,
            lambdas: vec![q(1)],
            vehicles: vec![vec![(2, q(5))]],
            cand_polys: vec![vec![(2, q(5))]],
            conclusion: vec![(2, q(5))],
        };
        let e = extract(vec![reject, accept]);
        assert!(verify_instance(&e));
        let b = CsrBatch::pack(&[e]);
        for lane in ALL_LOWERINGS {
            assert_eq!(verify_batch(&b, lane).verdicts, [true], "{lane:?}");
        }
    }

    #[test]
    fn big_values_defer_and_agree() {
        // 2^100-scale values: small planes refuse, verdicts still exact.
        let big = QQ::new(BigInt::from(1) << 100, BigUint::from(3u32));
        let a = ComboAttempt {
            branch: ComboBranch::Core,
            n_monos: 1,
            lambdas: vec![q(3)],
            vehicles: vec![vec![(0, big.clone())]],
            cand_polys: vec![vec![(0, big)]],
            conclusion: vec![(0, QQ::new(BigInt::from(1) << 100, BigUint::one()))],
        };
        let e = extract(vec![a]);
        assert!(verify_instance(&e));
        let b = CsrBatch::pack(std::slice::from_ref(&e));
        for lane in [Lowering::LqqSmall, Lowering::LintSmall] {
            let out = verify_batch(&b, lane);
            assert_eq!(out.verdicts, [true], "{lane:?}");
            assert_eq!(out.attempts_deferred, 1, "{lane:?} must defer");
        }
        for lane in [Lowering::CsrRef, Lowering::LqqBig, Lowering::LintBig] {
            assert_eq!(verify_batch(&b, lane).verdicts, [true], "{lane:?}");
        }
    }

    #[test]
    fn overflow_mid_fold_defers_not_wrong() {
        // Values fit i64 individually but the L-int scale product
        // overflows i128: many distinct prime denominators drive the
        // common denominator past any machine width.
        let primes: [u64; 40] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
        ];
        let vehicle: Vec<(u32, QQ)> = primes
            .iter()
            .enumerate()
            .map(|(i, p)| (i as u32, qd(1, *p)))
            .collect();
        // conclusion = 1 * vehicle.
        let a = ComboAttempt {
            branch: ComboBranch::Core,
            n_monos: primes.len() as u32,
            lambdas: vec![q(1)],
            vehicles: vec![vehicle.clone()],
            cand_polys: vec![vehicle.clone()],
            conclusion: vehicle,
        };
        let e = extract(vec![a]);
        assert!(verify_instance(&e));
        let b = CsrBatch::pack(std::slice::from_ref(&e));
        // lint_den overflows u64 → pack marks 0 → LintSmall defers.
        assert_eq!(b.lint_den[0], 0);
        for lane in ALL_LOWERINGS {
            let out = verify_batch(&b, lane);
            assert_eq!(out.verdicts, [true], "{lane:?}");
        }
    }
}
