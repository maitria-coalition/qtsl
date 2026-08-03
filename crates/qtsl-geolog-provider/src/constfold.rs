//! the flat-replay batch surface for closed integer linear-combination
//! rows (the `PConstExact` conservation/charge family at corpus scale).
//!
//! One `PConstExact` witness family instance — a P-invariant `y` of a
//! P/T net, in the first shipped case — is, as certificate content,
//! nothing but COLUMNS (the standing design ruling: certificates are
//! ordinary meta-schema content — columns, tensors where genuinely
//! tensor-shaped; no intermediate certificate format): a shared sparse
//! plane of signed leaves (`+post` / `−pre`, column-major), a sparse
//! coefficient vector per attempt, a charge operand vector, and one
//! rhs scalar per attempt. [`ConstSystem`] and [`ConstFoldBatch`] are
//! exactly those planes; [`verify_batch`] replays every row of every
//! attempt as a flat sparse fold. A dispatch census measured the
//! per-row term-tree path at 100–450 µs/row against
//! 1.74 ns/leaf-fold for this identical arithmetic — a ~4,000×
//! representation tax; this module is that finding graduated into the
//! provider's own batch surface (the blcsr precedent: consumer-side
//! Phase-V semantics live in-tree; no shared-kernel fork ahead of the
//! kernels queue's own gate).
//!
//! Semantics (the row grammar this surface replays): for attempt `a`
//! over system `s`,
//!   - conservation row `t < n_cols`:  Σ_{leaves i in column t}
//!     y_a[place(i)] · w(i)  =  0
//!   - charge row `t = n_cols`:  Σ_p y_a[p] · m0[p]  =  b_a
//!
//! which is exactly the closed sum-of-products content of the
//! catalogue's `PConstExact` rows for the family (the term-tree and
//! columnar renderings of ONE shared certificate); bit-identity of
//! verdicts against the landed per-row `constExactEvalTrue` dispatch
//! is gated by this crate's conformance battery on synthetic systems
//! (a corpus-scale stratified sample replay backs it out of tree) —
//! the lane law throughout: a lane may change cost,
//! never verdicts.
//!
//! Soundness discipline (the consumer-lane law, verbatim posture from
//! `blcsr`): **VCARM is vacuous** — no floating point exists in this
//! module. **DATERWI is the architecture**: the `i128` lane concludes
//! only where a pack-time exact bound (computed from the actual
//! operands, never asserted) clears `i128` with two bits of margin;
//! every other attempt routes to the exact `BigInt` lane. The fast
//! lane never produces a verdict the exact path would not — it is an
//! accelerator with a standing deferral, not a semantics fork.
//!
//! Path choice inside the `i128` lane (column-major fold vs
//! support-scatter over the place-major mirror) is cost-only and
//! verdict-neutral; [`verify_batch_with`] exposes the forced variants
//! so the conformance battery can assert that neutrality rather than
//! assume it.

use num_bigint::BigInt;
use num_traits::Zero;

/// Sentinel for [`ConstFoldOutcome::first_bad`]: no failing row.
pub const NONE: u32 = u32::MAX;

/// One system's shared planes: the signed leaf columns and the charge
/// operand vector. Leaves are column-major (the CSC planes) with a
/// derived place-major mirror (CSR) for the support-scatter path and
/// for pack-time admission bounds.
#[derive(Debug, Clone, Default)]
pub struct ConstSystem {
    pub n_places: u32,
    /// Conservation columns; the charge row is column `n_cols`.
    pub n_cols: u32,
    /// Column pointer over leaves; `len = n_cols + 1`.
    pub col_ptr: Vec<u32>,
    /// Per leaf: place index.
    pub leaf_place: Vec<u32>,
    /// Per leaf: signed weight (`+post` or `−pre`; never zero).
    pub leaf_w: Vec<i64>,
    /// Place-major mirror: row pointer (`len = n_places + 1`),
    /// column ids and weights in column-ascending order per place.
    pub row_ptr: Vec<u32>,
    pub row_col: Vec<u32>,
    pub row_w: Vec<i64>,
    /// Per place: Σ |w| over its leaves (admission-bound operand;
    /// exact — leaf count < 2^32 and |w| < 2^63 keep this in `u128`).
    pub row_abs: Vec<u128>,
    /// Charge operands, dense.
    pub m0: Vec<i64>,
}

impl ConstSystem {
    /// Build from `(column, place, signed weight)` triplets. Input
    /// order within a column is preserved (the certificate's leaf
    /// order); triplets may arrive in any column order. Zero weights
    /// are a caller bug (the leaf grammar has none) and panic.
    pub fn from_leaves(
        n_places: u32,
        n_cols: u32,
        leaves: &[(u32, u32, i64)],
        m0: Vec<i64>,
    ) -> ConstSystem {
        assert_eq!(m0.len(), n_places as usize, "m0 is dense over places");
        // Stable counting sort by column.
        let mut count = vec![0u32; n_cols as usize + 1];
        for &(c, p, w) in leaves {
            assert!(c < n_cols, "leaf column in range");
            assert!(p < n_places, "leaf place in range");
            assert!(w != 0, "leaf weight nonzero");
            count[c as usize + 1] += 1;
        }
        for i in 0..n_cols as usize {
            count[i + 1] += count[i];
        }
        let col_ptr = count.clone();
        let mut leaf_place = vec![0u32; leaves.len()];
        let mut leaf_w = vec![0i64; leaves.len()];
        let mut cursor = count;
        for &(c, p, w) in leaves {
            let at = cursor[c as usize] as usize;
            leaf_place[at] = p;
            leaf_w[at] = w;
            cursor[c as usize] += 1;
        }
        // Place-major mirror, column-ascending per place (CSC
        // traversal order), plus the absolute-sum plane.
        let mut rcount = vec![0u32; n_places as usize + 1];
        for &p in &leaf_place {
            rcount[p as usize + 1] += 1;
        }
        for i in 0..n_places as usize {
            rcount[i + 1] += rcount[i];
        }
        let row_ptr = rcount.clone();
        let mut row_col = vec![0u32; leaves.len()];
        let mut row_w = vec![0i64; leaves.len()];
        let mut row_abs = vec![0u128; n_places as usize];
        let mut rcursor = rcount;
        for c in 0..n_cols as usize {
            for i in col_ptr[c] as usize..col_ptr[c + 1] as usize {
                let p = leaf_place[i] as usize;
                let at = rcursor[p] as usize;
                row_col[at] = c as u32;
                row_w[at] = leaf_w[i];
                row_abs[p] += leaf_w[i].unsigned_abs() as u128;
                rcursor[p] += 1;
            }
        }
        ConstSystem {
            n_places,
            n_cols,
            col_ptr,
            leaf_place,
            leaf_w,
            row_ptr,
            row_col,
            row_w,
            row_abs,
            m0,
        }
    }

    pub fn n_leaves(&self) -> usize {
        self.leaf_place.len()
    }
}

/// The batch: attempts (sparse coefficient vectors + rhs scalars) over
/// shared systems. Exact planes are always populated (the deferral
/// target and the audit surface); `i128` images exist where the
/// attempt's admission bound cleared.
#[derive(Debug, Clone, Default)]
pub struct ConstFoldBatch {
    pub systems: Vec<ConstSystem>,
    /// Per attempt: owning system.
    pub attempt_sys: Vec<u32>,
    /// Attempt → support range. `len = attempts + 1`.
    pub y_ptr: Vec<u32>,
    /// Support places, strictly ascending per attempt.
    pub y_place: Vec<u32>,
    /// Exact coefficient plane (nonzero by construction).
    pub y_val: Vec<BigInt>,
    /// `i128` image, valid where the owning attempt has `small_ok`.
    /// A support entry that touches NO fold participant (no leaves,
    /// zero `m0`) stores 0 here — its value is provably absent from
    /// every row of both grammars, and the exact plane keeps it.
    pub y_i128: Vec<i128>,
    /// Per attempt: charge rhs, exact + admitted image.
    pub b_val: Vec<BigInt>,
    pub b_i128: Vec<i128>,
    /// Per attempt: the pack-time exact bound (audit artifact — a lane
    /// audit re-checks admission from the packed batch alone).
    pub bound: Vec<BigInt>,
    /// Per attempt: the `i128` lane may run (bound < 2^126).
    pub small_ok: Vec<bool>,
}

impl ConstFoldBatch {
    pub fn new(systems: Vec<ConstSystem>) -> ConstFoldBatch {
        ConstFoldBatch {
            systems,
            y_ptr: vec![0],
            ..Default::default()
        }
    }

    pub fn n_attempts(&self) -> usize {
        self.attempt_sys.len()
    }

    /// Pack one attempt: a DENSE coefficient vector over the system's
    /// places (zeros dropped here) plus the claimed charge rhs. The
    /// admission bound is `Σ_supp |y_p|·row_abs[p]` plus
    /// `Σ_supp |y_p·m0_p|` plus `|b|` — every partial sum of every
    /// row, in either fold order, is bounded by it.
    pub fn push_attempt(&mut self, sys: u32, y: &[BigInt], b: &BigInt) {
        let s = &self.systems[sys as usize];
        assert_eq!(y.len(), s.n_places as usize, "dense y over places");
        let mut bound = BigInt::ZERO;
        let base = self.y_val.len();
        for (p, yp) in y.iter().enumerate() {
            if yp.is_zero() {
                continue;
            }
            let abs = yp.magnitude();
            bound += BigInt::from(abs.clone()) * BigInt::from(s.row_abs[p]);
            if s.m0[p] != 0 {
                bound += BigInt::from(abs.clone()) * BigInt::from(s.m0[p].unsigned_abs());
            }
            self.y_place.push(p as u32);
            self.y_val.push(yp.clone());
        }
        bound += BigInt::from(b.magnitude().clone());
        let small_ok = bound < (BigInt::from(1u8) << 126);
        for k in base..self.y_val.len() {
            let p = self.y_place[k] as usize;
            // Not-admitted attempts and fold-irrelevant support (no
            // leaves, zero m0 — see field docs) both image to 0.
            self.y_i128
                .push(if !small_ok || (s.row_abs[p] == 0 && s.m0[p] == 0) {
                    0
                } else {
                    i128::try_from(&self.y_val[k])
                        .expect("|y_p| <= |y_p|*max(row_abs,|m0|) <= bound < 2^126")
                });
        }
        self.b_i128.push(if small_ok {
            i128::try_from(b).expect("|b| <= bound < 2^126")
        } else {
            0
        });
        self.b_val.push(b.clone());
        self.bound.push(bound);
        self.small_ok.push(small_ok);
        self.attempt_sys.push(sys);
        self.y_ptr.push(self.y_val.len() as u32);
    }
}

/// Batch verdicts. `ok[a]` ⟺ every conservation row of attempt `a`
/// folds to zero AND the charge row folds to `b_a`. `first_bad[a]` is
/// the least failing row index (`n_cols` = the charge row, [`NONE`] =
/// none) — a diagnostic, deterministic across lanes and paths.
/// `used_big[a]` marks attempts folded in exact arithmetic (admission
/// refusal in the production lane; every attempt in the reference
/// lane). `scatter_attempts` counts the cost-path choice (diagnostic).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstFoldOutcome {
    pub ok: Vec<bool>,
    pub used_big: Vec<bool>,
    pub first_bad: Vec<u32>,
    pub scatter_attempts: u64,
}

/// Cost-path policy for the `i128` lane — verdict-neutral by the lane
/// law; the forced variants exist so tests assert that instead of
/// assuming it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathPolicy {
    /// Scatter when the support-joined workload is under half the
    /// column-major workload (the measured census heuristic:
    /// support-pruning beat every lane choice on sparse-support nets).
    Auto,
    ColumnOnly,
    ScatterOnly,
}

/// Reusable scratch, sized to the batch's largest system once.
struct Scratch {
    /// place → support slot (sentinel [`NONE`]); cleared by support.
    supp_at: Vec<u32>,
    /// scatter accumulators + epoch stamps over columns.
    acc: Vec<i128>,
    stamp: Vec<u32>,
    epoch: u32,
}

impl Scratch {
    fn new(batch: &ConstFoldBatch) -> Scratch {
        let np = batch.systems.iter().map(|s| s.n_places).max().unwrap_or(0);
        let nc = batch.systems.iter().map(|s| s.n_cols).max().unwrap_or(0);
        Scratch {
            supp_at: vec![NONE; np as usize],
            acc: vec![0; nc as usize],
            stamp: vec![0; nc as usize],
            epoch: 0,
        }
    }
}

/// The production lane: `i128` where admitted (path per policy),
/// exact `BigInt` fallback otherwise. Verdict-identical to
/// [`verify_batch_big`] by construction and by battery.
pub fn verify_batch_with(batch: &ConstFoldBatch, policy: PathPolicy) -> ConstFoldOutcome {
    let n = batch.n_attempts();
    let mut out = ConstFoldOutcome {
        ok: Vec::with_capacity(n),
        used_big: Vec::with_capacity(n),
        first_bad: Vec::with_capacity(n),
        scatter_attempts: 0,
    };
    let mut scr = Scratch::new(batch);
    for a in 0..n {
        let s = &batch.systems[batch.attempt_sys[a] as usize];
        let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
        let first_bad = if batch.small_ok[a] {
            // Path choice: support-joined nnz vs whole-plane leaves.
            let supp_nnz: u64 = (lo..hi)
                .map(|k| {
                    let p = batch.y_place[k] as usize;
                    (s.row_ptr[p + 1] - s.row_ptr[p]) as u64
                })
                .sum();
            let scatter = match policy {
                PathPolicy::Auto => supp_nnz * 2 < s.n_leaves() as u64,
                PathPolicy::ColumnOnly => false,
                PathPolicy::ScatterOnly => true,
            };
            if scatter {
                out.scatter_attempts += 1;
                fold_scatter_i128(batch, a, s, &mut scr)
            } else {
                fold_columns_i128(batch, a, s, &mut scr)
            }
        } else {
            fold_columns_big(batch, a, s, &mut scr)
        };
        out.used_big.push(!batch.small_ok[a]);
        out.ok.push(first_bad == NONE);
        out.first_bad.push(first_bad);
    }
    out
}

/// The production lane at the default policy.
pub fn verify_batch(batch: &ConstFoldBatch) -> ConstFoldOutcome {
    verify_batch_with(batch, PathPolicy::Auto)
}

/// The exact reference lane: `BigInt`, column-major, every attempt.
pub fn verify_batch_big(batch: &ConstFoldBatch) -> ConstFoldOutcome {
    let n = batch.n_attempts();
    let mut out = ConstFoldOutcome {
        ok: Vec::with_capacity(n),
        used_big: vec![true; n],
        first_bad: Vec::with_capacity(n),
        scatter_attempts: 0,
    };
    let mut scr = Scratch::new(batch);
    for a in 0..n {
        let s = &batch.systems[batch.attempt_sys[a] as usize];
        let first_bad = fold_columns_big(batch, a, s, &mut scr);
        out.ok.push(first_bad == NONE);
        out.first_bad.push(first_bad);
    }
    out
}

/// Support map fill/clear discipline shared by the folds.
fn with_support<R>(
    batch: &ConstFoldBatch,
    a: usize,
    scr: &mut Scratch,
    f: impl FnOnce(&ConstFoldBatch, &mut Scratch) -> R,
) -> R {
    let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
    for k in lo..hi {
        scr.supp_at[batch.y_place[k] as usize] = k as u32;
    }
    let r = f(batch, scr);
    for k in lo..hi {
        scr.supp_at[batch.y_place[k] as usize] = NONE;
    }
    r
}

/// Charge row in `i128` (admitted attempts): Σ_supp y_p·m0_p == b.
fn charge_ok_i128(batch: &ConstFoldBatch, a: usize, s: &ConstSystem) -> bool {
    let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
    let mut acc: i128 = 0;
    for k in lo..hi {
        let m = s.m0[batch.y_place[k] as usize];
        if m != 0 {
            acc += batch.y_i128[k] * m as i128;
        }
    }
    acc == batch.b_i128[a]
}

fn fold_columns_i128(batch: &ConstFoldBatch, a: usize, s: &ConstSystem, scr: &mut Scratch) -> u32 {
    let bad = with_support(batch, a, scr, |batch, scr| {
        for t in 0..s.n_cols as usize {
            let mut acc: i128 = 0;
            for i in s.col_ptr[t] as usize..s.col_ptr[t + 1] as usize {
                let at = scr.supp_at[s.leaf_place[i] as usize];
                if at != NONE {
                    acc += batch.y_i128[at as usize] * s.leaf_w[i] as i128;
                }
            }
            if acc != 0 {
                return t as u32;
            }
        }
        NONE
    });
    if bad != NONE {
        return bad;
    }
    if charge_ok_i128(batch, a, s) {
        NONE
    } else {
        s.n_cols
    }
}

fn fold_scatter_i128(batch: &ConstFoldBatch, a: usize, s: &ConstSystem, scr: &mut Scratch) -> u32 {
    let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
    scr.epoch += 1;
    let epoch = scr.epoch;
    let mut touched: Vec<u32> = Vec::new();
    for k in lo..hi {
        let p = batch.y_place[k] as usize;
        let yv = batch.y_i128[k];
        for j in s.row_ptr[p] as usize..s.row_ptr[p + 1] as usize {
            let c = s.row_col[j] as usize;
            if scr.stamp[c] != epoch {
                scr.stamp[c] = epoch;
                scr.acc[c] = 0;
                touched.push(c as u32);
            }
            scr.acc[c] += yv * s.row_w[j] as i128;
        }
    }
    touched.sort_unstable();
    for &c in &touched {
        if scr.acc[c as usize] != 0 {
            return c;
        }
    }
    if charge_ok_i128(batch, a, s) {
        NONE
    } else {
        s.n_cols
    }
}

fn fold_columns_big(batch: &ConstFoldBatch, a: usize, s: &ConstSystem, scr: &mut Scratch) -> u32 {
    let bad = with_support(batch, a, scr, |batch, scr| {
        for t in 0..s.n_cols as usize {
            let mut acc = BigInt::ZERO;
            for i in s.col_ptr[t] as usize..s.col_ptr[t + 1] as usize {
                let at = scr.supp_at[s.leaf_place[i] as usize];
                if at != NONE {
                    acc += &batch.y_val[at as usize] * BigInt::from(s.leaf_w[i]);
                }
            }
            if !acc.is_zero() {
                return t as u32;
            }
        }
        NONE
    });
    if bad != NONE {
        return bad;
    }
    let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
    let mut acc = BigInt::ZERO;
    for k in lo..hi {
        let m = s.m0[batch.y_place[k] as usize];
        if m != 0 {
            acc += &batch.y_val[k] * BigInt::from(m);
        }
    }
    if acc == batch.b_val[a] {
        NONE
    } else {
        s.n_cols
    }
}

/// Single-row exact replay (the conformance sampler's hook): the
/// verdict of row `col` of `attempt`, always in exact arithmetic.
/// `col == n_cols` is the charge row.
pub fn row_verdict(batch: &ConstFoldBatch, attempt: u32, col: u32) -> bool {
    let a = attempt as usize;
    let s = &batch.systems[batch.attempt_sys[a] as usize];
    let (lo, hi) = (batch.y_ptr[a] as usize, batch.y_ptr[a + 1] as usize);
    let y_of = |place: u32| -> Option<&BigInt> {
        let supp = &batch.y_place[lo..hi];
        supp.binary_search(&place)
            .ok()
            .map(|k| &batch.y_val[lo + k])
    };
    assert!(col <= s.n_cols, "row index in range (n_cols = charge)");
    if col == s.n_cols {
        let mut acc = BigInt::ZERO;
        for k in lo..hi {
            let m = s.m0[batch.y_place[k] as usize];
            if m != 0 {
                acc += &batch.y_val[k] * BigInt::from(m);
            }
        }
        return acc == batch.b_val[a];
    }
    let mut acc = BigInt::ZERO;
    for i in s.col_ptr[col as usize] as usize..s.col_ptr[col as usize + 1] as usize {
        if let Some(yv) = y_of(s.leaf_place[i]) {
            acc += yv * BigInt::from(s.leaf_w[i]);
        }
    }
    acc.is_zero()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny hand-checked system: 3 places, 2 transitions.
    /// t0: p0 −1, p1 +1;  t1: p1 −1, p2 +1.  m0 = [2, 0, 0].
    /// y = (1,1,1) is a P-invariant with charge 2.
    fn tiny() -> ConstSystem {
        ConstSystem::from_leaves(
            3,
            2,
            &[(0, 0, -1), (0, 1, 1), (1, 1, -1), (1, 2, 1)],
            vec![2, 0, 0],
        )
    }

    #[test]
    fn tiny_invariant_and_mutant() {
        let mut b = ConstFoldBatch::new(vec![tiny()]);
        let one = BigInt::from(1);
        b.push_attempt(
            0,
            &[one.clone(), one.clone(), one.clone()],
            &BigInt::from(2),
        );
        // Mutant: y0+1 breaks t0; charge recomputed so it holds.
        b.push_attempt(
            0,
            &[BigInt::from(2), one.clone(), one.clone()],
            &BigInt::from(4),
        );
        // Wrong charge only.
        b.push_attempt(0, &[one.clone(), one.clone(), one], &BigInt::from(3));
        for policy in [
            PathPolicy::Auto,
            PathPolicy::ColumnOnly,
            PathPolicy::ScatterOnly,
        ] {
            let out = verify_batch_with(&b, policy);
            assert_eq!(out.ok, vec![true, false, false], "{policy:?}");
            assert_eq!(out.first_bad, vec![NONE, 0, 2], "{policy:?}");
        }
        let big = verify_batch_big(&b);
        assert_eq!(big.ok, vec![true, false, false]);
        assert_eq!(big.first_bad, vec![NONE, 0, 2]);
        // Row grain agrees.
        assert!(row_verdict(&b, 0, 0) && row_verdict(&b, 0, 1) && row_verdict(&b, 0, 2));
        assert!(!row_verdict(&b, 1, 0) && row_verdict(&b, 1, 2));
        assert!(row_verdict(&b, 2, 0) && row_verdict(&b, 2, 1) && !row_verdict(&b, 2, 2));
    }

    #[test]
    fn admission_refusal_routes_exact() {
        let mut b = ConstFoldBatch::new(vec![tiny()]);
        let huge: BigInt = BigInt::from(1u8) << 124;
        let y: Vec<BigInt> = vec![huge.clone(), huge.clone(), huge.clone()];
        b.push_attempt(0, &y, &(huge * 2));
        // bound = 2^124·(1+2+1) + 2^124·2 (charge terms) + 2^125 = 2^127.
        assert!(!b.small_ok[0], "2^124 coefficients exceed the bound");
        let out = verify_batch(&b);
        assert!(out.used_big[0] && out.ok[0]);
    }

    #[test]
    fn fold_irrelevant_support_is_safe() {
        // Place 3 has no leaves and m0 = 0: its (enormous) coefficient
        // is provably absent from every row; the attempt stays
        // admitted and true.
        let s = ConstSystem::from_leaves(
            4,
            2,
            &[(0, 0, -1), (0, 1, 1), (1, 1, -1), (1, 2, 1)],
            vec![2, 0, 0, 0],
        );
        let mut b = ConstFoldBatch::new(vec![s]);
        let one = BigInt::from(1);
        let huge: BigInt = BigInt::from(1u8) << 200;
        b.push_attempt(0, &[one.clone(), one.clone(), one, huge], &BigInt::from(2));
        assert!(b.small_ok[0], "irrelevant support does not tax the bound");
        let out = verify_batch(&b);
        let big = verify_batch_big(&b);
        assert!(out.ok[0] && big.ok[0]);
    }

    #[test]
    fn empty_support_and_empty_columns() {
        // A system with an empty column; a zero attempt (empty
        // support) holds iff b = 0.
        let s = ConstSystem::from_leaves(2, 3, &[(0, 0, 1), (0, 1, -1)], vec![5, 5]);
        let mut b = ConstFoldBatch::new(vec![s]);
        let zero = BigInt::ZERO;
        b.push_attempt(0, &[zero.clone(), zero.clone()], &BigInt::ZERO);
        b.push_attempt(0, &[zero.clone(), zero], &BigInt::from(1));
        let out = verify_batch(&b);
        assert_eq!(out.ok, vec![true, false]);
        assert_eq!(out.first_bad[1], 3, "only the charge row can fail");
    }
}
