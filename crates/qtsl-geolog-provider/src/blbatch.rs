//! batch tensors for the combination families (first brick).
//!
//! One combination-family instance (Farkas / Syzygy / PBound node)
//! extracts into up to three [`ComboAttempt`]s — one per translation
//! branch of `combination_check` (idx-free core / wire-coordinate /
//! mixed). An attempt is a fully value-resolved tensor: every
//! polynomial is a sparse vector over an attempt-local DENSE monomial
//! column space (interned at extraction; the GPU never sees a monomial
//! key), every coefficient an exact [`QQ`].
//!
//! [`verify_instance`] is the CPU reference implementation of the
//! batch pipeline's verification phase (Phase V) — dense
//! fold-accumulate, entrywise exact equality. It is the
//! kernel successor's executable spec: what a GPU custom call must
//! reproduce, slot for slot. Semantics authority remains the E3
//! evaluator (`blapplic::combination_check`); the `blbatch_diff`
//! differential pins extraction + this verifier against it on the
//! producer fixture corpus.
//!
//! Verdict equivalence argument (why value-only Phase V matches the
//! evaluator's early-exit control flow): the evaluator breaks a branch
//! on the first negative lambda or unmatched vehicle and returns true
//! on the first branch whose fold matches; every such break is a
//! value-dependent FALSE for that branch, and branches are
//! independent, so `any(attempt verdicts)` computes the same result
//! with exact (order-insensitive) arithmetic. Structure-dependent
//! breaks (untranslatable conclusion/vehicle) are attempt-ABSENCE,
//! resolved at extraction.

use crate::qq::QQ;

/// Sparse exact-rational vector in an attempt-local dense column
/// space: (column, coefficient) pairs, columns strictly ascending,
/// coefficients nonzero.
pub type SparseQVec = Vec<(u32, QQ)>;

/// Which translation branch of `combination_check` this attempt
/// mirrors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComboBranch {
    /// Idx-free core (`to_poly`; wire-element variables).
    Core,
    /// G1 wire-coordinate branch (`coord_poly`; `wireCoordKey` vars).
    WireCoord,
    /// Mixed bare/TIdx branch (`mixed_poly`; even/odd tagged vars —
    /// adjudicated sound 2026-07-19; carried as the Lean third branch).
    Mixed,
}

/// One branch's fully value-resolved verification problem.
#[derive(Debug, Clone)]
pub struct ComboAttempt {
    pub branch: ComboBranch,
    /// Dense column-space extent (monomials interned per attempt).
    pub n_monos: u32,
    /// Per entry $i$: the combination coefficient $\lambda_i$.
    pub lambdas: Vec<QQ>,
    /// Per entry $i$: the vehicle's polynomial as a sparse vector.
    pub vehicles: Vec<SparseQVec>,
    /// The candidate pool: premise-derived le-zero polynomials (and
    /// component posts, for the node families). Membership requires
    /// each vehicle to EQUAL some candidate; the candidate set is
    /// entry-independent (mirrors the evaluator: same list scanned
    /// for every entry).
    pub cand_polys: Vec<SparseQVec>,
    /// The conclusion's polynomial.
    pub conclusion: SparseQVec,
}

/// One instance's extraction: the attempts that were structurally
/// reachable. `decided_false` marks the not-the-encoding case
/// (`farkas_entries` → None): verdict false with zero attempts, which
/// `verify_instance` already returns — the flag is diagnostic.
#[derive(Debug, Clone, Default)]
pub struct ComboExtract {
    pub attempts: Vec<ComboAttempt>,
    pub decided_false: bool,
}

/// Reference Phase-V verification of one attempt — the kernel spec.
///
/// (i) every $\lambda_i \ge 0$; (ii) every vehicle equals some
/// candidate (exact sparse equality — canonical forms, so vector
/// equality decides polynomial equality); (iii) the dense fold
/// $F[m] = \sum_i \lambda_i \cdot V_i[m]$ equals the conclusion
/// entrywise.
pub fn verify_attempt(a: &ComboAttempt) -> bool {
    if !a.lambdas.iter().all(QQ::is_nonneg) {
        return false;
    }
    if a.lambdas.len() != a.vehicles.len() {
        return false;
    }
    if !a.vehicles.iter().all(|v| a.cand_polys.contains(v)) {
        return false;
    }
    // Dense fold-accumulate: the GPU-shaped computation (per-column
    // AXPY), executed in reference form.
    let n = a.n_monos as usize;
    let mut fold = vec![QQ::zero(); n];
    for (lam, veh) in a.lambdas.iter().zip(&a.vehicles) {
        for (col, c) in veh {
            let cell = &mut fold[*col as usize];
            *cell = cell.add(&lam.mul(c));
        }
    }
    let mut concl = vec![QQ::zero(); n];
    for (col, c) in &a.conclusion {
        concl[*col as usize] = c.clone();
    }
    fold == concl
}

/// Instance verdict: OR over attempts (branch order irrelevant —
/// exact arithmetic, independent attempts).
pub fn verify_instance(e: &ComboExtract) -> bool {
    e.attempts.iter().any(verify_attempt)
}

/// Batch statistics — the KCAP-tier receipt (which qint capacity tier
/// a corpus needs) and the workload-shape receipt for the kernel
/// successor's sizing.
#[derive(Debug, Clone, Copy, Default)]
pub struct BatchStats {
    pub instances: usize,
    pub attempts: usize,
    pub entries: usize,
    pub candidates: usize,
    pub max_monos: u32,
    /// Max magnitude bit length over every numerator in the batch.
    pub max_num_bits: u64,
    /// Max bit length over every denominator in the batch.
    pub max_den_bits: u64,
}

impl BatchStats {
    pub fn absorb_qq(&mut self, q: &QQ) {
        let (nb, db) = q.bit_widths();
        self.max_num_bits = self.max_num_bits.max(nb);
        self.max_den_bits = self.max_den_bits.max(db);
    }

    pub fn absorb_vec(&mut self, v: &SparseQVec) {
        for (_, q) in v {
            self.absorb_qq(q);
        }
    }

    pub fn absorb(&mut self, e: &ComboExtract) {
        self.instances += 1;
        for a in &e.attempts {
            self.attempts += 1;
            self.entries += a.lambdas.len();
            self.candidates += a.cand_polys.len();
            self.max_monos = self.max_monos.max(a.n_monos);
            for l in &a.lambdas {
                self.absorb_qq(l);
            }
            for v in &a.vehicles {
                self.absorb_vec(v);
            }
            for c in &a.cand_polys {
                self.absorb_vec(c);
            }
            self.absorb_vec(&a.conclusion);
        }
    }

    /// The qint limb tier this batch needs: limbs to hold the larger
    /// of max num/den magnitude (the fold's intermediates ride the
    /// kernels' own 2k scratch + overflow ladder, not this number).
    pub fn input_limb_tier(&self) -> u64 {
        self.max_num_bits.max(self.max_den_bits).div_ceil(64).max(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> QQ {
        QQ::from_int(n)
    }

    fn attempt() -> ComboAttempt {
        // lambdas (1, 2); vehicles x+1 and 2x (columns: 0 = x, 1 = 1);
        // conclusion 1*(x+1) + 2*(2x) = 5x + 1.
        ComboAttempt {
            branch: ComboBranch::Core,
            n_monos: 2,
            lambdas: vec![q(1), q(2)],
            vehicles: vec![vec![(0, q(1)), (1, q(1))], vec![(0, q(2))]],
            cand_polys: vec![vec![(0, q(1)), (1, q(1))], vec![(0, q(2))]],
            conclusion: vec![(0, q(5)), (1, q(1))],
        }
    }

    #[test]
    fn reference_attempt_accepts() {
        assert!(verify_attempt(&attempt()));
    }

    #[test]
    fn mutants_flip() {
        // λ-sign flip.
        let mut a = attempt();
        a.lambdas[1] = q(-2);
        assert!(!verify_attempt(&a));
        // Coefficient perturbation breaks membership.
        let mut a = attempt();
        a.vehicles[0][0].1 = q(3);
        assert!(!verify_attempt(&a));
        // Membership intact but conclusion perturbed breaks the fold.
        let mut a = attempt();
        a.conclusion[0].1 = q(4);
        assert!(!verify_attempt(&a));
    }

    #[test]
    fn instance_or_semantics() {
        let good = attempt();
        let mut bad = attempt();
        bad.conclusion[0].1 = q(4);
        let e = ComboExtract {
            attempts: vec![bad, good],
            decided_false: false,
        };
        assert!(verify_instance(&e));
        let none = ComboExtract {
            attempts: vec![],
            decided_false: true,
        };
        assert!(!verify_instance(&none));
    }

    #[test]
    fn stats_receipt() {
        let mut s = BatchStats::default();
        let e = ComboExtract {
            attempts: vec![attempt()],
            decided_false: false,
        };
        s.absorb(&e);
        assert_eq!(s.instances, 1);
        assert_eq!(s.entries, 2);
        assert_eq!(s.input_limb_tier(), 1);
    }
}
