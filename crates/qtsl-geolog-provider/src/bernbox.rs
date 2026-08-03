//! Tensor-product Bernstein nonnegativity over rational boxes, plus
//! the whole-space sign fragment — the exact-ℚ discharge core of the
//! colored-feature footprint tier.
//!
//! Two quantification domains, two verdict shapes:
//!
//! - [`whole_space_sign`]: sign of a polynomial over ALL of ℚ^w — the
//!   fragment the evaluators can reach TODAY, because the consumed-side
//!   color domain (guard slab / plate color box) has no relational
//!   home at the current staging (findings F-1: the branch image
//!   encloses the produced side only). Sound both ways on the
//!   decidable shapes (constants; single-signed even-monomial
//!   combinations), `Unknown` elsewhere — the caller refuses, naming
//!   the missing stratum.
//! - [`box_sign`]: Bernstein-coefficient nonnegativity over a closed
//!   rational box (sound, incomplete at the polynomial's own
//!   multidegree — no subdivision, no degree elevation this leg), with
//!   vertex/center witnesses for the negative direction (a witness
//!   point lies IN the box, so ∃-failure is sound). Written and
//!   mutant-tested now; wired to row bytes by the box-staging
//!   successor, and reachable today from the param-conformance range
//!   checks wherever a box is ever staged.
//!
//! Everything exact ℚ ([`crate::qq::QQ`] / [`crate::qpoly::QPoly`]);
//! no floats representable.

use crate::qpoly::{Mono, QPoly};
use crate::qq::QQ;
use num_bigint::{BigInt, BigUint};
use std::collections::BTreeMap;

/// Sign classification over the whole space ℚ^w.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpaceSign {
    /// `p(x) ≥ 0` for every rational `x` (certified).
    Nonneg,
    /// `p(x) < 0` for every rational `x` (certified).
    Neg,
    /// Not sign-decidable in this fragment.
    Unknown,
}

/// Sign of `p` over all of ℚ^w, on the decidable shapes: a constant
/// decides by its sign; a polynomial whose non-constant monomials are
/// all even-exponent and single-signed decides when the constant term
/// agrees (`c ≥ 0` + positive even terms ⟹ Nonneg; `c < 0` + negative
/// even terms ⟹ Neg). Everything else is `Unknown` — including mixed
/// even signs and any odd-exponent monomial.
pub fn whole_space_sign(p: &QPoly) -> SpaceSign {
    let mut constant = QQ::zero();
    let mut any_pos_even = false;
    let mut any_neg_even = false;
    for (m, c) in &p.0 {
        if m.is_empty() {
            constant = c.clone();
            continue;
        }
        if m.iter().any(|(_, e)| e % 2 == 1) {
            return SpaceSign::Unknown;
        }
        // Canonical polynomials carry no zero coefficients.
        if c.is_nonneg() {
            any_pos_even = true;
        } else {
            any_neg_even = true;
        }
    }
    let c_nonneg = constant.is_nonneg();
    match (any_pos_even, any_neg_even) {
        (false, false) => {
            if c_nonneg {
                SpaceSign::Nonneg
            } else {
                SpaceSign::Neg
            }
        }
        (true, false) => {
            if c_nonneg {
                SpaceSign::Nonneg
            } else {
                SpaceSign::Unknown
            }
        }
        (false, true) => {
            if c_nonneg {
                SpaceSign::Unknown
            } else {
                SpaceSign::Neg
            }
        }
        (true, true) => SpaceSign::Unknown,
    }
}

/// Sign classification over a box.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoxSign {
    /// Every degree-`d` Bernstein coefficient is ≥ 0: `p ≥ 0` on the
    /// box (certified; `d` = the polynomial's own multidegree).
    NonnegCertified,
    /// An in-box witness (vertex or center) evaluates `p` below zero.
    NegWitness,
    /// Neither certificate at this degree — the caller refuses (the
    /// family's fail-closed posture), never guesses.
    Unknown,
}

/// Budget cap on the dense coefficient grid (∏(dᵢ+1)) and the vertex
/// sweep (2^k); beyond it the check errs (refusal, never divergence).
pub const BERNBOX_MAX_GRID: usize = 1 << 16;

fn binom(n: u64, k: u64) -> BigUint {
    if k > n {
        return BigUint::from(0u8);
    }
    let k = k.min(n - k);
    let mut acc = BigUint::from(1u8);
    for i in 0..k {
        acc = acc * BigUint::from(n - i) / BigUint::from(i + 1);
    }
    acc
}

fn q_from_biguint(n: &BigUint) -> QQ {
    QQ::new(BigInt::from(n.clone()), BigUint::from(1u8))
}

/// Exact evaluation of `p` at a rational point (total on any point
/// whose length covers the polynomial's variables).
fn eval_at(p: &QPoly, x: &[QQ]) -> QQ {
    let mut acc = QQ::zero();
    for (m, c) in &p.0 {
        let mut term = c.clone();
        for (v, e) in m {
            let xv = &x[*v as usize];
            for _ in 0..*e {
                term = term.mul(xv);
            }
        }
        acc = acc.add(&term);
    }
    acc
}

/// Per-variable degrees of `p` over `w` variables.
fn multidegree(p: &QPoly, w: usize) -> Vec<u32> {
    let mut d = vec![0u32; w];
    for m in p.0.keys() {
        for (v, e) in m {
            let v = *v as usize;
            if d[v] < *e {
                d[v] = *e;
            }
        }
    }
    d
}

/// Strict-sign classification over a box (the [`box_sign_strict`]
/// verdict shape — the angelic support facet's reading).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrictBoxSign {
    /// Every degree-`d` Bernstein coefficient is `> 0`: `p > 0` on the
    /// box (certified — the Bernstein basis is a partition of unity of
    /// nonnegative functions, so `p ≥ min b_α > 0` pointwise).
    PosCertified,
    /// An in-box witness (vertex or center) evaluates `p ≤ 0` — sound
    /// against strict positivity, the witness point lies IN the box.
    NonposWitness,
    /// Neither certificate at this degree — the caller refuses (the
    /// family's fail-closed posture), never guesses.
    Unknown,
}

/// The shared sampled-point + Bernstein-coefficient scan behind
/// [`box_sign`] and [`box_sign_strict`]: one vertex/center sweep, one
/// affine pull, one coefficient grid — two verdict readings.
struct BoxScan {
    /// A sampled point (vertex or center) evaluated `< 0`.
    sampled_neg: bool,
    /// A sampled point evaluated exactly `0`.
    sampled_zero: bool,
    /// Every Bernstein coefficient `≥ 0`. (Meaningless when
    /// `sampled_neg` — the grid is skipped; both callers verdict on
    /// the witness alone.)
    coeffs_nonneg: bool,
    /// Every Bernstein coefficient `> 0` (same caveat).
    coeffs_pos: bool,
}

/// Sign of `p` over the closed box `dom` (one `(lo, hi)` pair per
/// variable, `lo ≤ hi`). Errs (caller refuses) on: a variable of `p`
/// outside `dom`'s width, a reversed interval, or a grid/vertex sweep
/// beyond [`BERNBOX_MAX_GRID`].
pub fn box_sign(p: &QPoly, dom: &[(QQ, QQ)]) -> Result<BoxSign, String> {
    let s = box_scan(p, dom)?;
    if s.sampled_neg {
        return Ok(BoxSign::NegWitness);
    }
    if s.coeffs_nonneg {
        Ok(BoxSign::NonnegCertified)
    } else {
        Ok(BoxSign::Unknown)
    }
}

/// STRICT sign of `p` over the closed box `dom` — the reading the
/// angelic enabled facet consumes (`dom ⊆ {p > 0}` demands strict
/// positivity on a closed box). Sound on both decided arms, incomplete
/// at the polynomial's own multidegree (no subdivision, no degree
/// elevation — the same incompleteness class as [`box_sign`]); same
/// refusal surface (width, inverted intervals, budgets).
pub fn box_sign_strict(p: &QPoly, dom: &[(QQ, QQ)]) -> Result<StrictBoxSign, String> {
    let s = box_scan(p, dom)?;
    if s.sampled_neg || s.sampled_zero {
        return Ok(StrictBoxSign::NonposWitness);
    }
    if s.coeffs_pos {
        Ok(StrictBoxSign::PosCertified)
    } else {
        Ok(StrictBoxSign::Unknown)
    }
}

fn box_scan(p: &QPoly, dom: &[(QQ, QQ)]) -> Result<BoxScan, String> {
    let w = dom.len();
    for m in p.0.keys() {
        for (v, _) in m {
            if *v as usize >= w {
                return Err(format!(
                    "polynomial reads color coordinate {v} beyond the box width {w}"
                ));
            }
        }
    }
    for (lo, hi) in dom {
        if lo.cmp_qq(hi) == std::cmp::Ordering::Greater {
            return Err("reversed interval (lo > hi) — malformed box".into());
        }
    }
    // --- sampled witnesses: vertices + center, exact -------------------
    if w > 0 && (1usize << w.min(63)) > BERNBOX_MAX_GRID {
        return Err("vertex sweep beyond the bernbox budget".into());
    }
    let mut sampled_neg = false;
    let mut sampled_zero = false;
    let n_vertices = 1usize << w;
    for mask in 0..n_vertices {
        let x: Vec<QQ> = (0..w)
            .map(|i| {
                if mask >> i & 1 == 1 {
                    dom[i].1.clone()
                } else {
                    dom[i].0.clone()
                }
            })
            .collect();
        let v = eval_at(p, &x);
        if v.is_zero() {
            sampled_zero = true;
        } else if !v.is_nonneg() {
            sampled_neg = true;
            break;
        }
    }
    if !sampled_neg {
        let half = QQ::new(BigInt::from(1), BigUint::from(2u8));
        let center: Vec<QQ> = dom.iter().map(|(lo, hi)| lo.add(hi).mul(&half)).collect();
        let v = eval_at(p, &center);
        if v.is_zero() {
            sampled_zero = true;
        } else if !v.is_nonneg() {
            sampled_neg = true;
        }
    }
    if sampled_neg {
        // The grid is skipped: both callers verdict on the witness.
        return Ok(BoxScan {
            sampled_neg,
            sampled_zero,
            coeffs_nonneg: false,
            coeffs_pos: false,
        });
    }
    // --- Bernstein certificate over [0,1]^w after the affine pull -----
    // x_i = lo_i + (hi_i − lo_i)·t_i, exact.
    let mut q = p.clone();
    for (i, (lo, hi)) in dom.iter().enumerate() {
        let width = hi.sub(lo);
        // substitute x_i := lo + width·t_i by monomial expansion.
        let mut out = QPoly::zero();
        let sub = QPoly::constant(lo.clone()).add(&QPoly::var(i as u64).scale(&width));
        for (m, c) in &q.0 {
            match m.iter().position(|(mv, _)| *mv == i as u64) {
                None => {
                    out = out.add(&QPoly(BTreeMap::from([(m.clone(), c.clone())])));
                }
                Some(pos) => {
                    let e = m[pos].1;
                    let mut rest = m.clone();
                    rest.remove(pos);
                    let mut pow = QPoly::constant(QQ::one());
                    for _ in 0..e {
                        pow = pow.mul(&sub);
                        if pow.0.len() > BERNBOX_MAX_GRID {
                            return Err("affine pull beyond the bernbox budget".into());
                        }
                    }
                    let base = QPoly(BTreeMap::from([(rest, c.clone())]));
                    out = out.add(&base.mul(&pow));
                }
            }
            if out.0.len() > BERNBOX_MAX_GRID {
                return Err("affine pull beyond the bernbox budget".into());
            }
        }
        q = out;
    }
    let d = multidegree(&q, w);
    let grid: usize = d
        .iter()
        .try_fold(1usize, |acc, di| {
            acc.checked_mul(*di as usize + 1)
                .filter(|g| *g <= BERNBOX_MAX_GRID)
                .ok_or(())
        })
        .map_err(|_| "coefficient grid beyond the bernbox budget".to_string())?;
    // Dense power-basis coefficients a_β, β ≤ d (mixed-radix index).
    let strides: Vec<usize> = {
        let mut s = vec![0usize; w];
        let mut acc = 1usize;
        for i in 0..w {
            s[i] = acc;
            acc *= d[i] as usize + 1;
        }
        s
    };
    let flat = |m: &Mono| -> usize {
        m.iter()
            .map(|(v, e)| strides[*v as usize] * *e as usize)
            .sum()
    };
    let mut a: Vec<QQ> = vec![QQ::zero(); grid.max(1)];
    for (m, c) in &q.0 {
        a[flat(m)] = c.clone();
    }
    // b_α = Σ_{β ≤ α} Π_i [C(α_i, β_i)/C(d_i, β_i)] a_β; all ≥ 0 ⟹
    // q ≥ 0 on [0,1]^w. Iterate α over the grid; β over its lower set.
    let decode = |mut ix: usize| -> Vec<u32> {
        let mut alpha = vec![0u32; w];
        for i in 0..w {
            alpha[i] = (ix % (d[i] as usize + 1)) as u32;
            ix /= d[i] as usize + 1;
        }
        alpha
    };
    let mut coeffs_nonneg = true;
    let mut coeffs_pos = true;
    for aix in 0..grid.max(1) {
        let alpha = decode(aix);
        let mut b = QQ::zero();
        // enumerate β ≤ α by mixed radix over (α_i + 1).
        let sub_grid: usize = alpha.iter().map(|ai| *ai as usize + 1).product();
        for bix in 0..sub_grid {
            let mut rem = bix;
            let mut coeff = QQ::one();
            let mut flat_b = 0usize;
            for i in 0..w {
                let beta_i = (rem % (alpha[i] as usize + 1)) as u64;
                rem /= alpha[i] as usize + 1;
                flat_b += strides[i] * beta_i as usize;
                let num = binom(alpha[i] as u64, beta_i);
                // den ≥ 1 always: β_i ≤ α_i ≤ d_i.
                let den = binom(d[i] as u64, beta_i);
                coeff = coeff.mul(&q_from_biguint(&num));
                coeff = coeff.mul(&QQ::new(BigInt::from(1), den));
            }
            if a[flat_b].is_zero() {
                continue;
            }
            b = b.add(&coeff.mul(&a[flat_b]));
        }
        if b.is_zero() {
            coeffs_pos = false;
        } else if !b.is_nonneg() {
            coeffs_nonneg = false;
            coeffs_pos = false;
            break; // nothing further changes either caller's verdict
        }
    }
    Ok(BoxScan {
        sampled_neg,
        sampled_zero,
        coeffs_nonneg,
        coeffs_pos,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn iv(lo: i64, hi: i64) -> (QQ, QQ) {
        (q(lo, 1), q(hi, 1))
    }

    #[test]
    fn whole_space_shapes() {
        // constants decide both ways
        assert_eq!(
            whole_space_sign(&QPoly::constant(q(0, 1))),
            SpaceSign::Nonneg
        );
        assert_eq!(
            whole_space_sign(&QPoly::constant(q(3, 7))),
            SpaceSign::Nonneg
        );
        assert_eq!(whole_space_sign(&QPoly::constant(q(-1, 2))), SpaceSign::Neg);
        // w² + 1 ≥ 0 everywhere; −w² − 1 < 0 everywhere
        let w2 = QPoly::var(0).mul(&QPoly::var(0));
        let p = w2.add(&QPoly::constant(q(1, 1)));
        assert_eq!(whole_space_sign(&p), SpaceSign::Nonneg);
        assert_eq!(whole_space_sign(&p.neg()), SpaceSign::Neg);
        // bare w² (zero constant) is still nonneg
        assert_eq!(whole_space_sign(&w2), SpaceSign::Nonneg);
        // odd monomial: unknown, both signs
        let w = QPoly::var(0);
        assert_eq!(whole_space_sign(&w), SpaceSign::Unknown);
        assert_eq!(
            whole_space_sign(&w.add(&QPoly::constant(q(5, 1)))),
            SpaceSign::Unknown
        );
        // w² − 1: even but constant disagrees — unknown
        assert_eq!(
            whole_space_sign(&w2.sub(&QPoly::constant(q(1, 1)))),
            SpaceSign::Unknown
        );
        // mixed even signs: w² − v²
        let v2 = QPoly::var(1).mul(&QPoly::var(1));
        assert_eq!(whole_space_sign(&w2.sub(&v2)), SpaceSign::Unknown);
    }

    /// The Minifab congestion tick's φ-space displacement: 2w + 2R − 2
    /// over w ∈ [1, T] (R = 0 at the last station — the guarded case).
    /// Degree ≤ 2 over a box, Minifab-shaped.
    #[test]
    fn congestion_tick_holds_on_guard_box() {
        // D = 2w − 2 over [1, 10]: Bernstein coeffs (2·1−2, 2·10−2)/…
        let d = QPoly::var(0).scale(&q(2, 1)).sub(&QPoly::constant(q(2, 1)));
        assert_eq!(
            box_sign(&d, &[iv(1, 10)]).unwrap(),
            BoxSign::NonnegCertified
        );
        // The box-widening mutant: [0, 10] re-admits w = 0 where the
        // sequent fails — the vertex witness catches it.
        assert_eq!(box_sign(&d, &[iv(0, 10)]).unwrap(), BoxSign::NegWitness);
    }

    /// A degree-2 Minifab-shaped sequent: (w+R)² − (w−1+R)² − 1 =
    /// 2w + 2R − 3 over the guard box, R = 5: holds on [1, 10]; the
    /// coefficient-sign flip fails at a vertex.
    #[test]
    fn degree_two_phi_space_row() {
        let r = q(5, 1);
        let w = QPoly::var(0);
        let f = w.add(&QPoly::constant(r.clone())); // w + R
        let fr = f.sub(&QPoly::constant(q(1, 1))); // (w−1) + R
        let d = f.mul(&f).sub(&fr.mul(&fr)).sub(&QPoly::constant(q(1, 1)));
        assert_eq!(
            box_sign(&d, &[iv(1, 10)]).unwrap(),
            BoxSign::NonnegCertified
        );
        // an everywhere-negative-on-the-box displacement is witnessed
        // at a vertex, exactly.
        let neg = d.neg().sub(&QPoly::constant(q(2, 1)));
        assert_eq!(box_sign(&neg, &[iv(1, 10)]).unwrap(), BoxSign::NegWitness);
    }

    /// Bernstein incompleteness is Unknown, never a guess: t·(1−t)
    /// − 1/5 on [0,1] dips negative strictly inside… actually pick a
    /// polynomial nonneg on the box whose degree-d Bernstein
    /// coefficients still go negative: t² − t + 1/4 = (t − 1/2)² ≥ 0,
    /// b = (1/4, −1/4, 1/4) at d = 2 — certified only by elevation,
    /// which this leg deliberately lacks; and its center evaluation is
    /// exactly 0, so no witness fires either.
    #[test]
    fn bernstein_incompleteness_is_unknown() {
        let t = QPoly::var(0);
        let p = t.mul(&t).sub(&t).add(&QPoly::constant(q(1, 4)));
        assert_eq!(box_sign(&p, &[iv(0, 1)]).unwrap(), BoxSign::Unknown);
    }

    /// Two-variable tensor product: w² + v² certifies on [0,1]²; on
    /// [−1,1]² the same polynomial is nonneg yet NOT degree-(2,2)
    /// certifiable (the (2t−1)² negative-middle-coefficient fact, in
    /// two variables) — Unknown, honestly; and w + v over [−1,1]² has
    /// the (−1,−1) vertex witness.
    #[test]
    fn two_variable_boxes() {
        let w = QPoly::var(0);
        let v = QPoly::var(1);
        let p = w.mul(&w).add(&v.mul(&v));
        assert_eq!(
            box_sign(&p, &[iv(0, 1), iv(0, 1)]).unwrap(),
            BoxSign::NonnegCertified
        );
        assert_eq!(
            box_sign(&p, &[iv(-1, 1), iv(-1, 1)]).unwrap(),
            BoxSign::Unknown
        );
        assert_eq!(
            box_sign(&w.add(&v), &[iv(-1, 1), iv(-1, 1)]).unwrap(),
            BoxSign::NegWitness
        );
        // and on the positive quadrant box the same poly certifies
        assert_eq!(
            box_sign(&w.add(&v), &[iv(0, 1), iv(0, 1)]).unwrap(),
            BoxSign::NonnegCertified
        );
    }

    /// Refusal shapes err (caller refuses): variable beyond the box
    /// width; reversed interval.
    #[test]
    fn malformed_inputs_err() {
        let v9 = QPoly::var(9);
        assert!(box_sign(&v9, &[iv(0, 1)]).is_err());
        let w = QPoly::var(0);
        assert!(box_sign(&w, &[iv(1, 0)]).is_err());
        // The strict reading shares the refusal surface.
        assert!(box_sign_strict(&v9, &[iv(0, 1)]).is_err());
        assert!(box_sign_strict(&w, &[iv(1, 0)]).is_err());
    }

    /// Strict positivity certifies where every Bernstein coefficient
    /// is strictly positive (constants; an affine form bounded away
    /// from zero on the box).
    #[test]
    fn strict_positive_certified() {
        assert_eq!(
            box_sign_strict(&QPoly::constant(q(1, 1)), &[iv(0, 2)]).unwrap(),
            StrictBoxSign::PosCertified
        );
        // x + 1 on [0, 2]: pulled coefficients 1 and 3.
        let p = QPoly::var(0).add(&QPoly::constant(q(1, 1)));
        assert_eq!(
            box_sign_strict(&p, &[iv(0, 2)]).unwrap(),
            StrictBoxSign::PosCertified
        );
    }

    /// A boundary ZERO is a nonpositivity witness for the strict
    /// reading while the nonneg reading stays certified on the same
    /// bytes — the two verdicts split exactly at `p(x) = 0`, `x` in
    /// the box.
    #[test]
    fn strict_zero_witness_splits_the_readings() {
        let x = QPoly::var(0);
        assert_eq!(
            box_sign_strict(&x, &[iv(0, 2)]).unwrap(),
            StrictBoxSign::NonposWitness
        );
        assert_eq!(box_sign(&x, &[iv(0, 2)]).unwrap(), BoxSign::NonnegCertified);
        // A strictly negative vertex is a witness for both readings.
        let p = x.sub(&QPoly::constant(q(1, 1)));
        assert_eq!(
            box_sign_strict(&p, &[iv(0, 2)]).unwrap(),
            StrictBoxSign::NonposWitness
        );
        assert_eq!(box_sign(&p, &[iv(0, 2)]).unwrap(), BoxSign::NegWitness);
    }

    /// Bernstein incompleteness at the polynomial's own multidegree:
    /// `100x² − 100x + 26` is ≥ 1 on [0, 1] (minimum 1 at 1/2), every
    /// sampled point positive, yet the degree-2 coefficient b₁ = −24 —
    /// both readings return their honest Unknown.
    #[test]
    fn strict_incompleteness_is_unknown() {
        let x = QPoly::var(0);
        let p = x
            .mul(&x)
            .scale(&q(100, 1))
            .sub(&x.scale(&q(100, 1)))
            .add(&QPoly::constant(q(26, 1)));
        assert_eq!(
            box_sign_strict(&p, &[iv(0, 1)]).unwrap(),
            StrictBoxSign::Unknown
        );
        assert_eq!(box_sign(&p, &[iv(0, 1)]).unwrap(), BoxSign::Unknown);
    }
}
