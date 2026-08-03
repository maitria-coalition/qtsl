//! The Bernstein-cone family: the heavy recompute side-conditions of
//! the region calculus — `allForwardDiffBernCoeffsSatisfyP` (the
//! exact-rational Bernstein forward-difference coefficient sweep),
//! `coverInfeasibilityValid` (the subdivision rule's 1-D interval
//! cover recompute), and `allForwardDiffBernIntvEnclosuresSatisfyP`
//! (the float lane: the same forward-difference grid recomputed in
//! validated dtype-interval arithmetic over [`crate::fpintv`], P
//! checked at the interval lower endpoints — its own section below).
//!
//! Semantic authority: the Lean catalogue's `bernConeCoeffCheck` and
//! `coverCheck` (`lean/qtsl/Qtsl/Core/Catalogue.lean`), each defining
//! its relation as `… = true`; the arithmetic pipeline is
//! `Core/QArith.lean` (`fdBernstein` and its combinatorial
//! substrate), transcribed here over [`crate::qpoly::QPoly`] /
//! [`crate::qq::QQ`] — exact rationals throughout, no floats, no
//! matrix inversion. Nothing is trusted from the certificate: the
//! coefficient table is RECOMPUTED from (simplex, S, degree,
//! polynomial) — BernCone nodes carry no coefficient data — and the
//! subdivision cover is recomputed from the branch regions (the
//! carried cover-certificate term is read but never consulted, exactly
//! as the Lean signature marks both `_termX` and `_coverCert` unused).
//!
//! # The coefficient sweep
//!
//! `bernConeCoeffCheck simplex S degree polynomial predicate`, arm by
//! arm (every branch below mirrors a branch of the Lean function):
//!
//! 1. the extension set's simplex must BE the simplex argument (see
//!    the guard note below);
//! 2. the simplex's vertices (ascending vertex order — the model
//!    filters `Fin.finRange`) must number exactly `ambDim + 1`
//!    (full dimensionality) — else decided `false`;
//! 3. the polynomial translates through `Term.asCoordPoly?`: an
//!    idx-free term folds by `Term.toPoly` over its wires and may use
//!    at most ONE wire (which becomes coordinate 0; two or more →
//!    decided `false`), while a term with `TIdx` nodes translates by
//!    the PLAIN coordinate reading — `TIdx(TVar _, i) ↦ x_i`, the
//!    wire identity ignored; bare wires and `TIdx` of a non-var are
//!    outside the fragment (decided `false`). This is deliberately
//!    NOT the combination families' wire-keyed `asCoordPolyIdxW?`;
//! 4. the scalar-scope gate: a nonconstant idx-free polynomial
//!    requires `ambDim = 1`; an idx-bearing polynomial requires the
//!    extension set EMPTY and every `TIdx` index below `ambDim` —
//!    else decided `false`;
//! 5. `fdBernstein`: substitute the barycentric parametrization
//!    (`coordPoly` from the vertex-coordinate table), homogenize to
//!    total degree `degree` with degree-lie REJECTION (`none` — never
//!    silent truncation — when any monomial exceeds it), and take the
//!    forward-difference grid over the extension mask (`none` when
//!    the core face is empty). A `none` is a decided `false`;
//! 6. the sweep: every grid coefficient satisfies the predicate,
//!    closed-evaluated with the coefficient at the predicate hole
//!    (`satisfiesPredQ` — `Formula.evalClosed` returning `none` means
//!    that coefficient FAILS the predicate: a free wire, a `TIdx`, an
//!    `FInRegion`, or a spec hole in the predicate is a decided
//!    non-satisfaction, not a refusal, exactly as in the Lean).
//!
//! # The subdivision cover
//!
//! `coverCheck simplex S nBranches branchSimplex branchS`: the parent
//! region and every branch region must read as 1-D intervals
//! (`ExtensionSet.interval1D?`: ambient dimension one, empty
//! extension mask, exactly two simplex vertices, distinct
//! coordinates — every other shape a decided `false`), and the branch
//! intervals must chain-cover `[lo, hi]`: `nBranches` extension
//! passes of "if `iv.lo ≤ r < iv.hi` then `r := iv.hi`" (fold in
//! branch order), accepting iff `hi ≤ r` at the end. Fail-toward-
//! refusal in the design source's sense: an uncoverable gap is a
//! decided `false`. The branch families (`PSubdivide/branchSimplex`,
//! `PSubdivide/branchS`) are read as dense `0..nBranches-1` families
//! — duplicates, gaps, or out-of-range indices refuse (the model's
//! functions are total on `Fin nBranches`; missing structure is
//! undecidable, not false).
//!
//! # Guard notes (adjudications, for review eyes)
//!
//! - **Same-simplex guards at row grain** (the halfspace form's
//!   precedent, inherited): the Lean checks `S.simplex = simplex` and
//!   `(branchS k).simplex = branchSimplex k` by decidable equality on
//!   model values. At row grain those guards are decidable only when
//!   the two sides are the SAME local element — chase congruence is
//!   not in view, and two row-grain-distinct elements may or may not
//!   denote one model simplex — so distinct elements REFUSE rather
//!   than guess in either direction (the Lean demo's branch-swap
//!   `false` golden therefore transposes to a refusal here; sound —
//!   nothing is admitted — and the consuming axioms feed each node's
//!   own fields, so the guard costs no completeness in their use).
//! - **The predicate hole in the POLYNOMIAL argument refuses** (the
//!   shared `Term.toPoly` walk's standing posture: the hole is
//!   outside the term model). The row-model projection would read a
//!   `THole` as the reserved hole wire and carry it as one more
//!   opaque variable; declining that pathological shape loudly is
//!   fail-safe, never a wrong verdict.
//! - **Recompute budgets**: the composition grids grow
//!   combinatorially in (degree, ambient dimension). A certificate
//!   whose recompute exceeds the fixed budget REFUSES (never a
//!   verdict) — same posture as the structural walk's node budget.
//!
//! Verdict discipline (the crate's): a decided mismatch is
//! `Ok(false)`; unresolvable or ambiguous elements, external element
//! references where structure must be read, malformed rows,
//! incomplete vertex tables, out-of-range membership/coordinate/
//! family rows, and exhausted budgets REFUSE with a reason, never
//! guessing.

use crate::barycoord::{
    coord_table, membership_mask, qq_div, unique_local_field, unique_nat_field, BaryVocab,
};
use crate::blpredclass::eval_predclass;
use crate::error::EvalError;
use crate::formrows::{BlVocab, FormCtor, TermCtor, Walk};
use crate::fpintv::{DtypeVocab, End, FloatKind, FpFmt, FpIv};
use crate::qpoly::{mono_mul, Mono, QPoly};
use crate::qq::QQ;
use crate::roster::{BernConeKind, EntryRow, PredClassKind, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet, HashMap};

const F_COEFFS: &[(&str, &str)] = &[
    ("S", "ExtensionSet"),
    ("degree", "Nat"),
    ("polynomial", "Term"),
    ("predicate", "Formula"),
    ("simplex", "Simplex"),
];

const F_COVER: &[(&str, &str)] = &[
    ("S", "ExtensionSet"),
    ("coverCertificate", "Term"),
    ("p", "PSubdivide"),
    ("simplex", "Simplex"),
    ("termX", "Term"),
];

/// Claim order is the declaring theory's bytewise field order (S,
/// degree, dtype, polynomial, predicate, simplex), NOT the source
/// declaration order — the binder adjudicates signatures bytewise.
const F_INTV: &[(&str, &str)] = &[
    ("S", "ExtensionSet"),
    ("degree", "Nat"),
    ("dtype", "Dtype"),
    ("polynomial", "Term"),
    ("predicate", "Formula"),
    ("simplex", "Simplex"),
];

/// The Bernstein-cone family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Registration order is
/// part of the seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "allForwardDiffBernCoeffsSatisfyP",
        F_COEFFS,
        RelKind::BernCone(BernConeKind::Coeffs),
    ),
    (
        "coverInfeasibilityValid",
        F_COVER,
        RelKind::BernCone(BernConeKind::Cover),
    ),
    (
        "allForwardDiffBernIntvEnclosuresSatisfyP",
        F_INTV,
        RelKind::BernCone(BernConeKind::IntvCoeffs),
    ),
];

// ---------------------------------------------------------------------
// The subdivision-node vocabulary
// ---------------------------------------------------------------------

/// The subdivision node's resolved vocabulary: the branch-count field
/// and the two indexed branch families — name-selected once at
/// construction and shape-verified (names select, shapes verify,
/// identities pin), exactly as [`crate::barycoord::BaryVocab`].
#[derive(Debug, Clone)]
pub struct SubdivideVocab {
    /// `PSubdivide/nBranches : PSubdivide -> Nat`.
    pub(crate) n_branches: Chid,
    /// `PSubdivide/branchSimplex : [k: Nat, p: PSubdivide] -> Simplex`
    /// (field order bytewise: `k`, `p`).
    pub(crate) branch_simplex: Chid,
    /// `PSubdivide/branchS : [k: Nat, p: PSubdivide] -> ExtensionSet`.
    pub(crate) branch_s: Chid,
}

/// Build the subdivision vocabulary over the declared indices. `Err` →
/// the cover relation is not claimed (declared-but-unbound,
/// safe-fail); the coefficient sweep's claim is unaffected.
pub fn build_subdivide_vocab(
    indices: &[&TheoryIndex],
    psub_sort: Chid,
    simplex_sort: Chid,
    ext_sort: Chid,
) -> Result<SubdivideVocab, String> {
    let field = |name: &str, cod: SortKey| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational
                || d.codomain != Some(cod)
                || d.domain != DomainSig::Unary(SortKey::Elem(psub_sort))
            {
                return Err(format!(
                    "`{name}` does not have the expected field shape \
                     (unary fun on the subdivision sort)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let family = |name: &str, cod: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = !d.relational
                && d.codomain == Some(SortKey::Elem(cod))
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [(f0, SortKey::Ground(Ground::Nat)), (f1, SortKey::Elem(s1))]
                            if f0 == "k" && f1 == "p" && *s1 == psub_sort
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected indexed-family shape \
                     ([k: Nat, p: PSubdivide] -> element)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(SubdivideVocab {
        n_branches: field("PSubdivide/nBranches", SortKey::Ground(Ground::Nat))?,
        branch_simplex: family("PSubdivide/branchSimplex", simplex_sort)?,
        branch_s: family("PSubdivide/branchS", ext_sort)?,
    })
}

// ---------------------------------------------------------------------
// Budgets
// ---------------------------------------------------------------------

/// Degrees past this refuse outright: the homogenization exponents and
/// composition grids are only meaningful at certificate scale, and a
/// wild `degree` literal must never drive an unbounded enumeration.
const MAX_DEGREE: u64 = 4096;

/// Total recompute-work budget (compositions emitted + coefficient
/// rows + monomials folded). Exhaustion REFUSES.
const WORK_BUDGET: usize = 1 << 20;

/// Branch counts past this refuse (the chain check is quadratic in the
/// branch count).
const MAX_BRANCHES: u64 = 1 << 16;

struct Budget {
    left: usize,
}

impl Budget {
    fn new() -> Budget {
        Budget { left: WORK_BUDGET }
    }
    fn charge(&mut self, name: &str, n: usize) -> Result<(), EvalError> {
        if self.left < n {
            return Err(refuse(
                name,
                0,
                "Bernstein recompute exhausted its work budget — the certificate's \
                 (degree, dimension) demand is past the fixed enumeration cap"
                    .into(),
            ));
        }
        self.left -= n;
        Ok(())
    }
}

fn refuse(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

// ---------------------------------------------------------------------
// ℕ combinatorics (Lean `Core/QArith.lean` — multinomial and the
// composition grids), exact and unbounded via BigUint.
// ---------------------------------------------------------------------

/// `Nat.choose` (Lean `Prim.nchoose`), iteratively:
/// `C(n, k) = Π_{i=1..k} (n - k + i) / i`, exact at every step.
fn nchoose(n: u64, k: u64) -> BigUint {
    if k > n {
        return BigUint::zero();
    }
    let k = k.min(n - k);
    let mut acc = BigUint::one();
    for i in 1..=k {
        acc = acc * BigUint::from(n - k + i) / BigUint::from(i);
    }
    acc
}

/// Lean `multinomial`: `[] ↦ 1`, `a :: rest ↦ C(a + Σrest, a) ·
/// multinomial rest`.
fn multinomial(v: &[u64]) -> BigUint {
    match v.split_first() {
        None => BigUint::one(),
        Some((a, rest)) => {
            let tail_sum: u64 = rest.iter().sum();
            nchoose(a + tail_sum, *a) * multinomial(rest)
        }
    }
}

/// Lean `compositions parts total`: every length-`parts` vector of
/// naturals summing to exactly `total`, first coordinate ascending.
fn compositions(
    name: &str,
    parts: u64,
    total: u64,
    b: &mut Budget,
) -> Result<Vec<Vec<u64>>, EvalError> {
    if parts == 0 {
        return Ok(if total == 0 { vec![vec![]] } else { vec![] });
    }
    let mut out = Vec::new();
    for a in 0..=total {
        for rest in compositions(name, parts - 1, total - a, b)? {
            b.charge(name, 1)?;
            let mut v = Vec::with_capacity(parts as usize);
            v.push(a);
            v.extend(rest);
            out.push(v);
        }
    }
    Ok(out)
}

/// Lean `compositionsUpTo parts bound`: totals `0..=bound`, in order.
fn compositions_up_to(
    name: &str,
    parts: u64,
    bound: u64,
    b: &mut Budget,
) -> Result<Vec<Vec<u64>>, EvalError> {
    let mut out = Vec::new();
    for total in 0..=bound {
        out.extend(compositions(name, parts, total, b)?);
    }
    Ok(out)
}

/// Lean `subCompositions j`: every `k` with `k ≤ j` componentwise.
fn sub_compositions(name: &str, j: &[u64], b: &mut Budget) -> Result<Vec<Vec<u64>>, EvalError> {
    match j.split_first() {
        None => Ok(vec![vec![]]),
        Some((a, rest)) => {
            let tails = sub_compositions(name, rest, b)?;
            let mut out = Vec::new();
            for k in 0..=*a {
                for t in &tails {
                    b.charge(name, 1)?;
                    let mut v = Vec::with_capacity(j.len());
                    v.push(k);
                    v.extend(t.iter().copied());
                    out.push(v);
                }
            }
            Ok(out)
        }
    }
}

/// Lean `assembleVec smask k β`: interleave the extension-face indices
/// (`k`, at `true` positions) with the core-face indices (`β`, at
/// `false` positions), zero-padding exhausted sources.
fn assemble_vec(smask: &[bool], k: &[u64], beta: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(smask.len());
    let (mut ki, mut bi) = (0usize, 0usize);
    for &s in smask {
        if s {
            out.push(if ki < k.len() {
                ki += 1;
                k[ki - 1]
            } else {
                0
            });
        } else {
            out.push(if bi < beta.len() {
                bi += 1;
                beta[bi - 1]
            } else {
                0
            });
        }
    }
    out
}

/// Lean `vecToMono`: the multi-index as a sparse monomial (zero
/// exponents dropped; positions ascending already).
fn vec_to_mono(name: &str, v: &[u64]) -> Result<Mono, EvalError> {
    let mut m: Mono = Vec::new();
    for (i, &e) in v.iter().enumerate() {
        if e != 0 {
            let e32 = u32::try_from(e).map_err(|_| {
                refuse(
                    name,
                    0,
                    "multi-index exponent past the sparse-monomial width".into(),
                )
            })?;
            m.push((i as u64, e32));
        }
    }
    Ok(m)
}

// ---------------------------------------------------------------------
// Polynomial helpers over QPoly (the Lean `Poly` operations the
// pipeline needs beyond the qpoly floor).
// ---------------------------------------------------------------------

fn poly_pow(name: &str, p: &QPoly, e: u64, b: &mut Budget) -> Result<QPoly, EvalError> {
    let mut acc = QPoly::constant(QQ::one());
    for _ in 0..e {
        acc = acc.mul(p);
        b.charge(name, acc.0.len().max(1))?;
    }
    Ok(acc)
}

fn coeff_of(p: &QPoly, m: &Mono) -> QQ {
    p.0.get(m).cloned().unwrap_or_else(QQ::zero)
}

fn poly_vars(p: &QPoly) -> BTreeSet<u64> {
    p.0.keys().flat_map(|m| m.iter().map(|&(v, _)| v)).collect()
}

fn mono_total_deg(m: &Mono) -> u64 {
    m.iter().map(|&(_, e)| e as u64).sum()
}

/// `Σ_{i < m} λ_i` (Lean `sumVars`).
fn sum_vars(m: u64) -> QPoly {
    let mut p = QPoly::zero();
    for i in 0..m {
        p = p.add(&QPoly::var(i));
    }
    p
}

/// Lean `Poly.substInto`: substitute `σ(v)` for each variable of `p`
/// (here σ is the barycentric parametrization `coordPoly`).
fn subst_into(name: &str, p: &QPoly, sigma: &[QPoly], b: &mut Budget) -> Result<QPoly, EvalError> {
    let mut acc = QPoly::zero();
    for (mono, c) in &p.0 {
        let mut term = QPoly::constant(QQ::one());
        for &(v, e) in mono {
            let sv = sigma.get(v as usize).ok_or_else(|| {
                refuse(
                    name,
                    0,
                    "polynomial variable past the ambient dimension — \
                     outside the guarded fragment"
                        .into(),
                )
            })?;
            term = term.mul(&poly_pow(name, sv, e as u64, b)?);
            b.charge(name, term.0.len().max(1))?;
        }
        acc = acc.add(&term.scale(c));
        b.charge(name, acc.0.len().max(1))?;
    }
    Ok(acc)
}

/// Lean `homogenize m d p`: multiply each monomial by
/// `(Σ λ)^(d − deg)`; `None` on any monomial of degree above `d`
/// (degree-lie rejection — never silent truncation).
fn homogenize(
    name: &str,
    m: u64,
    d: u64,
    p: &QPoly,
    b: &mut Budget,
) -> Result<Option<QPoly>, EvalError> {
    let sv = sum_vars(m);
    let mut acc = QPoly::zero();
    for (mono, c) in &p.0 {
        let e = mono_total_deg(mono);
        if e > d {
            return Ok(None);
        }
        let mut mp = QPoly::zero();
        mp.0.insert(mono.clone(), c.clone());
        acc = acc.add(&mp.mul(&poly_pow(name, &sv, d - e, b)?));
        b.charge(name, acc.0.len().max(1))?;
    }
    Ok(Some(acc))
}

/// Lean `bernCoeffRows m d hp`: `(α, hp.coeffOf(α) / multinomial α)`
/// over `compositions m d`.
fn bern_coeff_rows(
    name: &str,
    m: u64,
    d: u64,
    hp: &QPoly,
    b: &mut Budget,
) -> Result<Vec<(Vec<u64>, QQ)>, EvalError> {
    let mut out = Vec::new();
    for alpha in compositions(name, m, d, b)? {
        let mono = vec_to_mono(name, &alpha)?;
        let c = coeff_of(hp, &mono);
        let denom = QQ::new(BigInt::from(multinomial(&alpha)), BigUint::one());
        out.push((alpha, qq_div(&c, &denom)));
        b.charge(name, 1)?;
    }
    Ok(out)
}

/// The forward-difference grid rows (Lean `fdBernstein`, the `grid`
/// component — `gridAll` sweeps only the grid, so the base rows are
/// folded into `bAt` reads rather than materialized). `Ok(None)`
/// mirrors the construction's `none` branches: an empty core face, or
/// a degree lie in homogenization.
fn fd_bernstein_grid(
    name: &str,
    coords: &[Vec<QQ>],
    smask: &[bool],
    d: u64,
    p: &QPoly,
    b: &mut Budget,
) -> Result<Option<Vec<QQ>>, EvalError> {
    let m = coords.len() as u64;
    debug_assert_eq!(smask.len() as u64, m, "masks derive from one vertex list");
    let m_s = smask.iter().filter(|&&s| s).count() as u64;
    let m_b = m - m_s;
    if m_b == 0 {
        return Ok(None);
    }

    // coordPoly: σ(j) = Σ_i coords[i][j] · λ_i.
    let amb = coords.first().map(|c| c.len()).unwrap_or(0);
    let mut sigma = Vec::with_capacity(amb);
    for j in 0..amb {
        let mut s = QPoly::zero();
        for (i, vc) in coords.iter().enumerate() {
            let mut mono_poly = QPoly::var(i as u64);
            mono_poly = mono_poly.scale(&vc[j]);
            s = s.add(&mono_poly);
        }
        sigma.push(s);
    }

    let p_lam = subst_into(name, p, &sigma, b)?;
    let Some(hp) = homogenize(name, m, d, &p_lam, b)? else {
        return Ok(None);
    };

    // bAt k β = hp.coeffOf(assembleVec smask k β) / multinomial(…).
    let b_at = |name: &str, k: &[u64], beta: &[u64]| -> Result<QQ, EvalError> {
        let alpha = assemble_vec(smask, k, beta);
        let mono = vec_to_mono(name, &alpha)?;
        let denom = QQ::new(BigInt::from(multinomial(&alpha)), BigUint::one());
        Ok(qq_div(&coeff_of(&hp, &mono), &denom))
    };

    let mut out = Vec::new();
    for j in compositions_up_to(name, m_s, d, b)? {
        // pj = Σ_{k ≤ j} (−1)^{|k|} · Π C(jᵢ, kᵢ) · qk · (Σλ)^{|k|}.
        let mut pj = QPoly::zero();
        for k in sub_compositions(name, &j, b)? {
            let k_sum: u64 = k.iter().sum();
            let neg = k_sum % 2 == 1;
            let mut binom_prod = BigUint::one();
            for (ji, ki) in j.iter().zip(k.iter()) {
                binom_prod *= nchoose(*ji, *ki);
            }
            let mut qk = QPoly::zero();
            for beta in compositions(name, m_b, d - k_sum, b)? {
                let mono = vec_to_mono(name, &beta)?;
                let mult = QQ::new(BigInt::from(multinomial(&beta)), BigUint::one());
                let coeff = b_at(name, &k, &beta)?.mul(&mult);
                if !coeff.is_zero() {
                    let mut mp = QPoly::zero();
                    mp.0.insert(mono, coeff);
                    qk = qk.add(&mp);
                }
                b.charge(name, 1)?;
            }
            let hk = qk.mul(&poly_pow(name, &sum_vars(m_b), k_sum, b)?);
            let mut scale = QQ::new(BigInt::from(binom_prod), BigUint::one());
            if neg {
                scale = scale.neg();
            }
            pj = pj.add(&hk.scale(&scale));
            b.charge(name, pj.0.len().max(1))?;
        }
        for (_, c) in bern_coeff_rows(name, m_b, d, &pj, b)? {
            out.push(c);
        }
    }
    Ok(Some(out))
}

// ---------------------------------------------------------------------
// Term folds (the plain coordinate reading + idx bounds), over rows
// ---------------------------------------------------------------------

const MAX_FOLD_DEPTH: usize = 4096;

/// Lean `Term.asCoordPolyIdx?` over rows — the PLAIN coordinate
/// translation (`TIdx(TVar _, i) ↦ x_i`, the wire identity ignored;
/// bare wires and the hole outside the fragment). `Ok(None)` = outside
/// the fragment (a decided outcome for the caller); refusals only for
/// unresolvable rows and exhausted depth.
fn coord_poly_plain(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    memo: &mut HashMap<u32, Option<QPoly>>,
    depth: usize,
) -> Result<Option<QPoly>, EvalError> {
    if let Some(p) = memo.get(&elem) {
        return Ok(p.clone());
    }
    if depth > MAX_FOLD_DEPTH {
        return Err(w.refuse(
            index,
            "coordinate translation exhausted its depth budget — pathological rows".into(),
        ));
    }
    let (k, row) = w.term_ctor_row(index, elem)?;
    let row = row.clone();
    let p: Option<QPoly> = match k {
        TermCtor::Var | TermCtor::Hole => None,
        TermCtor::Const => Some(QPoly::constant(w.const_value(index, &row)?)),
        TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            let pl = coord_poly_plain(w, index, l, memo, depth + 1)?;
            let pr = coord_poly_plain(w, index, r, memo, depth + 1)?;
            match (pl, pr) {
                (Some(pl), Some(pr)) => Some(match k {
                    TermCtor::Add => pl.add(&pr),
                    TermCtor::Sub => pl.sub(&pr),
                    _ => pl.mul(&pr),
                }),
                _ => None,
            }
        }
        TermCtor::Neg => {
            let i = w.local(index, &row.args[0])?;
            coord_poly_plain(w, index, i, memo, depth + 1)?.map(|p| p.neg())
        }
        TermCtor::Idx => {
            // args (field order): [nat i, ref t]; translates iff t is a
            // bare TVar — the wire itself is NOT read (the plain
            // reading maps every projection at index i to x_i).
            let Value::Lit(il) = &row.args[0] else {
                return Err(w.refuse(index, "TIdx index cell is not a literal".into()));
            };
            let LiteralView::Nat(i) = il.view() else {
                return Err(w.refuse(index, "TIdx index cell is not a Nat".into()));
            };
            let t = w.local(index, &row.args[1])?;
            let (tk, _) = w.term_ctor_row(index, t)?;
            if tk == TermCtor::Var {
                Some(QPoly::var(i))
            } else {
                None
            }
        }
    };
    memo.insert(elem, p.clone());
    Ok(p)
}

/// Lean `Term.idxBounded n` over rows: every `TIdx` index is a Nat
/// literal strictly below `n`.
fn idx_bounded(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    n: u64,
    memo: &mut HashMap<u32, bool>,
    depth: usize,
) -> Result<bool, EvalError> {
    if let Some(&v) = memo.get(&elem) {
        return Ok(v);
    }
    if depth > MAX_FOLD_DEPTH {
        return Err(w.refuse(
            index,
            "idx-bound sweep exhausted its depth budget — pathological rows".into(),
        ));
    }
    let (k, row) = w.term_ctor_row(index, elem)?;
    let row = row.clone();
    let v = match k {
        TermCtor::Var | TermCtor::Const | TermCtor::Hole => true,
        TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            idx_bounded(w, index, l, n, memo, depth + 1)?
                && idx_bounded(w, index, r, n, memo, depth + 1)?
        }
        TermCtor::Neg => {
            let i = w.local(index, &row.args[0])?;
            idx_bounded(w, index, i, n, memo, depth + 1)?
        }
        TermCtor::Idx => {
            let Value::Lit(il) = &row.args[0] else {
                return Err(w.refuse(index, "TIdx index cell is not a literal".into()));
            };
            let LiteralView::Nat(i) = il.view() else {
                return Err(w.refuse(index, "TIdx index cell is not a Nat".into()));
            };
            let t = w.local(index, &row.args[1])?;
            i < n && idx_bounded(w, index, t, n, memo, depth + 1)?
        }
    };
    memo.insert(elem, v);
    Ok(v)
}

// ---------------------------------------------------------------------
// The predicate sweep (`satisfiesPredQ`)
// ---------------------------------------------------------------------

/// `Term.evalQ?` with the predicate hole reading as the swept constant
/// (Lean `satisfiesPredQ` substitutes `TConst c` at the hole before
/// evaluating; the two compositions agree). `Ok(None)` = the Lean
/// `none` — a decided non-value.
fn term_eval_at_hole(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    c: &QQ,
    depth: usize,
) -> Result<Option<QQ>, EvalError> {
    if depth > MAX_FOLD_DEPTH {
        return Err(w.refuse(
            index,
            "closed evaluation exhausted its depth budget — pathological rows".into(),
        ));
    }
    let (k, row) = w.term_ctor_row(index, elem)?;
    let row = row.clone();
    Ok(match k {
        TermCtor::Hole => Some(c.clone()),
        TermCtor::Var | TermCtor::Idx => None,
        TermCtor::Const => Some(w.const_value(index, &row)?),
        TermCtor::Neg => {
            let i = w.local(index, &row.args[0])?;
            term_eval_at_hole(w, index, i, c, depth + 1)?.map(|q| q.neg())
        }
        TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            let lv = term_eval_at_hole(w, index, l, c, depth + 1)?;
            let rv = term_eval_at_hole(w, index, r, c, depth + 1)?;
            match (lv, rv) {
                (Some(lv), Some(rv)) => Some(match k {
                    TermCtor::Add => lv.add(&rv),
                    TermCtor::Sub => lv.sub(&rv),
                    _ => lv.mul(&rv),
                }),
                _ => None,
            }
        }
    })
}

/// `Formula.evalClosed` with the hole at `c` (Lean `satisfiesPredQ`'s
/// body). `Ok(None)` mirrors the Lean `none` exactly — including the
/// non-short-circuiting `Option` monad on `FAnd`/`FOr` (a `none` on
/// EITHER side dominates a decided sibling), `FInRegion ↦ none`, and
/// the wire-model spec hole `FSpH ↦ none` (no closed value exists for
/// it; a decided non-satisfaction, matching the catalogue's treatment
/// of every non-evaluable formula).
fn formula_eval_at_hole(
    w: &mut Walk<'_>,
    index: usize,
    elem: u32,
    c: &QQ,
    depth: usize,
) -> Result<Option<bool>, EvalError> {
    if depth > MAX_FOLD_DEPTH {
        return Err(w.refuse(
            index,
            "closed evaluation exhausted its depth budget — pathological rows".into(),
        ));
    }
    let (k, row) = w.form_ctor_row(index, elem)?;
    let row = row.clone();
    Ok(match k {
        FormCtor::True => Some(true),
        FormCtor::False => Some(false),
        FormCtor::SpH | FormCtor::InRegion => None,
        FormCtor::Atom(b) => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            let lv = term_eval_at_hole(w, index, l, c, depth + 1)?;
            let rv = term_eval_at_hole(w, index, r, c, depth + 1)?;
            match (lv, rv) {
                (Some(lv), Some(rv)) => {
                    use std::cmp::Ordering::*;
                    let ord = lv.cmp_qq(&rv);
                    Some(match b {
                        0 => ord == Less,
                        1 => ord != Greater,
                        2 => ord == Equal,
                        3 => ord != Less,
                        4 => ord == Greater,
                        _ => ord != Equal,
                    })
                }
                _ => None,
            }
        }
        FormCtor::And | FormCtor::Or => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            let lv = formula_eval_at_hole(w, index, l, c, depth + 1)?;
            let rv = formula_eval_at_hole(w, index, r, c, depth + 1)?;
            match (lv, rv) {
                (Some(lv), Some(rv)) => Some(if k == FormCtor::And {
                    lv && rv
                } else {
                    lv || rv
                }),
                _ => None,
            }
        }
    })
}

// ---------------------------------------------------------------------
// Geometry decode (shared by both relations)
// ---------------------------------------------------------------------

struct SimplexGeom {
    complex: u32,
    n_vertices: u64,
    amb_dim: u64,
    /// The simplex's sealed membership mask (ascending).
    mask: BTreeSet<u64>,
}

fn decode_simplex(
    name: &str,
    index: usize,
    rows: &CertRows,
    bv: &BaryVocab,
    simplex: u32,
) -> Result<SimplexGeom, EvalError> {
    let complex = unique_local_field(
        name,
        index,
        rows,
        simplex,
        bv.simplex_complex,
        "Simplex/complex",
    )?;
    let n_vertices = unique_nat_field(
        name,
        index,
        rows,
        complex,
        bv.simpc_n_vertices,
        "SimpC/n_vertices",
    )?;
    let amb_dim = unique_nat_field(
        name,
        index,
        rows,
        complex,
        bv.simpc_amb_dim,
        "SimpC/amb_dim",
    )?;
    let mask = membership_mask(
        name,
        index,
        rows,
        simplex,
        bv.simplex_contains,
        n_vertices,
        "Simplex/contains",
    )?;
    Ok(SimplexGeom {
        complex,
        n_vertices,
        amb_dim,
        mask,
    })
}

/// The row-grain same-simplex guard (module docs): the same local
/// element passes; distinct elements refuse — chase congruence is not
/// in view.
fn require_same_simplex(
    name: &str,
    index: usize,
    got: u32,
    expected: u32,
    what: &str,
) -> Result<(), EvalError> {
    if got != expected {
        return Err(refuse(
            name,
            index,
            format!(
                "{what}: the two sides are row-grain distinct elements — chase \
                 congruence is not in view here, so the same-simplex guard is \
                 undecidable; refusing over a guess"
            ),
        ));
    }
    Ok(())
}

/// Lean `ExtensionSet.interval1D?` over rows: `Ok(None)` mirrors every
/// `none` branch (ambient dimension ≠ 1, nonempty extension mask,
/// vertex count ≠ 2, coincident coordinates); refusals only from the
/// row decode (missing coordinate rows, out-of-range membership).
fn interval_1d(
    name: &str,
    index: usize,
    rows: &CertRows,
    bv: &BaryVocab,
    ext: u32,
    simplex: u32,
) -> Result<Option<(QQ, QQ)>, EvalError> {
    let geom = decode_simplex(name, index, rows, bv, simplex)?;
    if geom.amb_dim != 1 {
        return Ok(None);
    }
    let emask = membership_mask(
        name,
        index,
        rows,
        ext,
        bv.ext_contains,
        geom.n_vertices,
        "ExtensionSet/contains",
    )?;
    if !emask.is_empty() {
        return Ok(None);
    }
    if geom.mask.len() != 2 {
        return Ok(None);
    }
    let mut it = geom.mask.iter();
    let a = *it.next().expect("two members");
    let b = *it.next().expect("two members");
    let coords = coord_table(name, index, rows, bv, geom.complex, geom.n_vertices, 1)?;
    let lookup = |vert: u64| -> Result<QQ, EvalError> {
        coords.get(&(vert, 0)).cloned().ok_or_else(|| {
            refuse(
                name,
                index,
                format!(
                    "no `SimpC/coord` row for vertex {vert}, axis 0 — the vertex \
                     table in view is incomplete, unresolvable"
                ),
            )
        })
    };
    let v0 = lookup(a)?;
    let v1 = lookup(b)?;
    use std::cmp::Ordering::*;
    Ok(match v0.cmp_qq(&v1) {
        Less => Some((v0, v1)),
        Greater => Some((v1, v0)),
        Equal => None,
    })
}

/// The dense `0..n-1` indexed family `fun{k, node} = elem`, read from
/// the rows about `node` — bijective presence (the model's branch
/// functions are total on `Fin nBranches`): duplicates, gaps, or
/// out-of-range `k` refuse; values must be local element refs.
fn dense_family(
    name: &str,
    index: usize,
    rows: &CertRows,
    node: u32,
    fun: Chid,
    n: u64,
    what: &str,
) -> Result<Vec<u32>, EvalError> {
    let n_usize = usize::try_from(n)
        .ok()
        .filter(|n| *n as u64 <= MAX_BRANCHES)
        .ok_or_else(|| {
            refuse(
                name,
                index,
                format!("`{what}` family size {n} out of budget"),
            )
        })?;
    let mut out: Vec<Option<u32>> = vec![None; n_usize];
    for row in rows.arg_rows(node) {
        if row.fun != fun {
            continue;
        }
        // Field order is bytewise: `k` precedes `p` — args = [nat k,
        // ref node]. Verify the node position actually IS this node
        // (arg_rows only guarantees membership somewhere).
        let [k_cell, p_cell] = row.args.as_slice() else {
            return Err(refuse(
                name,
                index,
                format!("`{what}` row has {} args (expected 2)", row.args.len()),
            ));
        };
        let p_local = match p_cell {
            Value::Ref(r) => rows.local(r),
            _ => None,
        };
        if p_local != Some(node) {
            continue;
        }
        let Value::Lit(kl) = k_cell else {
            return Err(refuse(
                name,
                index,
                format!("`{what}` index cell is not a literal"),
            ));
        };
        let LiteralView::Nat(k) = kl.view() else {
            return Err(refuse(
                name,
                index,
                format!("`{what}` index cell is not a Nat"),
            ));
        };
        let Ok(ku) = usize::try_from(k) else {
            return Err(refuse(
                name,
                index,
                format!("`{what}` index {k} out of range"),
            ));
        };
        if ku >= n_usize {
            return Err(refuse(
                name,
                index,
                format!("`{what}` index {k} >= declared branch count {n}"),
            ));
        }
        let elem = match &row.value {
            Value::Ref(r) => rows.local(r).ok_or_else(|| {
                refuse(
                    name,
                    index,
                    format!("`{what}` value is an external element ref — single-body context"),
                )
            })?,
            _ => {
                return Err(refuse(
                    name,
                    index,
                    format!("`{what}` value is not an element ref"),
                ))
            }
        };
        let slot = &mut out[ku];
        if slot.is_some() {
            return Err(refuse(
                name,
                index,
                format!("`{what}` index {k} appears twice"),
            ));
        }
        *slot = Some(elem);
    }
    out.into_iter()
        .enumerate()
        .map(|(k, v)| v.ok_or_else(|| refuse(name, index, format!("`{what}` index {k} missing"))))
        .collect()
}

// ---------------------------------------------------------------------
// The evaluators
// ---------------------------------------------------------------------

/// Evaluate a Bernstein-cone relation. Argument cells arrive in
/// declared (bytewise) field order — the entry table above. `blv` is
/// `Some` for every claimed coefficient-sweep entry, `sv` for every
/// claimed cover entry, and `dv` for every claimed float-lane entry
/// (construction invariants of the provider).
// The argument list is the vocabulary bundle itself (one optional wing
// per claimed entry family) — a dispatch hub, not a call-site burden.
#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_berncone(
    name: &str,
    blv: Option<&BlVocab>,
    bv: &BaryVocab,
    sv: Option<&SubdivideVocab>,
    dv: Option<&DtypeVocab>,
    kind: BernConeKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        BernConeKind::Coeffs => {
            let blv = blv.expect("claimed implies vocabulary");
            eval_coeffs(name, blv, bv, args, rows)
        }
        BernConeKind::Cover => {
            let sv = sv.expect("claimed implies vocabulary");
            eval_cover(name, bv, sv, args, rows)
        }
        BernConeKind::IntvCoeffs => {
            let blv = blv.expect("claimed implies vocabulary");
            let dv = dv.expect("claimed implies vocabulary");
            eval_intv_coeffs(name, blv, bv, dv, args, rows)
        }
    }
}

fn nat_arg(name: &str, index: usize, v: &Value) -> Result<u64, EvalError> {
    let Value::Lit(l) = v else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "Nat",
            found: 0xFF,
        });
    };
    let LiteralView::Nat(n) = l.view() else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "Nat",
            found: l.dtype_code(),
        });
    };
    Ok(n)
}

/// A carried-but-not-consulted Term argument: must be an element ref
/// (local or external — its structure is never read, exactly as the
/// Lean signature ignores it), anything else is a malformed cell.
fn carried_term_arg(name: &str, index: usize, v: &Value) -> Result<(), EvalError> {
    if matches!(v, Value::Ref(_)) {
        Ok(())
    } else {
        Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "element ref",
            found: 0xFF,
        })
    }
}

/// `allForwardDiffBernCoeffsSatisfyP` — field order: S, degree,
/// polynomial, predicate, simplex.
fn eval_coeffs(
    name: &str,
    blv: &BlVocab,
    bv: &BaryVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, blv, rows);
    let s_ext = w.local(0, args[0])?;
    let degree = nat_arg(name, 1, args[1])?;
    let polynomial = w.local(2, args[2])?;
    let predicate = w.local(3, args[3])?;
    let simplex = w.local(4, args[4])?;

    // The `S.simplex = simplex` guard, at row grain (module docs).
    let s_simplex =
        unique_local_field(name, 0, rows, s_ext, bv.ext_simplex, "ExtensionSet/simplex")?;
    require_same_simplex(
        name,
        0,
        s_simplex,
        simplex,
        "the extension set's simplex and the simplex argument",
    )?;

    let geom = decode_simplex(name, 4, rows, bv, simplex)?;
    // Full dimensionality: exactly ambDim + 1 vertices — else the Lean
    // decides false.
    if geom.mask.len() as u64 != geom.amb_dim + 1 {
        return Ok(false);
    }
    if degree > MAX_DEGREE {
        return Err(refuse(
            name,
            1,
            format!("degree {degree} past the recompute budget ({MAX_DEGREE})"),
        ));
    }

    // Term.asCoordPoly?, arm by arm.
    let p: QPoly = if w.idx_free(2, polynomial)? {
        // toPoly over wires; at most one distinct wire, remapped to
        // coordinate 0 (the walk refuses on the predicate hole — the
        // module docs' fail-safe divergence note).
        let wp = w.to_poly(2, polynomial)?;
        let vars = poly_vars(&wp);
        match vars.len() {
            0 => wp,
            1 => {
                // Exactly one distinct wire in the whole polynomial —
                // every monomial's variable is that wire; remap it to
                // coordinate 0 (the Lean single-var arm).
                let mut out = QPoly::zero();
                for (mono, c) in &wp.0 {
                    let m0: Mono = mono.iter().map(|&(_, e)| (0u64, e)).collect();
                    out.0.insert(m0, c.clone());
                }
                out
            }
            _ => return Ok(false),
        }
    } else {
        match coord_poly_plain(&mut w, 2, polynomial, &mut HashMap::new(), 0)? {
            None => return Ok(false),
            Some(p) => p,
        }
    };

    // The scalar-scope gates (Lean, both arms).
    if w.idx_free(2, polynomial)? {
        if !poly_vars(&p).is_empty() && geom.amb_dim != 1 {
            return Ok(false);
        }
    } else {
        let emask_probe = membership_mask(
            name,
            0,
            rows,
            s_ext,
            bv.ext_contains,
            geom.n_vertices,
            "ExtensionSet/contains",
        )?;
        if !emask_probe.is_empty()
            || !idx_bounded(&mut w, 2, polynomial, geom.amb_dim, &mut HashMap::new(), 0)?
        {
            return Ok(false);
        }
    }

    // The vertex-coordinate table, complete on verts × axes.
    let table = coord_table(
        name,
        4,
        rows,
        bv,
        geom.complex,
        geom.n_vertices,
        geom.amb_dim,
    )?;
    let verts: Vec<u64> = geom.mask.iter().copied().collect();
    let mut coords: Vec<Vec<QQ>> = Vec::with_capacity(verts.len());
    for &v in &verts {
        let mut vc = Vec::with_capacity(geom.amb_dim as usize);
        for j in 0..geom.amb_dim {
            vc.push(table.get(&(v, j)).cloned().ok_or_else(|| {
                refuse(
                    name,
                    4,
                    format!(
                        "no `SimpC/coord` row for vertex {v}, axis {j} — the vertex \
                         table in view is incomplete, unresolvable"
                    ),
                )
            })?);
        }
        coords.push(vc);
    }
    let emask = membership_mask(
        name,
        0,
        rows,
        s_ext,
        bv.ext_contains,
        geom.n_vertices,
        "ExtensionSet/contains",
    )?;
    let smask: Vec<bool> = verts.iter().map(|v| emask.contains(v)).collect();

    let mut budget = Budget::new();
    let Some(grid) = fd_bernstein_grid(name, &coords, &smask, degree, &p, &mut budget)? else {
        return Ok(false);
    };

    // The predicate sweep.
    for c in &grid {
        let sat = formula_eval_at_hole(&mut w, 3, predicate, c, 0)? == Some(true);
        if !sat {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `coverInfeasibilityValid` — field order: S, coverCertificate, p,
/// simplex, termX.
fn eval_cover(
    name: &str,
    bv: &BaryVocab,
    sv: &SubdivideVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let local = |index: usize, v: &Value| -> Result<u32, EvalError> {
        match v {
            Value::Ref(r) => rows.local(r).ok_or_else(|| {
                refuse(
                    name,
                    index,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: name.into(),
                index,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    };
    let s_ext = local(0, args[0])?;
    carried_term_arg(name, 1, args[1])?;
    let p_node = local(2, args[2])?;
    let simplex = local(3, args[3])?;
    carried_term_arg(name, 4, args[4])?;

    // The `S.simplex = simplex` guard, at row grain (module docs).
    let s_simplex =
        unique_local_field(name, 0, rows, s_ext, bv.ext_simplex, "ExtensionSet/simplex")?;
    require_same_simplex(
        name,
        0,
        s_simplex,
        simplex,
        "the extension set's simplex and the simplex argument",
    )?;

    // The parent interval (a decided `false` on every `none` branch).
    let Some((lo, hi)) = interval_1d(name, 0, rows, bv, s_ext, s_simplex)? else {
        return Ok(false);
    };

    // The branch families, dense over 0..nBranches-1.
    let n_branches =
        unique_nat_field(name, 2, rows, p_node, sv.n_branches, "PSubdivide/nBranches")?;
    let branch_simplex = dense_family(
        name,
        2,
        rows,
        p_node,
        sv.branch_simplex,
        n_branches,
        "PSubdivide/branchSimplex",
    )?;
    let branch_s = dense_family(
        name,
        2,
        rows,
        p_node,
        sv.branch_s,
        n_branches,
        "PSubdivide/branchS",
    )?;

    // Per branch: the `branchS(k).simplex = branchSimplex(k)` guard
    // (row grain — module docs) and the branch interval.
    let mut ivs: Vec<(QQ, QQ)> = Vec::with_capacity(branch_s.len());
    for (k, (&bs, &bsimp)) in branch_s.iter().zip(branch_simplex.iter()).enumerate() {
        let bs_simplex =
            unique_local_field(name, 2, rows, bs, bv.ext_simplex, "ExtensionSet/simplex")?;
        require_same_simplex(
            name,
            2,
            bs_simplex,
            bsimp,
            &format!("branch {k}: the branch extension set's simplex and the branch simplex"),
        )?;
        let Some(iv) = interval_1d(name, 2, rows, bv, bs, bs_simplex)? else {
            return Ok(false);
        };
        ivs.push(iv);
    }

    // The chain check: `ivs.length` extension passes, fold in branch
    // order (Lean `coverReach` / `coverExtendPass` / `coverChainCheck`).
    use std::cmp::Ordering::*;
    let mut r = lo;
    for _ in 0..ivs.len() {
        for iv in &ivs {
            if iv.0.cmp_qq(&r) != Greater && r.cmp_qq(&iv.1) == Less {
                r = iv.1.clone();
            }
        }
    }
    Ok(hi.cmp_qq(&r) != Greater)
}

// ---------------------------------------------------------------------
// The float lane: `allForwardDiffBernIntvEnclosuresSatisfyP`
// (substrate: [`crate::fpintv`]). The SAME pipeline as the exact
// sweep, arm for
// arm, with interval scalars — inputs (vertex coordinates, polynomial
// coefficients) enter as dtype enclosures and every operation rounds
// outward through the Lean-pinned `rdn`/`rup` maps, so by induction
// every computed interval CONTAINS its exact-sweep counterpart. The
// Prop is extensional (for every grid coefficient c there exists a
// dtype-representable v ≤ c with P(v), P read as `satisfiesPredQ`);
// the verdicts:
//
// - HOLDS: every grid interval has a finite lower endpoint c⁻ with
//   P(c⁻) — c⁻ is on the format grid and ≤ c, the witness directly.
// - FALSE: a structural arm decides false (the exact twin's
//   semantics), or an endpoint evaluation returns the Lean `none`
//   (`evalClosed` none-ness is hole-value-INDEPENDENT — structure on
//   evaluated paths, the non-short-circuiting monad — so one `none`
//   refutes P(v) for every v), or the predicate is certified
//   upward-closed-conic (the landed `blpredclass` classifier — the
//   consuming axiom carries that premise separately, so this gate
//   guards only OUR false verdict) and some finite upper endpoint c⁺
//   has P(c⁺) = false: c ≤ c⁺ + upward-closure twice refutes the
//   existential.
// - REFUSE: enclosure too wide to decide, ∞ endpoints where a witness
//   was needed, the predicate unclassified when only the false arm
//   remained, non-float / nonneg / unconstructed dtypes, budgets.
//
// **Degree-lie at interval grain** (the one arm that cannot transpose
// verbatim): a homogenization monomial above `degree` whose interval
// coefficient excludes zero is a CERTAIN lie — decided false; one
// whose interval straddles zero is indeterminate (the exact
// coefficient may be the cancellation the intervals cannot see) —
// REFUSED, never guessed in either direction.
// ---------------------------------------------------------------------

/// Sparse multivariate polynomial with interval coefficients (the
/// pipeline's working type; exactly-[0,0] coefficients drop, anything
/// merely CONTAINING zero is kept — containment is the invariant).
#[derive(Debug, Clone, Default)]
struct IvPoly(BTreeMap<Mono, FpIv>);

impl IvPoly {
    fn zero() -> IvPoly {
        IvPoly::default()
    }

    fn var(v: u64) -> IvPoly {
        let mut m = BTreeMap::new();
        m.insert(vec![(v, 1)], FpIv::one());
        IvPoly(m)
    }

    fn one() -> IvPoly {
        let mut m = BTreeMap::new();
        m.insert(Vec::new(), FpIv::one());
        IvPoly(m)
    }

    fn coeff_of(&self, m: &Mono) -> FpIv {
        self.0.get(m).cloned().unwrap_or_else(FpIv::zero)
    }

    fn add_term(&mut self, fmt: &FpFmt, m: Mono, iv: FpIv) {
        use std::collections::btree_map::Entry;
        if iv.is_exact_zero() {
            return;
        }
        match self.0.entry(m) {
            Entry::Vacant(e) => {
                e.insert(iv);
            }
            Entry::Occupied(mut e) => {
                let s = e.get().add(fmt, &iv);
                if s.is_exact_zero() {
                    e.remove();
                } else {
                    *e.get_mut() = s;
                }
            }
        }
    }

    fn add(&self, fmt: &FpFmt, o: &IvPoly) -> IvPoly {
        let mut out = self.clone();
        for (m, c) in &o.0 {
            out.add_term(fmt, m.clone(), c.clone());
        }
        out
    }

    fn mul(&self, fmt: &FpFmt, o: &IvPoly) -> IvPoly {
        let mut out = IvPoly::zero();
        for (ma, ca) in &self.0 {
            for (mb, cb) in &o.0 {
                out.add_term(fmt, mono_mul(ma, mb), ca.mul(fmt, cb));
            }
        }
        out
    }

    fn scale_q(&self, fmt: &FpFmt, c: &QQ) -> IvPoly {
        if c.is_zero() {
            return IvPoly::zero();
        }
        let mut out = IvPoly::zero();
        for (m, iv) in &self.0 {
            out.add_term(fmt, m.clone(), iv.scale(fmt, c));
        }
        out
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

/// `Σ_{i < m} λ_i` with exact-one coefficients (representable at every
/// format — width stays zero).
fn sum_vars_iv(m: u64) -> IvPoly {
    let mut p = IvPoly::zero();
    for i in 0..m {
        p.0.insert(vec![(i, 1)], FpIv::one());
    }
    p
}

fn poly_pow_iv(
    name: &str,
    fmt: &FpFmt,
    p: &IvPoly,
    e: u64,
    b: &mut Budget,
) -> Result<IvPoly, EvalError> {
    let mut acc = IvPoly::one();
    for _ in 0..e {
        acc = acc.mul(fmt, p);
        b.charge(name, acc.len().max(1))?;
    }
    Ok(acc)
}

/// `Poly.substInto` with interval scalars: the exact polynomial's
/// coefficients enter as enclosures here (`scale_q` rounds outward).
fn subst_into_iv(
    name: &str,
    fmt: &FpFmt,
    p: &QPoly,
    sigma: &[IvPoly],
    b: &mut Budget,
) -> Result<IvPoly, EvalError> {
    let mut acc = IvPoly::zero();
    for (mono, c) in &p.0 {
        let mut term = IvPoly::one();
        for &(v, e) in mono {
            let sv = sigma.get(v as usize).ok_or_else(|| {
                refuse(
                    name,
                    0,
                    "polynomial variable past the ambient dimension — \
                     outside the guarded fragment"
                        .into(),
                )
            })?;
            term = term.mul(fmt, &poly_pow_iv(name, fmt, sv, e as u64, b)?);
            b.charge(name, term.len().max(1))?;
        }
        acc = acc.add(fmt, &term.scale_q(fmt, c));
        b.charge(name, acc.len().max(1))?;
    }
    Ok(acc)
}

/// `homogenize` at interval grain. `Ok(None)` = a CERTAIN degree lie
/// (a too-high monomial whose interval excludes zero); a too-high
/// monomial straddling zero REFUSES (module doc above — the exact
/// coefficient may be a cancellation the intervals cannot see, so
/// neither verdict is available at this width).
fn homogenize_iv(
    name: &str,
    fmt: &FpFmt,
    m: u64,
    d: u64,
    p: &IvPoly,
    b: &mut Budget,
) -> Result<Option<IvPoly>, EvalError> {
    let sv = sum_vars_iv(m);
    let mut acc = IvPoly::zero();
    for (mono, c) in &p.0 {
        let e = mono_total_deg(mono);
        if e > d {
            let excludes_zero = match (&c.lo, &c.hi) {
                (End::Fin(lo), End::Fin(hi)) => {
                    use std::cmp::Ordering::*;
                    lo.cmp_qq(&QQ::zero()) == Greater || hi.cmp_qq(&QQ::zero()) == Less
                }
                // An ∞ endpoint cannot exclude zero from above/below
                // on its own side; check the finite side.
                (End::Fin(lo), End::PosInf) => {
                    lo.cmp_qq(&QQ::zero()) == std::cmp::Ordering::Greater
                }
                (End::NegInf, End::Fin(hi)) => hi.cmp_qq(&QQ::zero()) == std::cmp::Ordering::Less,
                _ => false,
            };
            if excludes_zero {
                return Ok(None);
            }
            return Err(refuse(
                name,
                0,
                "degree-lie indeterminate at dtype width: a homogenization \
                 monomial above the declared degree has an interval \
                 coefficient straddling zero — a wider dtype or the \
                 exact-lane relation decides"
                    .into(),
            ));
        }
        let mut mp = IvPoly::zero();
        mp.0.insert(mono.clone(), c.clone());
        acc = acc.add(fmt, &mp.mul(fmt, &poly_pow_iv(name, fmt, &sv, d - e, b)?));
        b.charge(name, acc.len().max(1))?;
    }
    Ok(Some(acc))
}

/// The forward-difference grid with interval scalars — line-pinned to
/// [`fd_bernstein_grid`], every arm in the same order; only the
/// scalar type and the degree-lie adjudication differ.
fn fd_bernstein_grid_iv(
    name: &str,
    fmt: &FpFmt,
    coords: &[Vec<QQ>],
    smask: &[bool],
    d: u64,
    p: &QPoly,
    b: &mut Budget,
) -> Result<Option<Vec<FpIv>>, EvalError> {
    let m = coords.len() as u64;
    debug_assert_eq!(smask.len() as u64, m, "masks derive from one vertex list");
    let m_s = smask.iter().filter(|&&s| s).count() as u64;
    let m_b = m - m_s;
    if m_b == 0 {
        return Ok(None);
    }

    // coordPoly with enclosed vertex coordinates.
    let amb = coords.first().map(|c| c.len()).unwrap_or(0);
    let mut sigma = Vec::with_capacity(amb);
    for j in 0..amb {
        let mut s = IvPoly::zero();
        for (i, vc) in coords.iter().enumerate() {
            s = s.add(fmt, &IvPoly::var(i as u64).scale_q(fmt, &vc[j]));
        }
        sigma.push(s);
    }

    let p_lam = subst_into_iv(name, fmt, p, &sigma, b)?;
    let Some(hp) = homogenize_iv(name, fmt, m, d, &p_lam, b)? else {
        return Ok(None);
    };

    let b_at = |k: &[u64], beta: &[u64]| -> Result<FpIv, EvalError> {
        let alpha = assemble_vec(smask, k, beta);
        let mono = vec_to_mono(name, &alpha)?;
        Ok(hp.coeff_of(&mono).div_nat(fmt, &multinomial(&alpha)))
    };

    let mut out = Vec::new();
    for j in compositions_up_to(name, m_s, d, b)? {
        let mut pj = IvPoly::zero();
        for k in sub_compositions(name, &j, b)? {
            let k_sum: u64 = k.iter().sum();
            let neg = k_sum % 2 == 1;
            let mut binom_prod = BigUint::one();
            for (ji, ki) in j.iter().zip(k.iter()) {
                binom_prod *= nchoose(*ji, *ki);
            }
            let mut qk = IvPoly::zero();
            for beta in compositions(name, m_b, d - k_sum, b)? {
                let mono = vec_to_mono(name, &beta)?;
                let mult = QQ::new(BigInt::from(multinomial(&beta)), BigUint::one());
                let coeff = b_at(&k, &beta)?.scale(fmt, &mult);
                if !coeff.is_exact_zero() {
                    let mut mp = IvPoly::zero();
                    mp.0.insert(mono, coeff);
                    qk = qk.add(fmt, &mp);
                }
                b.charge(name, 1)?;
            }
            let hk = qk.mul(fmt, &poly_pow_iv(name, fmt, &sum_vars_iv(m_b), k_sum, b)?);
            let mut scale = QQ::new(BigInt::from(binom_prod), BigUint::one());
            if neg {
                scale = scale.neg();
            }
            pj = pj.add(fmt, &hk.scale_q(fmt, &scale));
            b.charge(name, pj.len().max(1))?;
        }
        // `bernCoeffRows` at interval grain: coeff / multinomial over
        // the core-face compositions, in the same order.
        for alpha in compositions(name, m_b, d, b)? {
            let mono = vec_to_mono(name, &alpha)?;
            out.push(pj.coeff_of(&mono).div_nat(fmt, &multinomial(&alpha)));
            b.charge(name, 1)?;
        }
    }
    Ok(Some(out))
}

// ---------------------------------------------------------------------
// Dtype decode (design note §5)
// ---------------------------------------------------------------------

/// Resolve which nullary constant produced `elem`: exactly one
/// recognized producer row → its tag; none → unconstructed (refuse);
/// conflicting → ambiguous (refuse). `candidates` maps constant chids
/// to tags; unrecognized producer funs are ignored (other theories may
/// also cite the element).
fn resolve_const<T: Copy>(
    name: &str,
    index: usize,
    rows: &CertRows,
    elem: u32,
    candidates: &[(Chid, T)],
    what: &str,
) -> Result<T, EvalError> {
    let mut hit: Option<(Chid, T)> = None;
    for row in rows.producers(elem) {
        if !row.args.is_empty() {
            continue;
        }
        for (chid, tag) in candidates {
            if row.fun == *chid {
                match &hit {
                    None => hit = Some((*chid, *tag)),
                    Some((h, _)) if *h == *chid => {}
                    Some(_) => {
                        return Err(refuse(
                            name,
                            index,
                            format!(
                                "ambiguous `{what}`: conflicting constant rows — never picking"
                            ),
                        ))
                    }
                }
            }
        }
    }
    hit.map(|(_, t)| t).ok_or_else(|| {
        refuse(
            name,
            index,
            format!(
                "`{what}` element has no recognized constant constructor row in \
                 view — unconstructed, unresolvable"
            ),
        )
    })
}

/// Decode a `Dtype` element to a float format. Routes, in order: a
/// recognized alias producer (`F64` binds; `Q`/`Z`/`Nat`/`B` refuse by
/// name — the float lane's honest boundary), a `mkDtype` producer
/// (axes resolved through their own constant rows), or direct
/// `Dtype/kind`/`sign`/`ext` field rows. Sign must be `Ss` (no
/// authority pins the nonneg-format clamp); both `Efin` and `Eext`
/// bind — the verdict logic never branches on ext (an ∞ endpoint can
/// witness nothing either way; design note §5).
fn decode_dtype(
    name: &str,
    index: usize,
    rows: &CertRows,
    dv: &DtypeVocab,
    elem: u32,
) -> Result<&'static FpFmt, EvalError> {
    let local = |v: &Value, what: &str| -> Result<u32, EvalError> {
        match v {
            Value::Ref(r) => rows.local(r).ok_or_else(|| {
                refuse(
                    name,
                    index,
                    format!("`{what}` is an external element ref — single-body context"),
                )
            }),
            _ => Err(refuse(
                name,
                index,
                format!("`{what}` is not an element ref"),
            )),
        }
    };

    // Producer routes first.
    let mut axes: Option<(u32, u32, u32)> = None;
    for row in rows.producers(elem) {
        if row.fun == dv.alias_f64 {
            // ax/F64_is pins (KF64, Ss, Eext).
            return Ok(FloatKind::F64.fmt());
        }
        if row.fun == dv.alias_q
            || row.fun == dv.alias_z
            || row.fun == dv.alias_nat
            || row.fun == dv.alias_b
        {
            return Err(refuse(
                name,
                index,
                "exact-dtype alias (Q/Z/Nat/B) — the float lane refuses; exact \
                 dtypes certify via `allForwardDiffBernCoeffsSatisfyP`"
                    .into(),
            ));
        }
        if row.fun == dv.mk_dtype {
            let [k, s, e] = row.args.as_slice() else {
                return Err(refuse(
                    name,
                    index,
                    format!(
                        "malformed `mkDtype` row: {} args (expected 3)",
                        row.args.len()
                    ),
                ));
            };
            let trio = (
                local(k, "mkDtype k")?,
                local(s, "mkDtype s")?,
                local(e, "mkDtype e")?,
            );
            match &axes {
                None => axes = Some(trio),
                Some(prev) if *prev == trio => {}
                Some(_) => {
                    return Err(refuse(
                        name,
                        index,
                        "ambiguous dtype: conflicting `mkDtype` rows — never picking".into(),
                    ))
                }
            }
        }
    }

    // Field-row route when no producer resolved the axes.
    let (k_elem, s_elem, e_elem) = match axes {
        Some(t) => t,
        None => (
            unique_local_field(name, index, rows, elem, dv.kind_field, "Dtype/kind")?,
            unique_local_field(name, index, rows, elem, dv.sign_field, "Dtype/sign")?,
            unique_local_field(name, index, rows, elem, dv.ext_field, "Dtype/ext")?,
        ),
    };

    // Kind: the four float formats bind; exact kinds refuse by name.
    #[derive(Clone, Copy)]
    enum K {
        Float(FloatKind),
        Exact,
    }
    let kind = resolve_const(
        name,
        index,
        rows,
        k_elem,
        &[
            (dv.k_f16, K::Float(FloatKind::F16)),
            (dv.k_f16bf, K::Float(FloatKind::Bf16)),
            (dv.k_f32, K::Float(FloatKind::F32)),
            (dv.k_f64, K::Float(FloatKind::F64)),
            (dv.k_bool, K::Exact),
            (dv.k_int, K::Exact),
            (dv.k_rat, K::Exact),
        ],
        "Dtype kind",
    )?;
    let K::Float(fk) = kind else {
        return Err(refuse(
            name,
            index,
            "exact dtype kind (KBool/KInt/KRat) — the float lane refuses; exact \
             dtypes certify via `allForwardDiffBernCoeffsSatisfyP`"
                .into(),
        ));
    };

    // Sign: Ss binds; Snn refuses (no clamp authority).
    let signed = resolve_const(
        name,
        index,
        rows,
        s_elem,
        &[(dv.s_s, true), (dv.s_nn, false)],
        "Dtype sign",
    )?;
    if !signed {
        return Err(refuse(
            name,
            index,
            "nonnegative float dtype (Snn) — no authority pins the nonneg-format \
             rounding clamps; refusing over a guess"
                .into(),
        ));
    }

    // Ext: both bind; the verdict logic never branches on it.
    let _ext_fin = resolve_const(
        name,
        index,
        rows,
        e_elem,
        &[(dv.e_fin, true), (dv.e_ext, false)],
        "Dtype ext",
    )?;

    Ok(fk.fmt())
}

/// `allForwardDiffBernIntvEnclosuresSatisfyP` — field order: S,
/// degree, dtype, polynomial, predicate, simplex (registry bytewise).
/// Structural arms are the exact twin's, index-shifted; the sweep is
/// the module-doc trichotomy.
fn eval_intv_coeffs(
    name: &str,
    blv: &BlVocab,
    bv: &BaryVocab,
    dv: &DtypeVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, blv, rows);
    let s_ext = w.local(0, args[0])?;
    let degree = nat_arg(name, 1, args[1])?;
    let dtype_elem = w.local(2, args[2])?;
    let polynomial = w.local(3, args[3])?;
    let predicate = w.local(4, args[4])?;
    let simplex = w.local(5, args[5])?;

    // The `S.simplex = simplex` guard, at row grain (module docs).
    let s_simplex =
        unique_local_field(name, 0, rows, s_ext, bv.ext_simplex, "ExtensionSet/simplex")?;
    require_same_simplex(
        name,
        0,
        s_simplex,
        simplex,
        "the extension set's simplex and the simplex argument",
    )?;

    let geom = decode_simplex(name, 5, rows, bv, simplex)?;
    if geom.mask.len() as u64 != geom.amb_dim + 1 {
        return Ok(false);
    }
    if degree > MAX_DEGREE {
        return Err(refuse(
            name,
            1,
            format!("degree {degree} past the recompute budget ({MAX_DEGREE})"),
        ));
    }

    let fmt = decode_dtype(name, 2, rows, dv, dtype_elem)?;

    // Term.asCoordPoly?, arm by arm (the exact twin's translation —
    // the polynomial's own coefficients are certificate data, read
    // exactly; enclosure begins at the pipeline entry).
    let p: QPoly = if w.idx_free(3, polynomial)? {
        let wp = w.to_poly(3, polynomial)?;
        let vars = poly_vars(&wp);
        match vars.len() {
            0 => wp,
            1 => {
                let mut out = QPoly::zero();
                for (mono, c) in &wp.0 {
                    let m0: Mono = mono.iter().map(|&(_, e)| (0u64, e)).collect();
                    out.0.insert(m0, c.clone());
                }
                out
            }
            _ => return Ok(false),
        }
    } else {
        match coord_poly_plain(&mut w, 3, polynomial, &mut HashMap::new(), 0)? {
            None => return Ok(false),
            Some(p) => p,
        }
    };

    // The scalar-scope gates (the exact twin's, index-shifted).
    if w.idx_free(3, polynomial)? {
        if !poly_vars(&p).is_empty() && geom.amb_dim != 1 {
            return Ok(false);
        }
    } else {
        let emask_probe = membership_mask(
            name,
            0,
            rows,
            s_ext,
            bv.ext_contains,
            geom.n_vertices,
            "ExtensionSet/contains",
        )?;
        if !emask_probe.is_empty()
            || !idx_bounded(&mut w, 3, polynomial, geom.amb_dim, &mut HashMap::new(), 0)?
        {
            return Ok(false);
        }
    }

    let table = coord_table(
        name,
        5,
        rows,
        bv,
        geom.complex,
        geom.n_vertices,
        geom.amb_dim,
    )?;
    let verts: Vec<u64> = geom.mask.iter().copied().collect();
    let mut coords: Vec<Vec<QQ>> = Vec::with_capacity(verts.len());
    for &v in &verts {
        let mut vc = Vec::with_capacity(geom.amb_dim as usize);
        for j in 0..geom.amb_dim {
            vc.push(table.get(&(v, j)).cloned().ok_or_else(|| {
                refuse(
                    name,
                    5,
                    format!(
                        "no `SimpC/coord` row for vertex {v}, axis {j} — the vertex \
                         table in view is incomplete, unresolvable"
                    ),
                )
            })?);
        }
        coords.push(vc);
    }
    let emask = membership_mask(
        name,
        0,
        rows,
        s_ext,
        bv.ext_contains,
        geom.n_vertices,
        "ExtensionSet/contains",
    )?;
    let smask: Vec<bool> = verts.iter().map(|v| emask.contains(v)).collect();

    let mut budget = Budget::new();
    let Some(grid) = fd_bernstein_grid_iv(name, fmt, &coords, &smask, degree, &p, &mut budget)?
    else {
        return Ok(false);
    };

    // The sweep (module-doc trichotomy). A Lean-`none` evaluation at
    // any finite endpoint decides FALSE outright: `evalClosed`
    // none-ness is hole-value-independent, so one `none` refutes P(v)
    // for every candidate witness.
    let mut all_lo_ok = true;
    for iv in &grid {
        match &iv.lo {
            End::Fin(lo) => match formula_eval_at_hole(&mut w, 4, predicate, lo, 0)? {
                Some(true) => {}
                Some(false) => all_lo_ok = false,
                None => return Ok(false),
            },
            _ => all_lo_ok = false,
        }
    }
    if all_lo_ok {
        return Ok(true);
    }

    // The false arm: gated on the certified upward-closed-conic
    // classification (soundness: c ≤ c⁺, so P(v) for any v ≤ c would
    // transport up to P(c⁺) — refuted). A classifier refusal gates
    // toward our refusal, never a verdict.
    let up_closed = matches!(
        eval_predclass(name, blv, PredClassKind::UpClosedConic, &[args[4]], rows),
        Ok(true)
    );
    if up_closed {
        for iv in &grid {
            if let End::Fin(hi) = &iv.hi {
                match formula_eval_at_hole(&mut w, 4, predicate, hi, 0)? {
                    Some(false) => return Ok(false),
                    None => return Ok(false),
                    _ => {}
                }
            }
        }
    }
    Err(refuse(
        name,
        4,
        "enclosure indeterminate at dtype width: the interval endpoints \
         neither witness P at every lower endpoint nor refute it at an upper \
         endpoint under a certified upward-closed predicate — a wider dtype \
         or the exact-lane relation decides"
            .into(),
    ))
}

// ---------------------------------------------------------------------
// Unit checks on the arithmetic substrate (the batteries live in
// tests/berncone.rs; these pin the combinatorial floor).
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn choose_and_multinomial() {
        assert_eq!(nchoose(5, 2), BigUint::from(10u32));
        assert_eq!(nchoose(0, 0), BigUint::one());
        assert_eq!(nchoose(3, 5), BigUint::zero());
        assert_eq!(multinomial(&[]), BigUint::one());
        assert_eq!(multinomial(&[2, 1]), BigUint::from(3u32));
        assert_eq!(multinomial(&[1, 1, 1]), BigUint::from(6u32));
        assert_eq!(multinomial(&[0, 2]), BigUint::one());
    }

    #[test]
    fn composition_grids() {
        let mut b = Budget::new();
        let c = compositions("t", 2, 2, &mut b).unwrap();
        assert_eq!(c, vec![vec![0, 2], vec![1, 1], vec![2, 0]]);
        let up = compositions_up_to("t", 2, 1, &mut b).unwrap();
        assert_eq!(up, vec![vec![0, 0], vec![0, 1], vec![1, 0]]);
        let sub = sub_compositions("t", &[1, 2], &mut b).unwrap();
        assert_eq!(sub.len(), 6);
        assert!(sub.contains(&vec![1, 2]) && sub.contains(&vec![0, 0]));
        // parts = 0: exactly the empty composition at total 0.
        assert_eq!(
            compositions("t", 0, 0, &mut b).unwrap(),
            vec![Vec::<u64>::new()]
        );
        assert!(compositions("t", 0, 3, &mut b).unwrap().is_empty());
    }

    #[test]
    fn assemble_interleaves() {
        assert_eq!(
            assemble_vec(&[true, false, true, false], &[7, 8], &[1, 2]),
            vec![7, 1, 8, 2]
        );
        assert_eq!(assemble_vec(&[false, false], &[], &[3]), vec![3, 0]);
    }

    /// The executable demo's branch-B table by hand: p = 1/2 + 2·x on
    /// [1, 2], degree 1, S = ∅ — grid coefficients {5/2, 9/2}.
    #[test]
    fn fd_grid_matches_the_demo_by_hand() {
        let coords = vec![vec![q(1, 1)], vec![q(2, 1)]];
        let smask = vec![false, false];
        // p over coordinate 0: 1/2 + 2·x₀.
        let mut p = QPoly::constant(q(1, 2));
        p = p.add(&QPoly::var(0).scale(&q(2, 1)));
        let mut b = Budget::new();
        let grid = fd_bernstein_grid("t", &coords, &smask, 1, &p, &mut b)
            .unwrap()
            .expect("constructible");
        let mut got: Vec<QQ> = grid;
        got.sort_by(|a, b| a.cmp_qq(b));
        assert_eq!(got, vec![q(5, 2), q(9, 2)]);
    }

    /// Degree lie: x² at degree 1 is `None`, never truncated.
    #[test]
    fn degree_lie_rejects() {
        let coords = vec![vec![q(1, 1)], vec![q(2, 1)]];
        let smask = vec![false, false];
        let p = QPoly::var(0).mul(&QPoly::var(0));
        let mut b = Budget::new();
        assert_eq!(
            fd_bernstein_grid("t", &coords, &smask, 1, &p, &mut b).unwrap(),
            None
        );
    }

    /// Empty core face (`mB = 0`) is `None`.
    #[test]
    fn empty_core_face_rejects() {
        let coords = vec![vec![q(1, 1)], vec![q(2, 1)]];
        let smask = vec![true, true];
        let p = QPoly::constant(q(1, 1));
        let mut b = Budget::new();
        assert_eq!(
            fd_bernstein_grid("t", &coords, &smask, 1, &p, &mut b).unwrap(),
            None
        );
    }
}
