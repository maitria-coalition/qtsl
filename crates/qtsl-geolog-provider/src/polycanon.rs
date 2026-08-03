//! `qtsl_poly_canonical`: the Poly canonical-form receipt as a
//! row-context recompute — the system-spec family's first evaluator.
//!
//! Semantic authority: the Qtsl theory's Poly block (`Qtsl.geolog`
//! ll.157–165 — declaration comment + `qtsl_poly_canonical` decl) and
//! carillon's `manifest.Poly` canonical representation (the frozen
//! spec's "carillon's sort order": `Poly.make` stores
//! `tuple(sorted(...))` of the nonzero-coefficient exponent-tuple
//! dict — Python tuple sort, i.e. LEXICOGRAPHIC ASCENDING on the
//! dense exponent tuple, strictly (dict keys are unique)). The
//! kindred relation is `polynomialCanonicalEq`'s canonical-form class
//! ([`crate::qpoly`] mirrors the same laws in sparse-`Mono` dress for
//! the applicability family; THIS relation checks the stored dense
//! form, so the two representations stay injective images of the
//! same monomial → coefficient function).
//!
//! The check's obligations, from the declaration comment — no more,
//! no less:
//!
//! 1. **coeffs nonzero** — every `pTerm/coeff` is a nonzero exact-ℚ
//!    literal (ℚ-cell representation-canonicality is the ground
//!    invariant, not re-adjudicated here);
//! 2. **uniform exponent width** — every `pTerm/expts` Shape literal
//!    has one common length (the dense-tuple discipline: a Poly's
//!    monomials all live in the same variable box);
//! 3. **strictly increasing** — consecutive exponent tuples ascend
//!    strictly in lexicographic order (strict is load-bearing: a
//!    duplicate monomial is mergeable content, hence non-canonical —
//!    the opposite polarity from `qtsl_bag_canon`'s non-strict
//!    multiset order, where duplicates ARE content).
//!
//! `pZero` is the zero polynomial: the empty term list satisfies all
//! three obligations vacuously.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::bagcanon`]): a decided violation is `Ok(false)` — named
//! via [`PolyCanonViolation`] for callers that want the reason — and
//! anything the row context cannot decide (unconstructed or ambiguous
//! elements, exhausted budgets) REFUSES, never guesses.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The poly-canonicality family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] =
    &[("qtsl_poly_canonical", &[("p", "Poly")], RelKind::PolyCanon)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const POLYCANON_MAX_TERMS: usize = 1 << 16;
pub const POLYCANON_MAX_WIDTH: usize = 1 << 10;

/// The Poly constructor vocabulary, pinned at vocabulary resolution
/// (names select, shapes verify, identities pin — the
/// `build_bagcanon_vocab` pattern).
#[derive(Debug, Clone)]
pub struct PolyCanonVocab {
    p_zero: Chid,
    p_term: Chid,
    poly_sort: Chid,
    /// The Poly sort's constructor roster: fun chid → domain — so
    /// "constructed by something outside the expected pair" is a
    /// definite malformation, distinct from "not constructed in
    /// view" (refusal).
    ctors: HashMap<Chid, DomainSig>,
}

/// Build the Poly vocabulary for the named sort. `Err` → the family
/// is not claimed (C-ORACLE safe-fail; reason recorded on the
/// provider's vocabulary notes).
pub fn build_polycanon_vocab(
    indices: &[&TheoryIndex],
    poly_sort: Chid,
) -> Result<PolyCanonVocab, String> {
    let find =
        |name: &str, check: &dyn Fn(&DomainSig) -> Result<(), String>| -> Result<Chid, String> {
            for index in indices {
                let Some(d) = index.fun(name) else { continue };
                if d.relational || d.codomain != Some(SortKey::Elem(poly_sort)) {
                    return Err(format!(
                        "`{name}` is not a constructor of the expected sort \
                     (wrong kind or codomain)"
                    ));
                }
                check(&d.domain).map_err(|why| format!("`{name}`: {why}"))?;
                return Ok(d.chid);
            }
            Err(format!("no `{name}` constructor among the swept revisions"))
        };

    let p_zero = find("pZero", &|s| {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    })?;
    let p_term = find("pTerm", &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(c, SortKey::Ground(Ground::Q)), (e, SortKey::Ground(Ground::Shape)), (t, SortKey::Elem(ts))]
                if c == "coeff" && e == "expts" && t == "tail" && *ts == poly_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (coeff: Q, expts: Shape, tail: Poly)".into()),
        }
    })?;

    let mut ctors: HashMap<Chid, DomainSig> = HashMap::new();
    for index in indices {
        for decl in &index.funs {
            if decl.relational || decl.name.contains('/') {
                continue;
            }
            if decl.codomain == Some(SortKey::Elem(poly_sort)) {
                ctors.insert(decl.chid, decl.domain.clone());
            }
        }
    }

    Ok(PolyCanonVocab {
        p_zero,
        p_term,
        poly_sort,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The decoded value (pure data — the core checks run on this, so tests
// hit the combinatorics directly)
// ---------------------------------------------------------------------

/// A decoded stored Poly: the term list IN STORED ORDER — decode is
/// deliberately order- and content-preserving (no merging, no
/// zero-dropping): representation canonicality is exactly what this
/// relation adjudicates, so the decoder must not repair it (contrast
/// [`crate::miranda`]'s accumulating `poly` walk, which reads content
/// and leaves canonicality to THIS oracle).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredPoly {
    /// `(expts, coeff)` per `pTerm`, head-first (stored order).
    pub terms: Vec<(Vec<u64>, QQ)>,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is an obligation the declaration comment
/// names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolyCanonViolation {
    /// Term `term` carries a zero coefficient (droppable content —
    /// non-canonical).
    ZeroCoeff { term: usize },
    /// Term `term`'s exponent tuple width disagrees with term 0's.
    WidthMismatch {
        term: usize,
        got: usize,
        want: usize,
    },
    /// Term `term`'s exponent tuple is not lexicographically STRICTLY
    /// below its successor's (equal = mergeable duplicate; greater =
    /// unsorted) — the stored list is not carillon's canonical order.
    TermsUnsorted { term: usize },
}

impl std::fmt::Display for PolyCanonViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolyCanonViolation::ZeroCoeff { term } => {
                write!(f, "term {term} carries a zero coefficient")
            }
            PolyCanonViolation::WidthMismatch { term, got, want } => {
                write!(
                    f,
                    "term {term}: exponent width {got} against the polynomial's \
                     width {want}"
                )
            }
            PolyCanonViolation::TermsUnsorted { term } => {
                write!(
                    f,
                    "term {term} is not lexicographically strictly below its \
                     successor — not carillon's canonical order"
                )
            }
        }
    }
}

/// The full canonical-form check on a decoded value. `Err` = refusal
/// (budgets); `Ok(Err(v))` = decided false with the named violation;
/// `Ok(Ok(()))` = accept.
pub fn check_poly_canonical(p: &StoredPoly) -> Result<Result<(), PolyCanonViolation>, String> {
    if p.terms.len() > POLYCANON_MAX_TERMS {
        return Err(format!(
            "term count beyond the polynomial budget ({POLYCANON_MAX_TERMS}) — refusing"
        ));
    }
    // 1. coeffs nonzero.
    for (ti, (_, c)) in p.terms.iter().enumerate() {
        if c.is_zero() {
            return Ok(Err(PolyCanonViolation::ZeroCoeff { term: ti }));
        }
    }
    // 2. uniform exponent width.
    if let Some((first, _)) = p.terms.first() {
        if first.len() > POLYCANON_MAX_WIDTH {
            return Err(format!(
                "exponent width beyond the variable budget ({POLYCANON_MAX_WIDTH}) — refusing"
            ));
        }
        let want = first.len();
        for (ti, (e, _)) in p.terms.iter().enumerate().skip(1) {
            if e.len() != want {
                return Ok(Err(PolyCanonViolation::WidthMismatch {
                    term: ti,
                    got: e.len(),
                    want,
                }));
            }
        }
    }
    // 3. strictly increasing in carillon's sort order (lex ascending
    // on the now-equal-width dense tuples; strict — equal adjacent is
    // a mergeable duplicate).
    for (ti, w) in p.terms.windows(2).enumerate() {
        if w[0].0 >= w[1].0 {
            return Ok(Err(PolyCanonViolation::TermsUnsorted { term: ti }));
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// Row-context decode
// ---------------------------------------------------------------------

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// Decode the relation argument into a [`StoredPoly`] (exposed so
/// tests hit the combinatorics directly). Args in wire field order:
/// `p` (same-body element ref).
///
/// `Err(EvalError)` = refusal — row-context undecidability; decided
/// content lives in [`check_poly_canonical`].
pub fn decode_stored_poly(
    name: &str,
    v: &PolyCanonVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<StoredPoly, EvalError> {
    let elem = |val: &Value| -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => rows.local(r).ok_or_else(|| {
                ctx_err(
                    name,
                    0,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: name.into(),
                index: 0,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    };
    let sole = |e: u32| -> Result<&crate::rowctx::CtorRow, EvalError> {
        let mut found: Option<&crate::rowctx::CtorRow> = None;
        for row in rows.producers(e) {
            if !v.ctors.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    name,
                    0,
                    format!(
                        "element {e} is produced by multiple constructor rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            ctx_err(
                name,
                0,
                format!(
                    "element {e} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    };

    let mut terms: Vec<(Vec<u64>, QQ)> = Vec::new();
    let mut visited: HashSet<u32> = HashSet::new();
    let mut cur = elem(args[0])?;
    loop {
        if !visited.insert(cur) {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} recurs along its own term tail (P-ACYCLIC \
                     territory) — refusing"
                ),
            ));
        }
        if terms.len() > POLYCANON_MAX_TERMS {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "term walk beyond the polynomial budget ({POLYCANON_MAX_TERMS}) — \
                     pathological rows"
                ),
            ));
        }
        let row = sole(cur)?;
        if row.fun == v.p_zero {
            break;
        }
        if row.fun != v.p_term {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} is constructed by a fun outside the expected \
                     pZero/pTerm pair — malformed rows"
                ),
            ));
        }
        let [coeff, expts, tail] = row.args.as_slice() else {
            return Err(ctx_err(name, 0, "pTerm row arity mismatch".into()));
        };
        let c = match coeff {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                ctx_err(
                    name,
                    0,
                    "`pTerm/coeff` is not an exact-Q literal — malformed rows".into(),
                )
            })?,
            _ => {
                return Err(ctx_err(
                    name,
                    0,
                    "`pTerm/coeff` is not a literal cell — malformed rows".into(),
                ))
            }
        };
        let e: Vec<u64> = match expts {
            Value::Lit(l) => match l.view() {
                LiteralView::Shape(s) => s.iter().collect(),
                _ => {
                    return Err(ctx_err(
                        name,
                        0,
                        "`pTerm/expts` is not a Shape literal — malformed rows".into(),
                    ))
                }
            },
            _ => {
                return Err(ctx_err(
                    name,
                    0,
                    "`pTerm/expts` is not a literal cell — malformed rows".into(),
                ))
            }
        };
        terms.push((e, c));
        cur = elem(tail)?;
    }

    // Silence the "sort recorded but consumed only at build" lint
    // honestly: the sort identity IS consumed, at roster construction.
    let _ = v.poly_sort;
    Ok(StoredPoly { terms })
}

/// Decode + check: the `qtsl_poly_canonical` evaluation.
pub fn eval_poly_canonical(
    name: &str,
    v: &PolyCanonVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let p = decode_stored_poly(name, v, args, rows)?;
    match check_poly_canonical(&p) {
        Ok(Ok(())) => Ok(true),
        Ok(Err(_violation)) => Ok(false),
        Err(why) => Err(EvalError::CtxArg {
            name: name.into(),
            index: 0,
            why,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn poly(terms: &[(&[u64], (i64, u64))]) -> StoredPoly {
        StoredPoly {
            terms: terms
                .iter()
                .map(|(e, (n, d))| (e.to_vec(), q(*n, *d)))
                .collect(),
        }
    }

    #[test]
    fn zero_poly_accepts() {
        // pZero: the empty term list, every obligation vacuous.
        assert!(matches!(check_poly_canonical(&poly(&[])), Ok(Ok(()))));
    }

    #[test]
    fn canonical_accepts() {
        // 1/2 + 3·x₁ − x₀²x₁ over two variables: (0,0) < (0,1) < (2,1).
        let p = poly(&[(&[0, 0], (1, 2)), (&[0, 1], (3, 1)), (&[2, 1], (-1, 1))]);
        assert!(matches!(check_poly_canonical(&p), Ok(Ok(()))));
    }

    #[test]
    fn nullary_width_accepts() {
        // A constant polynomial over zero variables: one term, empty
        // exponent tuple.
        let p = poly(&[(&[], (5, 3))]);
        assert!(matches!(check_poly_canonical(&p), Ok(Ok(()))));
    }

    #[test]
    fn zero_coeff_rejects() {
        let p = poly(&[(&[0], (0, 1)), (&[1], (2, 1))]);
        assert_eq!(
            check_poly_canonical(&p).unwrap().unwrap_err(),
            PolyCanonViolation::ZeroCoeff { term: 0 }
        );
    }

    #[test]
    fn width_mismatch_rejects() {
        let p = poly(&[(&[0, 0], (1, 1)), (&[1], (2, 1))]);
        assert_eq!(
            check_poly_canonical(&p).unwrap().unwrap_err(),
            PolyCanonViolation::WidthMismatch {
                term: 1,
                got: 1,
                want: 2
            }
        );
    }

    #[test]
    fn unsorted_rejects() {
        let p = poly(&[(&[1, 0], (1, 1)), (&[0, 1], (2, 1))]);
        assert_eq!(
            check_poly_canonical(&p).unwrap().unwrap_err(),
            PolyCanonViolation::TermsUnsorted { term: 0 }
        );
    }

    #[test]
    fn duplicate_monomial_rejects() {
        // Equal adjacent exponent tuples: mergeable content — strict
        // order is load-bearing (contrast the Bag's non-strict order).
        let p = poly(&[(&[1, 1], (1, 1)), (&[1, 1], (2, 1))]);
        assert_eq!(
            check_poly_canonical(&p).unwrap().unwrap_err(),
            PolyCanonViolation::TermsUnsorted { term: 0 }
        );
    }

    #[test]
    fn lex_tiebreak_is_positional() {
        // (0,2) < (1,0): first coordinate decides before the second.
        let p = poly(&[(&[0, 2], (1, 1)), (&[1, 0], (2, 1))]);
        assert!(matches!(check_poly_canonical(&p), Ok(Ok(()))));
    }

    #[test]
    fn violation_order_checks_coeffs_first() {
        // A poly violating all three obligations names the zero
        // coefficient (obligation order fixed for test determinism).
        let p = poly(&[(&[1], (0, 1)), (&[0, 0], (1, 1)), (&[0, 0], (1, 1))]);
        assert!(matches!(
            check_poly_canonical(&p).unwrap().unwrap_err(),
            PolyCanonViolation::ZeroCoeff { term: 0 }
        ));
    }
}
