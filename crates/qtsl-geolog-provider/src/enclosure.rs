//! The enclosure family: `enclosureWitnessValid` — the remainder-bound
//! witness check, evaluated over rows.
//!
//! One relation, **`enclosureWitnessValid [j: EncJudgment]`**: the
//! judgment element carries a claimed enclosure — a function tag
//! (`EncJudgment/func`: 0 = exp, 1 = sin, 2 = cos), a truncation
//! degree (`EncJudgment/n`), a radius (`EncJudgment/r`), and a
//! remainder cap (`EncJudgment/cap`) — asserting that on `|x| <= r`
//! the tagged function is enclosed by its degree-`n` Maclaurin prefix
//! to within the cap. The relation holds exactly when the checker
//! obligations hold, in exact rational arithmetic:
//!
//! - **coefficients** — the Maclaurin prefix is recomputed from the
//!   tag's exact recurrence (`a^exp_k = 1/k!`; `a^sin_k = 0` even,
//!   `(-1)^((k-1)/2)/k!` odd; `a^cos_k` dually). The prefix is never
//!   stored: the judgment determines it, so at row grain this clause
//!   holds by the recompute itself — the recompute is nonetheless
//!   EXECUTED, not assumed, and its running factorial is exactly the
//!   `(n+1)!` the tail clause consumes.
//! - **radius** — `0 <= r` and `r < n + 2` (strict: the geometric
//!   guard of the tail argument).
//! - **tail cap** — `tail(n, r) = r^(n+1)/(n+1)! * (n+2)/((n+2)-r)
//!   <= cap`, decided by cross-multiplication (both denominators are
//!   strictly positive once the radius clause holds, so no rational
//!   division is ever performed).
//!
//! Semantic authority: `encCheck` and its soundness theorem
//! `encCheck_sound` (`lean/qtsl-aux/QtslAux/Enclosure.lean` — an
//! accepted witness satisfies `|f x - poly x| <= cap` for all
//! `|x| <= r`), with the HOL4 development
//! (`hol/checker/qtsl_enclosureScript.sml`) as the second tower. The
//! Lean file's kernel-decided examples are this module's golden
//! anchors, and all three accepts sit EXACTLY at the tail bound —
//! they pin the `<=` boundary itself.
//!
//! # Adjudicated boundaries
//!
//! - **Unknown function tags refuse.** The witness type has exactly
//!   three inhabitants (the Lean `FnTag`), and the certificate wire
//!   format rejects `func > 2` at parse. A row claiming a fourth
//!   function corresponds to no representable witness — refusal, the
//!   same posture as out-of-domain index values elsewhere in the
//!   crate. (The python model-level twin, which has no refusal
//!   channel, renders the same tag as a failure; the frozen corpus
//!   therefore carries in-domain tags only.)
//! - **The verdict is tag-independent.** The tail majorant is the
//!   uniform `|a_k| <= 1/k!` bound, so once a tag is representable
//!   the decided verdict depends only on `(n, r, cap)`. The corpus
//!   spans all three tags to witness the invariance; the per-tag
//!   content lives in the coefficient recompute, pinned against the
//!   Lean lists in the battery.
//!
//! Verdict discipline (the crate's): a decided violation of the
//! radius or tail clause is `Ok(false)`; missing or conflicting field
//! rows, non-literal or non-canonical values, external references,
//! unknown tags, and degrees beyond the budget REFUSE with a reason,
//! never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::{BigInt, BigUint};

const F_ENC: &[(&str, &str)] = &[("j", "EncJudgment")];

/// The enclosure family's row of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[("enclosureWitnessValid", F_ENC, RelKind::Enclosure)];

/// Degree budget: refusal beyond, never divergence. The factorial and
/// power computations are polynomial in the degree, and no honest
/// witness needs a fraction of this (the tail shrinks factorially).
pub const ENC_MAX_DEGREE: u64 = 1 << 12;

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// The enclosure family's resolved vocabulary: the four `EncJudgment`
/// field identities, name-selected once at construction and
/// shape-verified (names select, shapes verify, identities pin).
#[derive(Debug, Clone)]
pub struct EncVocab {
    enc_func: Chid,
    enc_n: Chid,
    enc_r: Chid,
    enc_cap: Chid,
}

/// Build the enclosure vocabulary over the declared indices. `Err` →
/// the family is not claimed (declared-but-unbound, safe-fail).
pub fn build_enclosure_vocab(indices: &[&TheoryIndex]) -> Result<EncVocab, String> {
    let enc_sort = crate::formrows::find_sort(indices, "EncJudgment")?;

    // A unary field on the judgment sort with a verified ground
    // codomain.
    let field = |name: &str, cod: Ground| -> Result<Chid, String> {
        let c = crate::formrows::find_field(indices, name, enc_sort)?;
        for index in indices {
            if let Some(d) = index.fun_by_chid(c) {
                if d.relational
                    || d.codomain != Some(SortKey::Ground(cod))
                    || d.domain != DomainSig::Unary(SortKey::Elem(enc_sort))
                {
                    return Err(format!(
                        "`{name}` does not have the expected field shape \
                         (unary fun on `EncJudgment` with the expected ground codomain)"
                    ));
                }
                return Ok(c);
            }
        }
        Err(format!(
            "`{name}` resolved but is not indexed — malformed sweep"
        ))
    };

    Ok(EncVocab {
        enc_func: field("EncJudgment/func", Ground::Nat)?,
        enc_n: field("EncJudgment/n", Ground::Nat)?,
        enc_r: field("EncJudgment/r", Ground::Q)?,
        enc_cap: field("EncJudgment/cap", Ground::Q)?,
    })
}

// ---------------------------------------------------------------------
// The exact arithmetic (the Lean twin)
// ---------------------------------------------------------------------

/// The three representable function tags, in wire order (the Lean
/// `FnTag` roster; the wire format rejects any other value at parse).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncTag {
    Exp,
    Sin,
    Cos,
}

impl EncTag {
    /// Wire tag → `EncTag`; `None` outside the three-element roster.
    pub fn from_wire(tag: u64) -> Option<EncTag> {
        match tag {
            0 => Some(EncTag::Exp),
            1 => Some(EncTag::Sin),
            2 => Some(EncTag::Cos),
            _ => None,
        }
    }
}

/// The recomputed Maclaurin prefix `(a_0, ..., a_n)` of the tagged
/// function, plus the running factorial's final value `(n+1)!` — the
/// exact quantity the tail clause consumes, produced by the same
/// recurrence that produced the coefficients. Transcribes the Lean
/// `maclaurin` (`a^exp_k = 1/k!`; `a^sin_k` nonzero at odd `k` with
/// sign `(-1)^((k-1)/2)`; `a^cos_k` nonzero at even `k` with sign
/// `(-1)^(k/2)`).
pub fn maclaurin_prefix(tag: EncTag, n: u64) -> (Vec<QQ>, BigUint) {
    let mut coeffs = Vec::with_capacity(n as usize + 1);
    let mut fact = BigUint::from(1u32); // k! for the current k
    for k in 0..=n {
        if k > 0 {
            fact *= k;
        }
        let signed_unit = |negative: bool| -> BigInt {
            if negative {
                BigInt::from(-1)
            } else {
                BigInt::from(1)
            }
        };
        let c = match tag {
            EncTag::Exp => QQ::new(BigInt::from(1), fact.clone()),
            EncTag::Sin => {
                if k % 2 == 1 {
                    QQ::new(signed_unit(((k - 1) / 2) % 2 == 1), fact.clone())
                } else {
                    QQ::zero()
                }
            }
            EncTag::Cos => {
                if k % 2 == 0 {
                    QQ::new(signed_unit((k / 2) % 2 == 1), fact.clone())
                } else {
                    QQ::zero()
                }
            }
        };
        coeffs.push(c);
    }
    fact *= n + 1; // (n+1)!
    (coeffs, fact)
}

/// `r^e` by square-and-multiply (exact; `e <= ENC_MAX_DEGREE + 1`).
fn qq_pow(r: &QQ, mut e: u64) -> QQ {
    let mut base = r.clone();
    let mut acc = QQ::one();
    while e > 0 {
        if e & 1 == 1 {
            acc = acc.mul(&base);
        }
        e >>= 1;
        if e > 0 {
            base = base.mul(&base);
        }
    }
    acc
}

/// The tail clause, `tail(n, r) <= cap`, decided WITHOUT rational
/// division: with `0 <= r < n + 2` (the radius clause, checked by the
/// caller), both `(n+1)!` and `(n+2) - r` are strictly positive, so
///
/// ```text
/// r^(n+1)/(n+1)! * (n+2)/((n+2)-r) <= cap
///     <=>  r^(n+1) * (n+2)  <=  cap * (n+1)! * ((n+2) - r)
/// ```
///
/// — an exact cross-multiplied comparison in `QQ`.
pub fn tail_le_cap(n: u64, r: &QQ, cap: &QQ, fact_n1: &BigUint) -> bool {
    let n_plus_2 = QQ::from_int(n as i64 + 2);
    let lhs = qq_pow(r, n + 1).mul(&n_plus_2);
    let fact = QQ::new(BigInt::from(fact_n1.clone()), BigUint::from(1u32));
    let rhs = cap.mul(&fact).mul(&n_plus_2.sub(r));
    lhs.cmp_qq(&rhs) != std::cmp::Ordering::Greater
}

// ---------------------------------------------------------------------
// Row decoding + dispatch
// ---------------------------------------------------------------------

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// The unique field row `fun(j) = value`: missing is a refusal
/// (structure undecidable), multiplicity is a refusal (never picking).
fn sole_field<'a>(
    name: &str,
    rows: &'a CertRows,
    j: u32,
    fun: Chid,
    what: &str,
) -> Result<&'a CtorRow, EvalError> {
    let mut found: Option<&CtorRow> = None;
    for row in rows.arg_rows(j) {
        if row.fun != fun {
            continue;
        }
        if found.is_some() {
            return Err(ctx_err(
                name,
                0,
                format!("judgment element {j} has multiple `{what}` rows — never picking"),
            ));
        }
        found = Some(row);
    }
    found.ok_or_else(|| {
        ctx_err(
            name,
            0,
            format!("judgment element {j} has no `{what}` row — structure undecidable"),
        )
    })
}

fn field_nat(name: &str, rows: &CertRows, j: u32, fun: Chid, what: &str) -> Result<u64, EvalError> {
    let row = sole_field(name, rows, j, fun, what)?;
    let Value::Lit(l) = &row.value else {
        return Err(ctx_err(
            name,
            0,
            format!("`{what}` value is not a literal cell"),
        ));
    };
    let LiteralView::Nat(n) = l.view() else {
        return Err(ctx_err(
            name,
            0,
            format!("`{what}` value is not a Nat literal"),
        ));
    };
    Ok(n)
}

fn field_q(name: &str, rows: &CertRows, j: u32, fun: Chid, what: &str) -> Result<QQ, EvalError> {
    let row = sole_field(name, rows, j, fun, what)?;
    let Value::Lit(l) = &row.value else {
        return Err(ctx_err(
            name,
            0,
            format!("`{what}` value is not a literal cell"),
        ));
    };
    QQ::from_q_literal(l)
        .ok_or_else(|| ctx_err(name, 0, format!("`{what}` value is not a Q literal")))
}

/// Evaluate `enclosureWitnessValid [j]`: decode the judgment's four
/// fields, then decide the radius and tail clauses exactly.
pub(crate) fn eval_enclosure_witness_valid(
    name: &str,
    v: &EncVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let j = elem_local(name, 0, args[0], rows)?;

    let func = field_nat(name, rows, j, v.enc_func, "EncJudgment/func")?;
    let n = field_nat(name, rows, j, v.enc_n, "EncJudgment/n")?;
    let r = field_q(name, rows, j, v.enc_r, "EncJudgment/r")?;
    let cap = field_q(name, rows, j, v.enc_cap, "EncJudgment/cap")?;

    // The function roster has exactly three inhabitants; the wire
    // format rejects a fourth tag at parse, so such a row corresponds
    // to no representable witness — refusal, never a guess.
    let Some(tag) = EncTag::from_wire(func) else {
        return Err(ctx_err(
            name,
            0,
            format!(
                "`EncJudgment/func` value {func} is outside the three-tag function \
                 roster (0 = exp, 1 = sin, 2 = cos) — no representable witness"
            ),
        ));
    };
    if n > ENC_MAX_DEGREE {
        return Err(ctx_err(
            name,
            0,
            format!("degree {n} exceeds the enclosure degree budget ({ENC_MAX_DEGREE})"),
        ));
    }

    // Radius clause: 0 <= r, strictly below n + 2 (the geometric
    // guard). Decided content.
    if !r.is_nonneg() {
        return Ok(false);
    }
    let n_plus_2 = QQ::from_int(n as i64 + 2);
    if r.cmp_qq(&n_plus_2) != std::cmp::Ordering::Less {
        return Ok(false);
    }

    // Coefficient clause: the prefix is determined by (tag, n) and
    // never stored, so equality holds by this very recompute — which
    // is EXECUTED, and whose running factorial is the exact `(n+1)!`
    // the tail clause consumes.
    let (coeffs, fact_n1) = maclaurin_prefix(tag, n);
    debug_assert_eq!(coeffs.len() as u64, n + 1);

    // Tail clause, cross-multiplied.
    Ok(tail_le_cap(n, &r, &cap, &fact_n1))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(num: i64, den: u64) -> QQ {
        QQ::new(BigInt::from(num), BigUint::from(den))
    }

    /// The Lean file's coefficient lists, verbatim (the kernel-decided
    /// accept examples' `coeffs` fields).
    #[test]
    fn maclaurin_prefix_matches_lean_anchors() {
        let (sin7, fact) = maclaurin_prefix(EncTag::Sin, 7);
        assert_eq!(
            sin7,
            vec![
                q(0, 1),
                q(1, 1),
                q(0, 1),
                q(-1, 6),
                q(0, 1),
                q(1, 120),
                q(0, 1),
                q(-1, 5040)
            ]
        );
        assert_eq!(fact, BigUint::from(40320u64)); // 8!

        let (exp4, fact) = maclaurin_prefix(EncTag::Exp, 4);
        assert_eq!(exp4, vec![q(1, 1), q(1, 1), q(1, 2), q(1, 6), q(1, 24)]);
        assert_eq!(fact, BigUint::from(120u64)); // 5!

        let (cos6, fact) = maclaurin_prefix(EncTag::Cos, 6);
        assert_eq!(
            cos6,
            vec![
                q(1, 1),
                q(0, 1),
                q(-1, 2),
                q(0, 1),
                q(1, 24),
                q(0, 1),
                q(-1, 720)
            ]
        );
        assert_eq!(fact, BigUint::from(5040u64)); // 7!
    }

    /// All three Lean accepts sit exactly at the bound:
    /// `tail(7, 1) = 1/35840`, `tail(4, 1/2) = 1/3520`,
    /// `tail(6, 1) = 1/4410`. The cross-multiplied comparison must
    /// accept AT the bound and reject one hair below it.
    #[test]
    fn tail_boundary_is_inclusive_and_exact() {
        let cases: &[(u64, QQ, u64, u64)] = &[
            (7, q(1, 1), 1, 35840),
            (4, q(1, 2), 1, 3520),
            (6, q(1, 1), 1, 4410),
        ];
        for (n, r, cn, cd) in cases {
            let (_, fact) = maclaurin_prefix(EncTag::Exp, *n);
            let exact = q(*cn as i64, *cd);
            assert!(tail_le_cap(*n, r, &exact, &fact), "at the bound: n={n}");
            // One hair below: cap * (1 - 10^-9).
            let hair = exact.mul(&q(999_999_999, 1_000_000_000));
            assert!(!tail_le_cap(*n, r, &hair, &fact), "below the bound: n={n}");
            // One hair above.
            let above = exact.mul(&q(1_000_000_001, 1_000_000_000));
            assert!(tail_le_cap(*n, r, &above, &fact), "above the bound: n={n}");
        }
    }

    /// `tail(n, 0) = 0`: the zero-radius witness is enclosed by any
    /// nonnegative cap, including zero.
    #[test]
    fn zero_radius_zero_tail() {
        let (_, fact) = maclaurin_prefix(EncTag::Cos, 0);
        assert!(tail_le_cap(0, &QQ::zero(), &QQ::zero(), &fact));
        assert!(!tail_le_cap(0, &QQ::zero(), &q(-1, 1_000_000), &fact));
    }

    #[test]
    fn pow_is_exact() {
        assert_eq!(qq_pow(&q(2, 3), 5), q(32, 243));
        assert_eq!(qq_pow(&q(-1, 2), 3), q(-1, 8));
        assert_eq!(qq_pow(&q(7, 1), 0), QQ::one());
    }

    #[test]
    fn wire_tag_roster_is_three() {
        assert_eq!(EncTag::from_wire(0), Some(EncTag::Exp));
        assert_eq!(EncTag::from_wire(1), Some(EncTag::Sin));
        assert_eq!(EncTag::from_wire(2), Some(EncTag::Cos));
        assert_eq!(EncTag::from_wire(3), None);
        assert_eq!(EncTag::from_wire(u64::MAX), None);
    }
}
