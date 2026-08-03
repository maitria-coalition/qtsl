//! The predicate semantic-class family: `isConicPredicate`,
//! `isConvexPredicate`, `isUpwardClosedConicPredicate` — bounded
//! syntactic classification of a predicate `Formula`'s satisfying set.
//!
//! Spec authority: the Lean catalogue (`Core/Catalogue.lean`) —
//! `parseHoleSide`, `Term.evalQ?`, `classifyPredAtom`, `classifyPred`,
//! and the three Props defined over the classifier's output:
//!
//! - `isConicPredicate P := (classifyPred P).map (·.conic) = some true`
//! - `isConvexPredicate P := (classifyPred P).isSome`
//! - `isUpwardClosedConicPredicate P :=
//!      (classifyPred P).map (fun c => c.conic && c.upClosed) = some true`
//!
//! `classifyPred` is TOTAL on the Lean `Formula`: it recognizes a
//! closed-world fragment (single-atom rays and their positive literal
//! scalings, `= 0` kernels, and finite conjunctions thereof) and
//! returns `none` on everything else. So a decoded formula outside the
//! fragment makes each Prop **false** — the evaluator decides false
//! there, and refusals are reserved for rows that do not resolve to a
//! formula of the Lean grammar at all.
//!
//! # Adjudications (for review eyes)
//!
//! - **Outside-fragment = decided false.** The recognizer is inside
//!   the spec (the Props are equations about `classifyPred`'s output),
//!   so `none` is semantic falsity, not evaluator abstention. All
//!   three relations are consumed positively (the BernCone predicate
//!   guards), so this is also fail-closed.
//! - **`FSpH` in the predicate REFUSES.** The spec-hole formula
//!   constructor exists in the row grammar and the wire model but not
//!   in the Lean `Formula` these Props quantify over; a predicate
//!   containing it has no denotation at the spec's grain (the
//!   unrepresentable-constructor refusal class, kin: the enclosure
//!   family's out-of-roster function tags). The join checkers'
//!   `expandSph` law (spec-hole read as `tt`) is local to the
//!   composition seam and licenses nothing here.
//! - **Genuine wires decide false, not refuse.** A predicate is a
//!   formula over the designated hole only; `parseHoleSide` and
//!   `evalQ?` both return `none` on real wires, so the
//!   hole-only well-formedness condition is enforced by the
//!   recognizer itself.
//!
//! # Spec-grain traps (transcribed, each pinned by battery + corpus)
//!
//! - `evalQ?` is structural constant folding, NOT the polynomial
//!   fold: `0 * w` is a constant under `toPoly` but `evalQ?` returns
//!   `none` on any wire/idx/hole leaf. This module never calls
//!   `to_poly`.
//! - The scaling coefficient is an immediate `TConst` literal (one
//!   `TMul` deep, either operand order, strict `0 < a`); the
//!   comparison side runs full `evalQ?` folding. The asymmetry is the
//!   Lean's.
//! - A constant-left atom re-orients with the bowtie flipped
//!   (`lt <-> gt`, `le <-> ge`, `eq`/`ne` fixed).
//! - The conjunction recursion is `FAnd`-only; `FOr`, `FInRegion`,
//!   `FTrue`, `FFalse` leaves classify `none` (`FTrue` is NOT a
//!   convex predicate — the closed world is deliberate). The walk
//!   rides `conjunct_list` (the crate's `Formula.conjunctList`
//!   mirror), verdict-identical to the binary recursion because `&&`
//!   is associative-commutative and `none` propagates identically.
//!
//! Verdict discipline (the crate's): outside-fragment shapes are
//! `Ok(false)`; unresolvable structure — unconstructed or ambiguous
//! constructor rows, external refs, non-canonical `TConst` literals,
//! cyclic row graphs (node-budget exhaustion), the spec-hole
//! constructor — REFUSES with a reason, never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::formrows::{BlVocab, FormCtor, TermCtor, Walk};
use crate::qq::QQ;
use crate::roster::{EntryRow, PredClassKind, RelKind};
use crate::rowctx::CertRows;
use geolog_envelope::Value;
use std::collections::HashMap;

// Field names + bytewise order are part of the claim (copied from the
// registry's signature column — all three relations are unary on the
// predicate formula).
const F_PREDCLASS: &[(&str, &str)] = &[("predicate", "Formula")];

/// The predicate-class family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Registration order is
/// part of the seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "isConicPredicate",
        F_PREDCLASS,
        RelKind::PredClass(PredClassKind::Conic),
    ),
    (
        "isConvexPredicate",
        F_PREDCLASS,
        RelKind::PredClass(PredClassKind::Convex),
    ),
    (
        "isUpwardClosedConicPredicate",
        F_PREDCLASS,
        RelKind::PredClass(PredClassKind::UpClosedConic),
    ),
];

/// Lean `parseHoleSide`: the hole itself (coefficient 1), or a
/// positive literal scaling of it, one `TMul` deep, either operand
/// order. At row grain the hole is exactly the `THole` constructor
/// (`TVar` references a `Wire` element, which is never the hole:
/// symbol tables are capped below the hole index).
fn parse_hole_side(w: &mut Walk, index: usize, term: u32) -> Result<Option<QQ>, EvalError> {
    let (k, row) = w.term_ctor_row(index, term)?;
    Ok(match k {
        TermCtor::Hole => Some(QQ::one()),
        TermCtor::Mul => {
            let l = w.local(index, &row.args[0])?;
            let r = w.local(index, &row.args[1])?;
            let (kl, row_l) = w.term_ctor_row(index, l)?;
            let (kr, row_r) = w.term_ctor_row(index, r)?;
            let coeff = match (kl, kr) {
                (TermCtor::Const, TermCtor::Hole) => Some(w.const_value(index, row_l)?),
                (TermCtor::Hole, TermCtor::Const) => Some(w.const_value(index, row_r)?),
                _ => None,
            };
            // Strict positivity: `0 < a`. Zero and negative scalings
            // are outside the fragment.
            coeff.filter(|a| a.is_nonneg() && !a.is_zero())
        }
        _ => None,
    })
}

/// Lean `Term.evalQ?`: structural constant folding. `none` on any
/// wire, idx, or hole leaf — deliberately NOT the polynomial fold
/// (`0 * w` must stay unevaluable). Iterative post-order with a memo
/// (row graphs may share elements); cycles exhaust the walk's node
/// budget and refuse there.
fn eval_q(w: &mut Walk, index: usize, root: u32) -> Result<Option<QQ>, EvalError> {
    let mut memo: HashMap<u32, Option<QQ>> = HashMap::new();
    let mut stack = vec![root];
    while let Some(&e) = stack.last() {
        if memo.contains_key(&e) {
            stack.pop();
            continue;
        }
        let (k, row) = w.term_ctor_row(index, e)?;
        match k {
            TermCtor::Var | TermCtor::Idx | TermCtor::Hole => {
                memo.insert(e, None);
                stack.pop();
            }
            TermCtor::Const => {
                let c = w.const_value(index, row)?;
                memo.insert(e, Some(c));
                stack.pop();
            }
            TermCtor::Neg => {
                let u = w.local(index, &row.args[0])?;
                if let Some(v) = memo.get(&u) {
                    let out = v.as_ref().map(QQ::neg);
                    memo.insert(e, out);
                    stack.pop();
                } else {
                    stack.push(u);
                }
            }
            TermCtor::Add | TermCtor::Sub | TermCtor::Mul => {
                let l = w.local(index, &row.args[0])?;
                let r = w.local(index, &row.args[1])?;
                match (memo.get(&l), memo.get(&r)) {
                    (Some(lv), Some(rv)) => {
                        let out = match (lv, rv) {
                            (Some(a), Some(b)) => Some(match k {
                                TermCtor::Add => a.add(b),
                                TermCtor::Sub => a.sub(b),
                                _ => a.mul(b),
                            }),
                            _ => None,
                        };
                        memo.insert(e, out);
                        stack.pop();
                    }
                    _ => {
                        stack.push(r);
                        stack.push(l);
                    }
                }
            }
        }
    }
    Ok(memo.remove(&root).expect("folded"))
}

/// Bowtie codes: 0=LT 1=LE 2=EQ 3=GE 4=GT 5=NE (the design source).
/// Re-orientation for a constant-left atom flips the strict/large
/// pairs and fixes eq/ne.
fn flip_bowtie(b: u8) -> u8 {
    match b {
        0 => 4,
        1 => 3,
        3 => 1,
        4 => 0,
        other => other, // eq, ne
    }
}

/// Lean `classifyPredAtom` on one conjunct leaf:
/// `Some((conic, upClosed))` for recognized rays, `None` outside the
/// fragment. The caller has already peeled `FAnd` nodes.
fn classify_atom(w: &mut Walk, index: usize, form: u32) -> Result<Option<(bool, bool)>, EvalError> {
    let (k, row) = w.form_ctor_row(index, form)?;
    let b = match k {
        FormCtor::Atom(b) => b,
        FormCtor::SpH => {
            return Err(w.refuse(
                index,
                "the spec-hole formula constructor has no projection into the \
                 Lean predicate grammar — unclassifiable structure"
                    .into(),
            ))
        }
        // FTrue / FFalse / FOr / FInRegion: representable in the Lean
        // grammar, outside the recognized fragment — classify none.
        _ => return Ok(None),
    };
    let l = w.local(index, &row.args[0])?;
    let r = w.local(index, &row.args[1])?;
    // Orientation: hole side left first; on PATTERN failure (either
    // half unparseable) try the flipped reading. `parseHoleSide`'s
    // coefficient is checked for shape only here — the classified
    // constant is the OTHER side's `evalQ?` value.
    let oriented: Option<(u8, QQ)> = match (parse_hole_side(w, index, l)?, eval_q(w, index, r)?) {
        (Some(_), Some(c)) => Some((b, c)),
        _ => match (parse_hole_side(w, index, r)?, eval_q(w, index, l)?) {
            (Some(_), Some(c)) => Some((flip_bowtie(b), c)),
            _ => None,
        },
    };
    Ok(match oriented {
        // GE: conic iff the constant is zero; always upward-closed.
        Some((3, c)) => Some((c.is_zero(), true)),
        // LE: conic iff zero; never upward-closed.
        Some((1, c)) => Some((c.is_zero(), false)),
        // EQ at zero: the kernel ray. EQ elsewhere: outside (the
        // singleton is convex semantically, but the v1 grammar's
        // equality row is `= 0` only — closed world).
        Some((2, c)) => {
            if c.is_zero() {
                Some((true, false))
            } else {
                None
            }
        }
        // LT / GT / NE: strict rays and disequalities are outside v1.
        _ => None,
    })
}

/// Lean `classifyPred`: the `FAnd`-only recursion, walked as the
/// flattened conjunct list (verdict-identical; see the module header).
/// Both class bits combine with `&&`; any unclassifiable leaf makes
/// the whole predicate unclassified.
fn classify_pred(w: &mut Walk, index: usize, form: u32) -> Result<Option<(bool, bool)>, EvalError> {
    let leaves = w.conjunct_list(index, form)?;
    let mut conic = true;
    let mut up_closed = true;
    for leaf in leaves {
        match classify_atom(w, index, leaf)? {
            None => return Ok(None),
            Some((c, u)) => {
                conic &= c;
                up_closed &= u;
            }
        }
    }
    Ok(Some((conic, up_closed)))
}

/// Evaluate a predicate-class relation. One argument cell: the
/// predicate `Formula` element.
pub(crate) fn eval_predclass(
    name: &str,
    v: &BlVocab,
    kind: PredClassKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let predicate = elem_local(name, 0, args[0], rows)?;
    let cls = classify_pred(&mut w, 0, predicate)?;
    Ok(match kind {
        PredClassKind::Conic => matches!(cls, Some((true, _))),
        PredClassKind::Convex => cls.is_some(),
        PredClassKind::UpClosedConic => matches!(cls, Some((true, true))),
    })
}
