//! The Formula/Term surgery family: the proof-theory context machinery
//! — ∧-tree path reads and writes (`conjunctAt`, `conjReplace`) and the
//! two substitution relations (`substituteInFormula`,
//! `applyPredicateToTerm`).
//!
//! Spec authority: the Lean catalogue (`Core/Catalogue.lean`) —
//! `Formula.conjGet?` / `Formula.conjReplace?` over `ConjPath`
//! (here/left/right), `Formula.subst` / `Term.subst` (structural
//! recursion, replacing exactly the `TVar(wire)` leaves), and
//! `applyPredicateToTerm P arg F  :=  F = P.subst predicateHole arg`.
//! The relations are equalities against a deterministic construction,
//! so each evaluator is a PARALLEL STRUCTURAL WALK of the input and the
//! claimed output — never a rebuild (the row context cannot mint
//! elements, and does not need to: equality-with-the-build is decidable
//! by simultaneous descent).
//!
//! # Path convention (the C2 pinned reading)
//!
//! `CtxPath` rows are `PathHere/PathL/PathR` chains read PREFIX-first:
//! the OUTERMOST constructor is the FIRST step (`PathL(p)` = descend
//! into the left conjunct, then follow `p`), exactly the Lean
//! `ConjPath` traversal and the route-d projection's `gPathF`
//! (PathL = 0, PathR = 1). A path that walks off the ∧-tree — a
//! left/right step at a non-`FAnd` node — makes the relation DECIDEDLY
//! FALSE (`conjGet?`/`conjReplace?` return `none`; the Prop is false),
//! not a refusal: the rows are well-formed, the equality just fails.
//!
//! # The hole, transported through the projection
//!
//! The Lean model has no hole constructors: the row theory's `THole`
//! projects to `.var predicateHole` (`Wire = 4294967295` — the route-d
//! projection maps `VfTHole ↦ TmVar 4294967295`, and `holeFresh` pins
//! that no genuine wire types that index), and `FSpH` projects to the
//! wire-model's own nullary (`FwSpH`). Consequences, each an exact
//! transport of `Formula.subst` rather than an extension of it:
//!
//! - under `substituteInFormula` the substituted wire is a GENUINE wire
//!   element (nominal ref — it can never be the hole), so `THole` maps
//!   to itself, exactly as `.var predicateHole` is untouched by a
//!   substitution at any other wire;
//! - under `applyPredicateToTerm` the `THole` leaves are exactly the
//!   `.var predicateHole` occurrences `P.subst predicateHole arg`
//!   replaces, so each must match `arg` in the result;
//! - `FSpH`, like `FTrue`/`FFalse`, carries no terms: substitution is
//!   identity on it.
//!
//! Verdict discipline (the crate's): a decided structural mismatch is
//! `Ok(false)`; unresolvable/ambiguous elements, external refs (the row
//! context is single-body), malformed rows, cyclic constructor chains,
//! and exhausted budgets REFUSE with a reason, never guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::formrows::{find_ctor, find_sort, sole, BlVocab, FormCtor, TermCtor, Walk, MAX_NODES};
use crate::roster::{EntryRow, RelKind, SurgeryKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, TheoryIndex};
use geolog_envelope::Value;
use std::collections::HashSet;

// Field names + bytewise order are part of the claim (copied from the
// registry's signature column, NOT the theory declaration order —
// `conjReplace` and `substituteInFormula` differ between the two).
const F_APPLY_PRED: &[(&str, &str)] = &[
    ("arg", "Term"),
    ("predicate", "Formula"),
    ("result", "Formula"),
];
const F_CONJ_REPLACE: &[(&str, &str)] = &[
    ("form", "Formula"),
    ("path", "CtxPath"),
    ("result", "Formula"),
    ("sub", "Formula"),
];
const F_CONJ_AT: &[(&str, &str)] = &[("form", "Formula"), ("path", "CtxPath"), ("sub", "Formula")];
const F_SUBST: &[(&str, &str)] = &[
    ("form", "Formula"),
    ("result", "Formula"),
    ("term", "Term"),
    ("wire", "Wire"),
];

/// The surgery family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the seam
/// surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "applyPredicateToTerm",
        F_APPLY_PRED,
        RelKind::Surgery(SurgeryKind::ApplyPred),
    ),
    (
        "conjReplace",
        F_CONJ_REPLACE,
        RelKind::Surgery(SurgeryKind::ConjReplace),
    ),
    (
        "conjunctAt",
        F_CONJ_AT,
        RelKind::Surgery(SurgeryKind::ConjAt),
    ),
    (
        "substituteInFormula",
        F_SUBST,
        RelKind::Surgery(SurgeryKind::SubstForm),
    ),
];

/// The surgery family's resolved vocabulary: the three `CtxPath`
/// constructors, name-selected once at construction and shape-verified
/// (C-ORACLE: names select, shapes verify, identities pin). The
/// Formula/Term rosters ride the shared [`BlVocab`], passed at
/// evaluation.
#[derive(Debug, Clone)]
pub struct SurgeryVocab {
    path_here: Chid,
    path_l: Chid,
    path_r: Chid,
}

/// Build the surgery vocabulary over the declared indices. `Err` → the
/// family is not claimed (declared-but-unbound, safe-fail).
pub fn build_surgery_vocab(indices: &[&TheoryIndex]) -> Result<SurgeryVocab, String> {
    let ctxpath = find_sort(indices, "CtxPath")?;
    Ok(SurgeryVocab {
        path_here: find_ctor(indices, "PathHere", ctxpath, 0)?,
        path_l: find_ctor(indices, "PathL", ctxpath, 1)?,
        path_r: find_ctor(indices, "PathR", ctxpath, 1)?,
    })
}

/// One ∧-tree step. `Left` descends the first `FAnd` argument,
/// `Right` the second. (Shared with the promise family's recomputed-
/// context walk, [`crate::blpromise`].)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Dir {
    Left,
    Right,
}

/// Decode a `CtxPath` element into its step sequence, prefix-first
/// (outermost constructor = first step). Linear chains only: a
/// revisited element is a constructor cycle (P-ACYCLIC territory) and
/// refuses; missing/ambiguous constructor rows refuse via [`sole`].
/// (Shared with [`crate::blpromise`], whose `PPromise/path` rows are
/// the same `CtxPath` chains.)
pub(crate) fn decode_path(
    name: &str,
    w: &mut Walk,
    sv: &SurgeryVocab,
    rows: &CertRows,
    index: usize,
    path: u32,
) -> Result<Vec<Dir>, EvalError> {
    #[derive(Clone, Copy)]
    enum P {
        Here,
        L,
        R,
    }
    let mut dirs = Vec::new();
    let mut seen: HashSet<u32> = HashSet::new();
    let mut cur = path;
    loop {
        w.budget(index)?;
        if !seen.insert(cur) {
            return Err(w.refuse(
                index,
                format!(
                    "path element {cur} participates in cyclic constructor rows \
                     (P-ACYCLIC territory) — refusing"
                ),
            ));
        }
        let (k, row) = sole(
            name,
            index,
            cur,
            rows,
            |fun| {
                if fun == sv.path_here {
                    Some(P::Here)
                } else if fun == sv.path_l {
                    Some(P::L)
                } else if fun == sv.path_r {
                    Some(P::R)
                } else {
                    None
                }
            },
            "path",
        )?;
        match k {
            P::Here => {
                if !row.args.is_empty() {
                    return Err(w.refuse(
                        index,
                        format!(
                            "malformed `PathHere` row: {} args (expected 0)",
                            row.args.len()
                        ),
                    ));
                }
                return Ok(dirs);
            }
            P::L | P::R => {
                if row.args.len() != 1 {
                    return Err(w.refuse(
                        index,
                        format!(
                            "malformed path-step row: {} args (expected 1)",
                            row.args.len()
                        ),
                    ));
                }
                dirs.push(if matches!(k, P::L) {
                    Dir::Left
                } else {
                    Dir::Right
                });
                cur = w.local(index, &row.args[0])?;
            }
        }
    }
}

/// Which leaf rule the parallel substitution walk applies — the two
/// substitution relations share one engine.
enum SubstMode<'x> {
    /// `substituteInFormula`: replace `TVar(wire)`; `THole` is
    /// untouched (the hole is no wire — `holeFresh`).
    Wire { wire: &'x Value, term: u32 },
    /// `applyPredicateToTerm`: replace `THole` (the projection of
    /// `.var predicateHole`); genuine wires are untouched.
    Hole { arg: u32 },
}

/// Decide `b = subst(a)` by simultaneous structural descent — the
/// direct transport of `Formula.subst`/`Term.subst` to row grain.
/// Pair-memoized (DAG-linear); ctor/literal/nominal mismatches decide
/// FALSE, unresolvable structure refuses through the walk's machinery.
fn subst_walk(
    w: &mut Walk,
    mode: &SubstMode,
    ia: usize,
    ib: usize,
    root_a: u32,
    root_b: u32,
) -> Result<bool, EvalError> {
    // (input elem, output elem, is_term).
    let mut seen: HashSet<(u32, u32, bool)> = HashSet::new();
    let mut work: Vec<(u32, u32, bool)> = vec![(root_a, root_b, false)];
    while let Some((a, b, is_term)) = work.pop() {
        if !seen.insert((a, b, is_term)) {
            continue;
        }
        if seen.len() > MAX_NODES {
            return Err(w.refuse(
                ia,
                "substitution walk exhausted its pair budget — pathological rows".into(),
            ));
        }
        if is_term {
            let (ka, ra) = w.term_ctor_row(ia, a)?;
            // The two replacement leaves compare the OUTPUT subtree
            // against a fixed term, not against the input node.
            match ka {
                TermCtor::Var => {
                    if let SubstMode::Wire { wire, term } = mode {
                        if w.nominal_eq(ia, &ra.args[0], wire)? {
                            if !w.struct_eq(ib, b, *term, true)? {
                                return Ok(false);
                            }
                            continue;
                        }
                    }
                    // An untouched wire: the output is the same var.
                    let (kb, rb) = w.term_ctor_row(ib, b)?;
                    if kb != TermCtor::Var || !w.nominal_eq(ib, &ra.args[0], &rb.args[0])? {
                        return Ok(false);
                    }
                }
                TermCtor::Hole => {
                    if let SubstMode::Hole { arg } = mode {
                        if !w.struct_eq(ib, b, *arg, true)? {
                            return Ok(false);
                        }
                        continue;
                    }
                    // Wire mode: the hole is untouched.
                    let (kb, _) = w.term_ctor_row(ib, b)?;
                    if kb != TermCtor::Hole {
                        return Ok(false);
                    }
                }
                TermCtor::Const => {
                    let (kb, rb) = w.term_ctor_row(ib, b)?;
                    if kb != TermCtor::Const || ra.args[0] != rb.args[0] {
                        return Ok(false);
                    }
                }
                TermCtor::Neg => {
                    let (kb, rb) = w.term_ctor_row(ib, b)?;
                    if kb != TermCtor::Neg {
                        return Ok(false);
                    }
                    let ca = w.local(ia, &ra.args[0])?;
                    let cb = w.local(ib, &rb.args[0])?;
                    work.push((ca, cb, true));
                }
                TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                    let (kb, rb) = w.term_ctor_row(ib, b)?;
                    if kb != ka {
                        return Ok(false);
                    }
                    for i in 0..2 {
                        let ca = w.local(ia, &ra.args[i])?;
                        let cb = w.local(ib, &rb.args[i])?;
                        work.push((ca, cb, true));
                    }
                }
                TermCtor::Idx => {
                    // args (field order): [nat i, ref t]; the index is
                    // preserved, the term slot descends (Lean:
                    // `.idx u i => .idx (subst u) i`).
                    let (kb, rb) = w.term_ctor_row(ib, b)?;
                    if kb != TermCtor::Idx || ra.args[0] != rb.args[0] {
                        return Ok(false);
                    }
                    let ca = w.local(ia, &ra.args[1])?;
                    let cb = w.local(ib, &rb.args[1])?;
                    work.push((ca, cb, true));
                }
            }
        } else {
            let (ka, ra) = w.form_ctor_row(ia, a)?;
            let (kb, rb) = w.form_ctor_row(ib, b)?;
            if ka != kb {
                return Ok(false);
            }
            match ka {
                FormCtor::True | FormCtor::False | FormCtor::SpH => {}
                FormCtor::Atom(_) => {
                    for i in 0..2 {
                        let ca = w.local(ia, &ra.args[i])?;
                        let cb = w.local(ib, &rb.args[i])?;
                        work.push((ca, cb, true));
                    }
                }
                FormCtor::And | FormCtor::Or => {
                    for i in 0..2 {
                        let ca = w.local(ia, &ra.args[i])?;
                        let cb = w.local(ib, &rb.args[i])?;
                        work.push((ca, cb, false));
                    }
                }
                FormCtor::InRegion => {
                    // args (field order S < simplex < t): the nominal
                    // positions are PRESERVED by substitution (Lean:
                    // `.inRegion u simplex S => .inRegion (subst u)
                    // simplex S`); the term slot descends.
                    if !w.nominal_eq(ia, &ra.args[0], &rb.args[0])?
                        || !w.nominal_eq(ia, &ra.args[1], &rb.args[1])?
                    {
                        return Ok(false);
                    }
                    let ca = w.local(ia, &ra.args[2])?;
                    let cb = w.local(ib, &rb.args[2])?;
                    work.push((ca, cb, true));
                }
            }
        }
    }
    Ok(true)
}

/// Evaluate a surgery-family relation. Argument cells arrive in
/// declared (bytewise) field order — the entry tables above.
pub(crate) fn eval_surgery(
    name: &str,
    v: &BlVocab,
    sv: &SurgeryVocab,
    kind: SurgeryKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    match kind {
        SurgeryKind::ConjAt => {
            // Field order: form, path, sub.
            let form = elem_local(name, 0, args[0], rows)?;
            let path = elem_local(name, 1, args[1], rows)?;
            let sub = elem_local(name, 2, args[2], rows)?;
            let dirs = decode_path(name, &mut w, sv, rows, 1, path)?;
            let mut cur = form;
            for d in dirs {
                let (k, row) = w.form_ctor_row(0, cur)?;
                if k != FormCtor::And {
                    // The path walked off the ∧-tree: conjGet? = none,
                    // the equality is decidedly false.
                    return Ok(false);
                }
                let slot = if d == Dir::Left { 0 } else { 1 };
                cur = w.local(0, &row.args[slot])?;
            }
            w.struct_eq(2, cur, sub, false)
        }
        SurgeryKind::ConjReplace => {
            // Field order: form, path, result, sub (the REGISTRY
            // order — the theory declaration lists sub before result).
            let form = elem_local(name, 0, args[0], rows)?;
            let path = elem_local(name, 1, args[1], rows)?;
            let result = elem_local(name, 2, args[2], rows)?;
            let sub = elem_local(name, 3, args[3], rows)?;
            let dirs = decode_path(name, &mut w, sv, rows, 1, path)?;
            // Parallel descent: at every step the input must be an
            // `FAnd` (else conjReplace? = none — decidedly false), the
            // output must be an `FAnd` whose UNTOUCHED arm equals the
            // input's, and both descend on the step's side. At the
            // path's end the output subtree must equal `sub`. Note
            // `conjReplace? .here g = some g` regardless of the input
            // node's shape — a here-path constrains only result = sub.
            let mut fc = form;
            let mut rc = result;
            for d in dirs {
                let (fk, frow) = w.form_ctor_row(0, fc)?;
                if fk != FormCtor::And {
                    return Ok(false);
                }
                let (rk, rrow) = w.form_ctor_row(2, rc)?;
                if rk != FormCtor::And {
                    return Ok(false);
                }
                let (fl, fr) = (w.local(0, &frow.args[0])?, w.local(0, &frow.args[1])?);
                let (rl, rr) = (w.local(2, &rrow.args[0])?, w.local(2, &rrow.args[1])?);
                match d {
                    Dir::Left => {
                        if !w.struct_eq(2, fr, rr, false)? {
                            return Ok(false);
                        }
                        fc = fl;
                        rc = rl;
                    }
                    Dir::Right => {
                        if !w.struct_eq(2, fl, rl, false)? {
                            return Ok(false);
                        }
                        fc = fr;
                        rc = rr;
                    }
                }
            }
            let _ = fc; // the replaced subtree's prior content is unconstrained
            w.struct_eq(2, rc, sub, false)
        }
        SurgeryKind::SubstForm => {
            // Field order: form, result, term, wire (registry order).
            let form = elem_local(name, 0, args[0], rows)?;
            let result = elem_local(name, 1, args[1], rows)?;
            let term = elem_local(name, 2, args[2], rows)?;
            // The wire argument stays a nominal ref (compared via
            // normalized refs, never resolved to structure).
            match args[3] {
                Value::Ref(_) => {}
                _ => {
                    return Err(EvalError::ArgDtype {
                        name: name.into(),
                        index: 3,
                        expected: "element ref",
                        found: 0xFF,
                    })
                }
            }
            let mode = SubstMode::Wire {
                wire: args[3],
                term,
            };
            subst_walk(&mut w, &mode, 0, 1, form, result)
        }
        SurgeryKind::ApplyPred => {
            // Field order: arg, predicate, result.
            let arg = elem_local(name, 0, args[0], rows)?;
            let predicate = elem_local(name, 1, args[1], rows)?;
            let result = elem_local(name, 2, args[2], rows)?;
            let mode = SubstMode::Hole { arg };
            subst_walk(&mut w, &mode, 1, 2, predicate, result)
        }
    }
}
