//! The atomic-compare form checks (`atomicCompareForm` /
//! `atomicCompareZero`) and the shared row-context structural walks.
//!
//! Both relations decide whether a `Formula` element has a pinned
//! syntactic shape relative to two `Term` elements:
//!
//! - Form: `formula` **is** `(l bowtie r)` — head constructor
//!   `FAtom<op>` selected by the bowtie code, arms structurally equal
//!   to `l`/`r`.
//! - Zero: `formula` **is** `((l - r) bowtie 0)` — head `FAtom<op>`,
//!   left arm a `TSub` of terms structurally equal to `l`/`r`, right
//!   arm `TConst(0)`.
//!
//! Bowtie coding 0..4 selects LT, LE, EQ, GE, GT; code 5 (NE) exists
//! as a constructor but no atomic formula corresponds to codes ≥ 5 —
//! those are a decided `false`, which is exactly what discharges the
//! declaring rule's bowtie-range premise.
//!
//! "Is" means STRUCTURAL equality over the constructor rows (the Lean
//! realization compares decoded inductive values; interning is the
//! writer's choice, so element identity is sufficient but not
//! necessary). Verdict discipline: a decided mismatch (wrong head,
//! wrong operator, bowtie ≥ 5, non-zero constant, structurally
//! different terms) is `Ok(false)`; anything the row context cannot
//! decide (unconstructed elements with distinct ids, ambiguous
//! constructor rows, external refs, exhausted depth) refuses via
//! [`EvalError::CtxArg`] — never a guessed verdict.

use crate::error::EvalError;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{Literal, LiteralView, Value};
use std::collections::HashMap;

const F_ATOMIC: &[(&str, &str)] = &[
    ("bowtie", "Nat"),
    ("formula", "Formula"),
    ("l", "Term"),
    ("r", "Term"),
];

/// The atomic-compare family's rows of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "atomicCompareForm",
        F_ATOMIC,
        RelKind::Atomic { zero: false },
    ),
    (
        "atomicCompareZero",
        F_ATOMIC,
        RelKind::Atomic { zero: true },
    ),
];

/// Budget for the structural walks: refusal, never divergence, on
/// pathological row graphs.
pub(crate) const MAX_STRUCT_NODES: usize = 1 << 20;

/// The pinned Formula/Term constructor vocabulary the atomic-compare
/// family walks (names select once at construction; all dispatch is by
/// the pinned identities). Rosters span every swept index whose funs
/// target the two sorts, so "constructed by something else" is a
/// definite *false*, distinct from "not constructed in view"
/// (refusal).
#[derive(Debug, Clone)]
pub struct SyntaxVocab {
    pub(crate) term_sort: Chid,
    #[allow(dead_code)]
    pub(crate) formula_sort: Chid,
    /// bowtie coding 0..4 → FAtomLT, FAtomLE, FAtomEQ, FAtomGE, FAtomGT.
    fatom: [Chid; 5],
    tsub: Chid,
    tconst: Chid,
    /// Constructor identity → its domain signature, for funs whose
    /// codomain is the Term sort (structural-equality recursion
    /// consults the per-position sorts: Term positions recurse, other
    /// element sorts compare nominally).
    pub(crate) term_ctors: HashMap<Chid, DomainSig>,
    /// Same, codomain = the Formula sort.
    formula_ctors: HashMap<Chid, DomainSig>,
}

impl SyntaxVocab {
    /// Build the constructor vocabulary for the given (Term, Formula)
    /// sorts. Names select the special constructors, shapes verify,
    /// identities pin; the rosters sweep EVERY index so any
    /// constructor of the two sorts yields a definite structural
    /// verdict rather than a refusal. `Err` → the family defers
    /// (safe-fail; never misdispatch).
    pub fn build(
        indices: &[&TheoryIndex],
        term_sort: Chid,
        formula_sort: Chid,
    ) -> Result<SyntaxVocab, String> {
        let mut term_ctors = HashMap::new();
        let mut formula_ctors = HashMap::new();
        for index in indices {
            for decl in &index.funs {
                if decl.relational {
                    continue;
                }
                match decl.codomain {
                    Some(SortKey::Elem(c)) if c == term_sort => {
                        term_ctors.insert(decl.chid, decl.domain.clone());
                    }
                    Some(SortKey::Elem(c)) if c == formula_sort => {
                        formula_ctors.insert(decl.chid, decl.domain.clone());
                    }
                    _ => {}
                }
            }
        }
        let term_pair = DomainSig::Record(vec![
            ("l".to_string(), SortKey::Elem(term_sort)),
            ("r".to_string(), SortKey::Elem(term_sort)),
        ]);
        let find = |name: &str, want_cod: Chid, want_dom: &DomainSig| -> Result<Chid, String> {
            for index in indices {
                let Some(d) = index.fun(name) else { continue };
                if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                    return Err(format!(
                        "`{name}` is not a constructor of the expected sort \
                         (wrong kind or codomain)"
                    ));
                }
                if &d.domain != want_dom {
                    return Err(format!(
                        "`{name}` domain does not match the expected constructor shape"
                    ));
                }
                return Ok(d.chid);
            }
            Err(format!("no `{name}` constructor among the swept revisions"))
        };
        let fatom = [
            find("FAtomLT", formula_sort, &term_pair)?,
            find("FAtomLE", formula_sort, &term_pair)?,
            find("FAtomEQ", formula_sort, &term_pair)?,
            find("FAtomGE", formula_sort, &term_pair)?,
            find("FAtomGT", formula_sort, &term_pair)?,
        ];
        let tsub = find("TSub", term_sort, &term_pair)?;
        let tconst = find(
            "TConst",
            term_sort,
            &DomainSig::Unary(SortKey::Ground(Ground::Q)),
        )?;
        Ok(SyntaxVocab {
            term_sort,
            formula_sort,
            fatom,
            tsub,
            tconst,
            term_ctors,
            formula_ctors,
        })
    }
}

/// Evaluate one atomic-compare relation. `zero` selects the
/// `((l - r) bowtie 0)` shape over the `(l bowtie r)` shape. Args
/// arrive in wire field order (bytewise): `bowtie, formula, l, r`.
pub fn eval_atomic(
    name: &str,
    v: &SyntaxVocab,
    zero: bool,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let Value::Lit(b) = args[0] else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index: 0,
            expected: "Nat",
            found: 0xFF,
        });
    };
    let LiteralView::Nat(bowtie) = b.view() else {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index: 0,
            expected: "Nat",
            found: b.dtype_code(),
        });
    };
    let formula = elem_local(name, 1, args[1], rows)?;
    let l = elem_local(name, 2, args[2], rows)?;
    let r = elem_local(name, 3, args[3], rows)?;
    // bowtie ≥ 5: no atomic formula corresponds to the code — a
    // decided false (the declaring rule's bowtie-range premise never
    // holds out of range).
    let Some(&want_head) = usize::try_from(bowtie).ok().and_then(|c| v.fatom.get(c)) else {
        return Ok(false);
    };
    let head = sole_roster_row(name, 1, &v.formula_ctors, formula, rows)?;
    if head.fun != want_head {
        return Ok(false);
    }
    // FAtom<op> args, wire order: [l: Term, r: Term].
    let [head_l, head_r] = head.args.as_slice() else {
        return Err(ctx_err(
            name,
            1,
            format!(
                "formula element {formula}'s constructor row has {} args \
                 (FAtom takes 2) — malformed rows",
                head.args.len()
            ),
        ));
    };
    let head_l = elem_local(name, 1, head_l, rows)?;
    let head_r = elem_local(name, 1, head_r, rows)?;
    if zero {
        // Left arm: TSub(l', r') with l' ≡ l, r' ≡ r.
        let sub = sole_roster_row(name, 1, &v.term_ctors, head_l, rows)?;
        if sub.fun != v.tsub {
            return Ok(false);
        }
        let [sub_l, sub_r] = sub.args.as_slice() else {
            return Err(ctx_err(
                name,
                1,
                format!(
                    "term element {head_l}'s TSub row has {} args — malformed rows",
                    sub.args.len()
                ),
            ));
        };
        let sub_l = elem_local(name, 1, sub_l, rows)?;
        let sub_r = elem_local(name, 1, sub_r, rows)?;
        if !(term_eq(name, v, 2, sub_l, l, rows)? && term_eq(name, v, 3, sub_r, r, rows)?) {
            return Ok(false);
        }
        // Right arm: TConst(0) — the canonical rational zero.
        let konst = sole_roster_row(name, 1, &v.term_ctors, head_r, rows)?;
        if konst.fun != v.tconst {
            return Ok(false);
        }
        let [c] = konst.args.as_slice() else {
            return Err(ctx_err(
                name,
                1,
                format!(
                    "term element {head_r}'s TConst row has {} args — malformed rows",
                    konst.args.len()
                ),
            ));
        };
        let Value::Lit(lit) = c else {
            return Err(ctx_err(
                name,
                1,
                "TConst argument is not a literal cell — malformed rows".into(),
            ));
        };
        let zero_lit = Literal::q(0, 1).expect("canonical zero");
        Ok(*lit == zero_lit)
    } else {
        Ok(term_eq(name, v, 2, head_l, l, rows)? && term_eq(name, v, 3, head_r, r, rows)?)
    }
}

pub(crate) fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// A Value that must be a same-body element ref.
pub(crate) fn elem_local(
    name: &str,
    index: usize,
    val: &Value,
    rows: &CertRows,
) -> Result<u32, EvalError> {
    match val {
        Value::Ref(r) => rows.local(r).ok_or_else(|| {
            ctx_err(
                name,
                index,
                "external element ref — the row context is single-body".into(),
            )
        }),
        _ => Err(EvalError::ArgDtype {
            name: name.into(),
            index,
            expected: "element ref",
            found: 0xFF,
        }),
    }
}

/// The unique roster-constructor row producing `elem`: zero rows in
/// the roster is undecidable (refuse — the element's structure is not
/// in view), more than one is functionality-violating territory the
/// projection rejects (refuse — never pick).
pub(crate) fn sole_roster_row<'a>(
    name: &str,
    index: usize,
    roster: &HashMap<Chid, DomainSig>,
    elem: u32,
    rows: &'a CertRows,
) -> Result<&'a CtorRow, EvalError> {
    let mut found: Option<&CtorRow> = None;
    for row in rows.producers(elem) {
        if !roster.contains_key(&row.fun) {
            continue;
        }
        if found.is_some() {
            return Err(ctx_err(
                name,
                index,
                format!(
                    "element {elem} is produced by multiple constructor rows — \
                     ambiguous structure, refusing"
                ),
            ));
        }
        found = Some(row);
    }
    found.ok_or_else(|| {
        ctx_err(
            name,
            index,
            format!(
                "element {elem} has no constructor row in the context — \
                 structure undecidable"
            ),
        )
    })
}

/// Acyclicity of the term-constructor graph reachable from `root` —
/// iterative white/gray/black DFS over the Term-sorted positions of
/// roster constructor rows (nominal and ground positions are leaves
/// for this walk, exactly the positions the equality walk never
/// descends). A back edge refuses (acyclicity is a projection-side
/// conformance check; evaluation must not diverge on rows the
/// projection would reject). Elements without a roster row, or with
/// several, are LEAVES here — the equality walk refuses on them if and
/// where it actually needs their structure.
fn check_term_acyclic(
    name: &str,
    v: &SyntaxVocab,
    index: usize,
    root: u32,
    rows: &CertRows,
) -> Result<(), EvalError> {
    enum Frame {
        Enter(u32),
        Exit(u32),
    }
    let mut gray: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut black: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut stack = vec![Frame::Enter(root)];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Exit(e) => {
                gray.remove(&e);
                black.insert(e);
            }
            Frame::Enter(e) => {
                if black.contains(&e) {
                    continue;
                }
                if !gray.insert(e) {
                    return Err(ctx_err(
                        name,
                        index,
                        format!(
                            "element {e} participates in cyclic constructor \
                             rows — refusing"
                        ),
                    ));
                }
                if black.len() + gray.len() > MAX_STRUCT_NODES {
                    return Err(ctx_err(
                        name,
                        index,
                        "structural walk exhausted its node budget — \
                         pathological rows"
                            .into(),
                    ));
                }
                stack.push(Frame::Exit(e));
                let roster_rows: Vec<&CtorRow> = rows
                    .producers(e)
                    .iter()
                    .filter(|r| v.term_ctors.contains_key(&r.fun))
                    .collect();
                let [row] = roster_rows.as_slice() else {
                    continue; // leaf here; equality refuses if it matters
                };
                let sorts = v.term_ctors[&row.fun].arg_sorts();
                for (i, sort) in sorts.iter().enumerate() {
                    if !matches!(sort, SortKey::Elem(s) if *s == v.term_sort) {
                        continue;
                    }
                    if let Some(Value::Ref(r)) = row.args.get(i) {
                        if let Some(child) = rows.local(r) {
                            stack.push(Frame::Enter(child));
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/// Structural equality of two Term elements — iterative worklist with
/// a resolved-pair memo (sound because both sides are
/// acyclicity-checked first: on directed acyclic row graphs, a
/// revisited pair is a shared subcomparison already scheduled, never a
/// cycle). Per pair: identity short-circuits (interned bodies decide
/// here); otherwise both sides' unique roster constructors must agree
/// and their arguments compare per-position by the constructor's own
/// signature — Term positions join the worklist, ground positions
/// compare literal cells (canonical bytes), and every other element
/// sort is NOMINAL: distinct elements are genuinely distinct objects
/// there, so id inequality is a decided false, not a refusal.
pub(crate) fn term_eq(
    name: &str,
    v: &SyntaxVocab,
    index: usize,
    a: u32,
    b: u32,
    rows: &CertRows,
) -> Result<bool, EvalError> {
    check_term_acyclic(name, v, index, a, rows)?;
    check_term_acyclic(name, v, index, b, rows)?;
    let mut seen: std::collections::HashSet<(u32, u32)> = std::collections::HashSet::new();
    let mut work: Vec<(u32, u32)> = vec![(a, b)];
    while let Some((a, b)) = work.pop() {
        if a == b || !seen.insert((a, b)) {
            continue;
        }
        if seen.len() > MAX_STRUCT_NODES {
            return Err(ctx_err(
                name,
                index,
                "structural walk exhausted its pair budget — pathological rows".into(),
            ));
        }
        let ra = sole_roster_row(name, index, &v.term_ctors, a, rows)?;
        let rb = sole_roster_row(name, index, &v.term_ctors, b, rows)?;
        if ra.fun != rb.fun {
            return Ok(false);
        }
        let sorts = v.term_ctors[&ra.fun].arg_sorts();
        if ra.args.len() != sorts.len() || rb.args.len() != sorts.len() {
            return Err(ctx_err(
                name,
                index,
                format!(
                    "constructor row arity disagrees with the declaration \
                     (elements {a}/{b}) — malformed rows"
                ),
            ));
        }
        for (i, sort) in sorts.iter().enumerate() {
            let (va, vb) = (&ra.args[i], &rb.args[i]);
            match sort {
                SortKey::Elem(s) if *s == v.term_sort => {
                    let (la, lb) = (
                        elem_local(name, index, va, rows)?,
                        elem_local(name, index, vb, rows)?,
                    );
                    work.push((la, lb));
                }
                SortKey::Elem(_) => match (va, vb) {
                    (Value::Ref(fa), Value::Ref(fb)) => {
                        if rows.norm(fa) != rows.norm(fb) {
                            return Ok(false);
                        }
                    }
                    _ => {
                        return Err(ctx_err(
                            name,
                            index,
                            "non-ref cell in an element-sorted constructor \
                             position — malformed rows"
                                .into(),
                        ))
                    }
                },
                // Ground and tensor positions: cell equality (canonical
                // forms make byte equality value equality).
                SortKey::Ground(_) | SortKey::TensorOf(_) => match (va, vb) {
                    (Value::Ref(_), _) | (_, Value::Ref(_)) => {
                        return Err(ctx_err(
                            name,
                            index,
                            "element ref in a ground-sorted constructor \
                             position — malformed rows"
                                .into(),
                        ))
                    }
                    _ => {
                        if va != vb {
                            return Ok(false);
                        }
                    }
                },
            }
        }
    }
    Ok(true)
}
