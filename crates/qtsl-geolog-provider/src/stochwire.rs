//! `qtsl_stochwire_shape`: the QMarginalCompat shape receipt
//! as a row-context recompute (the PDG wire tier's checker surface).
//!
//! Semantic authority: the section-F block of
//! the declaring theory (QPenaltyFun / StochWire /
//! QStochContribList / QMarginalCompat, staged 2026-07-19) + the
//! committed EvalSpec row (OracleSemanticsQtslCert, R7) + the
//! QMarginalCompat entry of the rule catalogue. The Lean
//! warrant (the auxiliary Lean development's marginal-compatibility module,
//! sorry-free) owns the discharge itself: for the sum-formed
//! composition law the marginal-compatibility conclusion is a THEOREM
//! (`penalty_marginal_domination` + `sublevel_marginal`; auto-discharge
//! `sum_dominates_sup`), so for sum-formed wires this shape receipt is
//! the rule's ENTIRE checker surface.
//!
//! The walk's obligations (registry R7), verbatim from the committed
//! EvalSpec row — no more, no less (checking beyond the committed spec
//! would be an impl/spec mismatch in the other direction):
//!
//! 1. **decode** — the contributor kit: a `QStochContribList`
//!    cons-list of (axes, fun) pairs, `axes` a Shape literal (the
//!    injection as a sorted axis-index list — the tensor-contraction
//!    index-map idiom), `fun` a `QPenaltyFun` element
//!    (`qpfIndicator` or `qpfNamed`);
//! 2. **axis lists** (decided content) — each contributor's axis list
//!    is strictly sorted and every axis is within the declared common
//!    space's rank;
//! 3. **induced extents** (decided content) — the extents the common
//!    space induces along the contributor's axes equal the contributor
//!    functional's own declared space, element-wise (the pushforward
//!    is onto the space the functional was declared over — the
//!    "composite functional reference is the declared additive
//!    composition over the wiring row's injections" residue that is
//!    syntactic rather than definitional);
//! 4. **wf class dispatch** — `qpfNamed` classes route through the
//!    ENNRat-codomain receipt's recognizer ([`RECOGNIZED_NAMED_CLASSES`]),
//!    FAIL-CLOSED: an unrecognized class REFUSES (refuse-not-guess:
//!    the claim may be fine, this checker cannot
//!    decide it). `qpfIndicator` is the kernel-tier rung whose
//!    well-formedness is definitional (a face of the simplex) — no
//!    class row exists and none is consulted.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::miranda`]): a decided violation is `Ok(false)` — named via
//! [`StochWireViolation`] for callers that want the reason — and
//! anything the row context cannot decide (unconstructed/ambiguous
//! elements, unrecognized classes, exhausted budgets) REFUSES, never
//! guesses.

use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The stochastic-wire family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_stochwire_shape",
    &[("contribs", "QStochContribList"), ("space", "Shape")],
    RelKind::StochWire,
)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const STOCHWIRE_MAX_RANK: usize = 1 << 10;
const MAX_DECODE_STEPS: usize = 1 << 20;

/// The ENNRat-codomain receipt's recognizer: the `qpfNamed` classes
/// whose penalty functionals are established ENNRat-valued (convex,
/// lsc, proper) in the house record. FAIL-CLOSED: any class not listed
/// here refuses at dispatch.
///
/// - `"relent_cpd"` — the edge-local relative-entropy wire of
///   the stochastic-wire verification study (the section-F staging comment's
///   "first concrete class"): for a wire with cpd table `p` and weight
///   `beta > 0`, `f(mu) = beta * E_{x ~ mu_src}[ KL( mu(tgt | x) ||
///   p[x] ) ]` — jointly convex (joint convexity of KL + linearity of
///   marginalization), lower-semicontinuous, proper (finite at any
///   `mu` matching the cpd), and `[0, infinity]`-valued by the
///   nonnegativity of KL with `beta > 0`.
pub const RECOGNIZED_NAMED_CLASSES: &[&str] = &["relent_cpd"];

/// The contributor-kit constructor vocabulary, pinned at registry
/// construction from the sort the `qtsl_stochwire_shape` declaration
/// names (the `build_miranda_vocab` pattern: names select, shapes
/// verify, identities pin).
#[derive(Debug, Clone)]
pub struct StochWireVocab {
    qsc_nil: Chid,
    qsc_cons: Chid,
    qpf_indicator: Chid,
    qpf_named: Chid,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain) —
    /// so "constructed by something outside the expected pair" is a
    /// definite malformation, distinct from "not constructed in view"
    /// (refusal).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// The `qtsl_stochwire_shape` relation's expected shape — record
/// `{contribs: C, space: Shape}` (bytewise field order) with `C` an
/// element sort and `space` on the Shape ground. Returns `C` on match.
pub fn matches_stochwire_signature(sig: &DomainSig) -> Option<Chid> {
    let DomainSig::Record(fields) = sig else {
        return None;
    };
    let [(f0, s0), (f1, s1)] = fields.as_slice() else {
        return None;
    };
    if f0 != "contribs" || f1 != "space" {
        return None;
    }
    let (SortKey::Elem(c), SortKey::Ground(Ground::Shape)) = (s0, s1) else {
        return None;
    };
    Some(*c)
}

/// Build the contributor-kit vocabulary for the sort the gated
/// declaration names. `Err` → the candidate relation Refuses
/// (C-ORACLE safe-fail).
pub fn build_stochwire_vocab(
    indices: &[&TheoryIndex],
    contribs_sort: Chid,
) -> Result<StochWireVocab, String> {
    let find = |name: &str,
                want_cod: Chid,
                check: &dyn Fn(&DomainSig) -> Result<(), String>|
     -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort \
                     (wrong kind or codomain)"
                ));
            }
            check(&d.domain).map_err(|why| format!("`{name}`: {why}"))?;
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };

    // --- the contributor cons-list -------------------------------------
    let (qsc_nil, _) = find("qscNil", contribs_sort, &|s| {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    })?;
    let (qsc_cons, cons_sig) = find("qscCons", contribs_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(a, SortKey::Ground(Ground::Shape)), (f, SortKey::Elem(_)), (t, SortKey::Elem(ts))]
                if a == "axes" && f == "fun" && t == "tail" && *ts == contribs_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (axes: Shape, fun: QPenaltyFun, tail: \
                      QStochContribList)"
                .into()),
        }
    })?;
    let DomainSig::Record(cons_fields) = &cons_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(penalty_sort) = cons_fields[1].1 else {
        unreachable!("checked above")
    };

    // --- the penalty-functional constructors ----------------------------
    let (qpf_indicator, _) = find("qpfIndicator", penalty_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(c, SortKey::Ground(Ground::Shape)), (sp, SortKey::Ground(Ground::Shape))]
                if c == "cells" && sp == "space" =>
            {
                Ok(())
            }
            _ => Err("expected fields (cells: Shape, space: Shape)".into()),
        }
    })?;
    let (qpf_named, _) = find("qpfNamed", penalty_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(c, SortKey::Ground(Ground::Str)), (n, SortKey::Ground(Ground::Str)), (sp, SortKey::Ground(Ground::Shape))]
                if c == "class" && n == "name" && sp == "space" =>
            {
                Ok(())
            }
            _ => Err("expected fields (class: Str, name: Str, space: Shape)".into()),
        }
    })?;

    // --- per-sort constructor rosters -----------------------------------
    let kit_sorts = [contribs_sort, penalty_sort];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in kit_sorts {
        ctors.entry(s).or_default();
    }
    for index in indices {
        for decl in &index.funs {
            if decl.relational || decl.name.contains('/') {
                continue;
            }
            if let Some(SortKey::Elem(c)) = decl.codomain {
                if let Some(roster) = ctors.get_mut(&c) {
                    roster.insert(decl.chid, decl.domain.clone());
                }
            }
        }
    }

    Ok(StochWireVocab {
        qsc_nil,
        qsc_cons,
        qpf_indicator,
        qpf_named,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The decoded kit (pure data — the core checks run on this, so tests
// hit the combinatorics directly)
// ---------------------------------------------------------------------

/// One decoded penalty-functional reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PenaltyFunDecl {
    /// `qpfIndicator` — the kernel-tier rung (f ∈ {0, ∞}); wf is
    /// definitional, `cells` is retained as data but R7's committed
    /// spec consults only `space`.
    Indicator { cells: Vec<u64>, space: Vec<u64> },
    /// `qpfNamed` — an opaque named reference to producer-side credal
    /// data; `class` routes the wf recognizer (fail-closed).
    Named {
        class: String,
        name: String,
        space: Vec<u64>,
    },
}

impl PenaltyFunDecl {
    /// The functional's own declared space (per-axis extents).
    pub fn space(&self) -> &[u64] {
        match self {
            PenaltyFunDecl::Indicator { space, .. } => space,
            PenaltyFunDecl::Named { space, .. } => space,
        }
    }
}

/// One contributor: (axes, fun) — WHICH axes of the common space the
/// contributor reads, and the functional it applies there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StochContributor {
    pub axes: Vec<u64>,
    pub fun: PenaltyFunDecl,
}

/// The decoded shape-receipt kit.
#[derive(Debug, Clone)]
pub struct StochWireKit {
    /// The declared common space (per-axis extents).
    pub space: Vec<u64>,
    pub contribs: Vec<StochContributor>,
}

/// A decided kit violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is a check the committed R7 spec names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StochWireViolation {
    /// A contributor's axis list is not strictly increasing (the
    /// mis-bound wire: an injection that repeats or scrambles axes).
    AxesUnsorted { contrib: usize },
    /// A contributor names an axis at or beyond the common space's
    /// rank.
    AxisOutOfRank { contrib: usize, axis: u64 },
    /// The extents the common space induces along the contributor's
    /// axes disagree with the functional's own declared space (the
    /// marginal-incompatibility shape: the pushforward does not land
    /// on the space the functional was declared over).
    ExtentMismatch {
        contrib: usize,
        induced: Vec<u64>,
        declared: Vec<u64>,
    },
}

impl std::fmt::Display for StochWireViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StochWireViolation::AxesUnsorted { contrib } => {
                write!(f, "contributor {contrib}: axis list not strictly sorted")
            }
            StochWireViolation::AxisOutOfRank { contrib, axis } => {
                write!(
                    f,
                    "contributor {contrib}: axis {axis} at or beyond the \
                     declared space's rank"
                )
            }
            StochWireViolation::ExtentMismatch {
                contrib,
                induced,
                declared,
            } => {
                write!(
                    f,
                    "contributor {contrib}: induced extents {induced:?} disagree \
                     with the functional's declared space {declared:?}"
                )
            }
        }
    }
}

/// The full R7 check on a decoded kit. `Err` = refusal (an
/// unrecognized `qpfNamed` class — the fail-closed recognizer — or a
/// budget-class out); `Ok(Err(v))` = decided false with the named
/// violation; `Ok(Ok(()))` = accept.
pub fn check_stochwire(kit: &StochWireKit) -> Result<Result<(), StochWireViolation>, String> {
    let rank = kit.space.len();
    if rank > STOCHWIRE_MAX_RANK {
        return Err(format!(
            "common-space rank beyond the shape budget ({STOCHWIRE_MAX_RANK}) — refusing"
        ));
    }
    for (ci, c) in kit.contribs.iter().enumerate() {
        if c.axes.len() > STOCHWIRE_MAX_RANK {
            return Err(format!(
                "contributor {ci}: axis-list length beyond the shape budget \
                 ({STOCHWIRE_MAX_RANK}) — refusing"
            ));
        }
        // 4. wf class dispatch, FAIL-CLOSED (a refusal, not a decided
        //    false: the functional may be perfectly well-formed; this
        //    checker cannot decide it).
        if let PenaltyFunDecl::Named { class, .. } = &c.fun {
            if !RECOGNIZED_NAMED_CLASSES.contains(&class.as_str()) {
                return Err(format!(
                    "contributor {ci}: qpfNamed class `{class}` is not in the \
                     ENNRat-codomain recognizer — fail-closed, refusing"
                ));
            }
        }
        // 2. axis lists strictly sorted and within the space's rank.
        for w in c.axes.windows(2) {
            if w[0] >= w[1] {
                return Ok(Err(StochWireViolation::AxesUnsorted { contrib: ci }));
            }
        }
        for &a in &c.axes {
            if a as usize >= rank {
                return Ok(Err(StochWireViolation::AxisOutOfRank {
                    contrib: ci,
                    axis: a,
                }));
            }
        }
        // 3. induced extents equal the functional's own declared space.
        let induced: Vec<u64> = c.axes.iter().map(|&a| kit.space[a as usize]).collect();
        if induced != c.fun.space() {
            return Ok(Err(StochWireViolation::ExtentMismatch {
                contrib: ci,
                induced,
                declared: c.fun.space().to_vec(),
            }));
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// Row-context decode
// ---------------------------------------------------------------------

use crate::error::EvalError;

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a StochWireVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self, index: usize) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
                index,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, index: usize, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                ctx_err(
                    self.name,
                    index,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: self.name.into(),
                index,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    }

    fn sole(&mut self, index: usize, sort: Chid, elem: u32) -> Result<&'a CtorRow, EvalError> {
        self.step(index)?;
        let roster = self.v.ctors.get(&sort).expect("kit sorts rostered");
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {elem} is produced by multiple constructor rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            ctx_err(
                self.name,
                index,
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    fn shape(&self, index: usize, val: &Value, what: &str) -> Result<Vec<u64>, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Shape(s) = l.view() {
                return Ok(s.iter().collect());
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Shape literal — malformed rows"),
        ))
    }

    fn str_lit(&self, index: usize, val: &Value, what: &str) -> Result<String, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Str(s) = l.view() {
                return Ok(s.to_string());
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Str literal — malformed rows"),
        ))
    }

    /// Decode one QPenaltyFun element.
    fn penalty_fun(
        &mut self,
        index: usize,
        penalty_sort: Chid,
        elem: u32,
    ) -> Result<PenaltyFunDecl, EvalError> {
        let row = self.sole(index, penalty_sort, elem)?;
        if row.fun == self.v.qpf_indicator {
            let [cells, space] = row.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    index,
                    "qpfIndicator row arity mismatch".into(),
                ));
            };
            Ok(PenaltyFunDecl::Indicator {
                cells: self.shape(index, cells, "qpfIndicator/cells")?,
                space: self.shape(index, space, "qpfIndicator/space")?,
            })
        } else if row.fun == self.v.qpf_named {
            let [class, name, space] = row.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    index,
                    "qpfNamed row arity mismatch".into(),
                ));
            };
            Ok(PenaltyFunDecl::Named {
                class: self.str_lit(index, class, "qpfNamed/class")?,
                name: self.str_lit(index, name, "qpfNamed/name")?,
                space: self.shape(index, space, "qpfNamed/space")?,
            })
        } else {
            Err(ctx_err(
                self.name,
                index,
                "penalty-fun element constructed outside the qpfIndicator/qpfNamed \
                 pair — malformed rows"
                    .into(),
            ))
        }
    }
}

/// Decode the two relation arguments into a [`StochWireKit`] (exposed
/// so tests can hit the combinatorics directly). Args in wire field
/// order: `contribs` (same-body element ref), `space` (Shape literal).
///
/// `Err(EvalError)` = refusal — row-context undecidability;
/// decided content lives in [`check_stochwire`].
pub fn decode_stochwire_kit(
    name: &str,
    v: &StochWireVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<StochWireKit, EvalError> {
    let contribs_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qsc_cons))
        .map(|(s, _)| s)
        .expect("qscCons rostered under its codomain");
    let penalty_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qpf_indicator))
        .map(|(s, _)| s)
        .expect("qpfIndicator rostered under its codomain");
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };

    // --- arg 1: the declared common space (a literal) -------------------
    let space = d.shape(1, args[1], "space")?;

    // --- arg 0: the contributor cons-list --------------------------------
    let head = d.elem(0, args[0])?;
    let mut contribs = Vec::new();
    let mut visited: HashSet<u32> = HashSet::new();
    let mut cur = head;
    loop {
        if !visited.insert(cur) {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} recurs along its own list tail (P-ACYCLIC \
                     territory) — refusing"
                ),
            ));
        }
        let row = d.sole(0, contribs_sort, cur)?;
        if row.fun == v.qsc_nil {
            break;
        }
        if row.fun != v.qsc_cons {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} is constructed by a fun outside the expected \
                     nil/cons pair — malformed rows"
                ),
            ));
        }
        let [axes, fun, tail] = row.args.as_slice() else {
            return Err(ctx_err(name, 0, "qscCons row arity mismatch".into()));
        };
        let axes = d.shape(0, axes, "qscCons/axes")?;
        let fun_elem = d.elem(0, fun)?;
        let fun = d.penalty_fun(0, penalty_sort, fun_elem)?;
        contribs.push(StochContributor { axes, fun });
        cur = d.elem(0, tail)?;
    }

    Ok(StochWireKit { space, contribs })
}

/// Decode + check: the `qtsl_stochwire_shape` evaluation.
pub fn eval_stochwire(
    name: &str,
    v: &StochWireVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let kit = decode_stochwire_kit(name, v, args, rows)?;
    match check_stochwire(&kit) {
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

    fn named(class: &str, space: &[u64]) -> PenaltyFunDecl {
        PenaltyFunDecl::Named {
            class: class.into(),
            name: "t".into(),
            space: space.to_vec(),
        }
    }

    fn indicator(cells: &[u64], space: &[u64]) -> PenaltyFunDecl {
        PenaltyFunDecl::Indicator {
            cells: cells.to_vec(),
            space: space.to_vec(),
        }
    }

    /// The witness shape in miniature: common space [2, 2]; a
    /// recognized named block on axis 0; the diagonal indicator on
    /// both axes (the share itself, kernel-tier rung).
    fn witness_kit() -> StochWireKit {
        StochWireKit {
            space: vec![2, 2],
            contribs: vec![
                StochContributor {
                    axes: vec![0],
                    fun: named("relent_cpd", &[2]),
                },
                StochContributor {
                    axes: vec![0, 1],
                    fun: indicator(&[0, 3], &[2, 2]),
                },
            ],
        }
    }

    #[test]
    fn witness_shape_accepts() {
        assert_eq!(check_stochwire(&witness_kit()), Ok(Ok(())));
    }

    #[test]
    fn empty_contributor_list_accepts() {
        // Zero contributors: every per-contributor obligation is
        // vacuous (and the discharge concludes nothing).
        let kit = StochWireKit {
            space: vec![3],
            contribs: vec![],
        };
        assert_eq!(check_stochwire(&kit), Ok(Ok(())));
    }

    #[test]
    fn empty_axes_constant_contributor_accepts() {
        // A contributor on no axes is a constant functional over the
        // empty product; its declared space must be [] and is.
        let kit = StochWireKit {
            space: vec![2, 2],
            contribs: vec![StochContributor {
                axes: vec![],
                fun: named("relent_cpd", &[]),
            }],
        };
        assert_eq!(check_stochwire(&kit), Ok(Ok(())));
    }

    #[test]
    fn violations_are_named() {
        // unsorted axes (the mis-bound wire)
        let mut kit = witness_kit();
        kit.contribs[1].axes = vec![1, 0];
        assert_eq!(
            check_stochwire(&kit).unwrap().unwrap_err(),
            StochWireViolation::AxesUnsorted { contrib: 1 }
        );
        // repeated axis is also "not strictly sorted"
        let mut kit = witness_kit();
        kit.contribs[1].axes = vec![0, 0];
        assert_eq!(
            check_stochwire(&kit).unwrap().unwrap_err(),
            StochWireViolation::AxesUnsorted { contrib: 1 }
        );
        // axis out of rank
        let mut kit = witness_kit();
        kit.contribs[0].axes = vec![2];
        assert_eq!(
            check_stochwire(&kit).unwrap().unwrap_err(),
            StochWireViolation::AxisOutOfRank {
                contrib: 0,
                axis: 2
            }
        );
        // induced extents disagree with the declared space
        let mut kit = witness_kit();
        kit.contribs[0].fun = named("relent_cpd", &[3]);
        assert_eq!(
            check_stochwire(&kit).unwrap().unwrap_err(),
            StochWireViolation::ExtentMismatch {
                contrib: 0,
                induced: vec![2],
                declared: vec![3],
            }
        );
    }

    #[test]
    fn unrecognized_class_refuses_fail_closed() {
        let mut kit = witness_kit();
        kit.contribs[0].fun = named("mystery_meat", &[2]);
        let verdict = check_stochwire(&kit);
        assert!(
            matches!(&verdict, Err(why) if why.contains("mystery_meat")
                && why.contains("fail-closed")),
            "unrecognized class must REFUSE, not decide: {verdict:?}"
        );
    }

    #[test]
    fn indicator_needs_no_class_row() {
        // The kernel-tier rung is definitional — an all-indicator kit
        // passes with no recognizer consultation.
        let kit = StochWireKit {
            space: vec![2, 2],
            contribs: vec![StochContributor {
                axes: vec![0, 1],
                fun: indicator(&[0, 3], &[2, 2]),
            }],
        };
        assert_eq!(check_stochwire(&kit), Ok(Ok(())));
    }
}
