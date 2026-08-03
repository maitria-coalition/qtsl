//! Row-context for element-argument oracles .
//!
//! The R18 registry's first two families evaluated **literal** arguments
//! (ground cells in, verdict out). The `atomicCompareForm` /
//! `atomicCompareZero` family takes *element* arguments — `l`, `r` of
//! sort `Term`; `formula` of sort `Formula` — so its evaluation must see
//! the certificate body's rows: which constructor produced an element,
//! with which arguments. [`CertRows`] is that view: a one-pass index of
//! a body's `FUN_VAL` ops keyed by the **produced element** (the op's
//! value cell), consulted by the oracle's structural walks.
//!
//! Scope honesty: this is representation-level context, same tier as
//! the deferral witness — a body's ops in, no chase state, no
//! projection. The context is deliberately *generic* (every fun-value
//! row is indexed, not just Term/Formula constructors): the evaluator
//! filters against its own pinned constructor roster (C-ORACLE: chids,
//! never names), and the later `conjunctAt`/`conjReplace` legs walk
//! `FAnd` trees and `CtxPath` chains through this same view (the
//! CtxPath prefix reading is a pinned contract, not an
//! implementation choice).
//!
//! Malformation posture: this index REPORTS what the rows say —
//! including shapes the projection would reject (an element produced by
//! two constructor rows, a cyclic term). The *evaluator* is the loud
//! party: it refuses on ambiguity, unresolvable elements, and
//! exhausted depth, never guessing a verdict (P-FUN / P-ACYCLIC are
//! projection-side conformance rows; evaluation cannot assume them).

use crate::theory::Chid;
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Value};
use std::collections::HashMap;

/// One fun-value row: the fun's pinned identity, its argument cells
/// (wire field order — bytewise field-name order), and the
/// value cell. In the constructor reading (`producers`) the value is
/// the produced element itself; in the field-access reading
/// (`arg_rows`, the field-access reading) the value is the field's content — carrying
/// it here is what makes that reading usable.
#[derive(Debug, Clone)]
pub struct CtorRow {
    pub fun: Chid,
    pub args: Vec<Value>,
    pub value: Value,
}

/// One attribute-shaped row, seen from its SUBJECT (the row's first
/// argument, when that cell is a local element ref): the fun's pinned
/// identity, the full argument cells, and the produced value. This is
/// the entity-attribute view the Morse family needs —
/// `QBlockLattice` is entity-like (attribute funs FROM it), so its
/// structure is read by scanning rows keyed on the lattice element,
/// not rows producing it.
#[derive(Debug, Clone)]
pub struct AttrRow {
    pub fun: Chid,
    pub args: Vec<Value>,
    pub value: Value,
}

/// One relation-instance row (`REL_VAL`, no value cell): the
/// relation's pinned identity and its argument cells (wire field
/// order). Membership-style vocabulary (`Simplex/contains`,
/// `ExtensionSet/contains`) is declared relational, so its instance
/// rows ride this shape rather than [`CtorRow`] — the mask family's
/// sweeps read the sealed finite membership data through this view.
#[derive(Debug, Clone)]
pub struct RelRow {
    pub rel: Chid,
    pub args: Vec<Value>,
}

/// A certificate body's fun-value rows, keyed by produced element (the
/// op's value cell, when that cell is a local element ref) and, dually,
/// by subject element (the op's first argument, same condition).
#[derive(Debug, Clone, Default)]
pub struct CertRows {
    /// The body's own commit hash (Locals normalize against it).
    own: [u8; 32],
    /// The body's CHID list (External refs index it).
    deps: Vec<[u8; 32]>,
    by_value: HashMap<u32, Vec<CtorRow>>,
    /// the node walks: the same rows keyed by each LOCAL
    /// element appearing in an ARGUMENT position — field-access reading
    /// direction ("the rows about `p`"), where `by_value` is the
    /// constructor direction ("the rows producing `e`"). A node's field
    /// row `PSyzygy/conclusion(p) = t` is reachable from `p` only here:
    /// its value cell is `t`. Same CtorRow payload, duplicated by
    /// design (additive; the landed producers() path is untouched).
    by_arg: HashMap<u32, Vec<CtorRow>>,
    by_subject: HashMap<u32, Vec<AttrRow>>,
    /// the external-subject clause: rows whose FIRST argument is an EXTERNAL element ref
    /// — invisible to `by_subject`/`subject_elems` by construction (the
    /// subject index is keyed on local counters), so they are reported
    /// here instead of vanishing. Universal-posture consumers (the
    /// admission chase) consult this surface and refuse on the funs
    /// they quantify over — same malformation posture as everything
    /// else in this index: it REPORTS, the evaluator is the loud party.
    external_subject: Vec<AttrRow>,
    /// Relation-instance rows (`Op::Rela`), keyed by SUBJECT — the
    /// first argument, when that cell is a local element ref. The
    /// membership sweeps ("this simplex's mask") read here; the same
    /// malformation posture holds (this index REPORTS; the evaluator
    /// refuses on shapes the projection would reject).
    rel_by_subject: HashMap<u32, Vec<RelRow>>,
    /// The same relation-instance rows keyed by EVERY local element
    /// appearing in ANY argument position (once per distinct element)
    /// — the citation reading, [`Self::arg_rows`]'s relation-row twin.
    /// Vocabulary whose wire order puts a literal field first
    /// (`CellSimplexHasV : [cell: Nat, complex: SimpC, v: Nat]`) is
    /// structurally invisible to the subject reading; its sweeps
    /// ("this complex's cell masks") read here instead. Additive: the
    /// landed subject-keyed paths are untouched.
    rel_by_arg: HashMap<u32, Vec<RelRow>>,
    /// Relation-instance rows whose first argument is an EXTERNAL
    /// element ref — the external-subject clause, relation-row twin:
    /// structurally invisible to `rel_attrs` (keyed on local
    /// counters), reported here instead of vanishing. A local element
    /// can never alias an external ref (a body's hash is unknowable at
    /// authoring, so its deps table cannot cite itself), so
    /// subject-scoped sweeps over a LOCAL element are complete without
    /// this surface; universal-posture consumers consult it.
    rel_external_subject: Vec<RelRow>,
    /// The same relation-instance rows keyed by RELATION identity —
    /// the whole-context enumeration surface ("every row of this
    /// relation in view"), for consumers whose demand quantifies
    /// globally rather than from a known element (the asel both-slots
    /// sweep: the theory's refusal reads "anywhere", so the walk must
    /// see rows citing elements it has never reached). Shape-blind by
    /// design: rows whose arguments are literals or EXTERNAL refs —
    /// structurally invisible to the subject-/citation-keyed views —
    /// are indexed here too, so no row dodges the quantifier. Same
    /// malformation posture as every other view: this REPORTS rows as
    /// written (duplicates included); the evaluator dedups, filters,
    /// and refuses.
    rel_by_rel: HashMap<Chid, Vec<RelRow>>,
}

impl CertRows {
    /// The empty context: every element-argument oracle called against
    /// it refuses loudly (the bare `eval` path for literal families).
    pub fn empty() -> CertRows {
        CertRows::default()
    }

    /// Index a body's ops. `own` is the body's commit hash, `deps` its
    /// CHID list — fun refs normalize to pinned identities through them
    /// (the same normalization every other loader in this crate uses).
    pub fn from_ops(ops: &[Op], own: [u8; 32], deps: &[[u8; 32]]) -> CertRows {
        let mut by_value: HashMap<u32, Vec<CtorRow>> = HashMap::new();
        let mut by_arg: HashMap<u32, Vec<CtorRow>> = HashMap::new();
        let mut by_subject: HashMap<u32, Vec<AttrRow>> = HashMap::new();
        let mut external_subject: Vec<AttrRow> = Vec::new();
        let mut rel_by_subject: HashMap<u32, Vec<RelRow>> = HashMap::new();
        let mut rel_by_arg: HashMap<u32, Vec<RelRow>> = HashMap::new();
        let mut rel_external_subject: Vec<RelRow> = Vec::new();
        let mut rel_by_rel: HashMap<Chid, Vec<RelRow>> = HashMap::new();
        for op in ops {
            let Op::Funa { fun, args, value } = op else {
                if let Op::Rela { rel, args } = op {
                    let row = RelRow {
                        rel: norm(rel, own, deps),
                        args: args.clone(),
                    };
                    // Relation direction: every Rela op, regardless of
                    // argument shape (the enumeration surface).
                    rel_by_rel.entry(row.rel).or_default().push(row.clone());
                    // Citation direction: once per DISTINCT local arg
                    // elem, any position (the fun-row `by_arg` twin).
                    let mut seen_args: Vec<u32> = Vec::with_capacity(args.len());
                    for a in args {
                        if let Value::Ref(ElemRef::Local(e)) = a {
                            if !seen_args.contains(e) {
                                seen_args.push(*e);
                                rel_by_arg.entry(*e).or_default().push(row.clone());
                            }
                        }
                    }
                    match args.first() {
                        Some(Value::Ref(ElemRef::Local(subject))) => {
                            rel_by_subject.entry(*subject).or_default().push(row);
                        }
                        Some(Value::Ref(ElemRef::External { .. })) => {
                            rel_external_subject.push(row);
                        }
                        // Literal or absent first arg: no subject in
                        // this reading (such a row is about no element;
                        // consumers that would care refuse elsewhere).
                        _ => {}
                    }
                }
                continue;
            };
            match args.first() {
                Some(Value::Ref(ElemRef::Local(subject))) => {
                    by_subject.entry(*subject).or_default().push(AttrRow {
                        fun: norm(fun, own, deps),
                        args: args.clone(),
                        value: value.clone(),
                    });
                }
                Some(Value::Ref(ElemRef::External { .. })) => {
                    external_subject.push(AttrRow {
                        fun: norm(fun, own, deps),
                        args: args.clone(),
                        value: value.clone(),
                    });
                }
                // Literal or absent first arg: not an element, so not a
                // subject in either reading (an entity variable can only
                // be instantiated by an element; constructor rows with
                // literal first fields are the normal case here).
                _ => {}
            }
            let row = CtorRow {
                fun: norm(fun, own, deps),
                args: args.clone(),
                value: value.clone(),
            };
            // Arg direction: index once per DISTINCT local arg elem (a
            // row citing the same elem twice files once there).
            let mut seen_args: Vec<u32> = Vec::with_capacity(args.len());
            for a in args {
                if let Value::Ref(ElemRef::Local(e)) = a {
                    if !seen_args.contains(e) {
                        seen_args.push(*e);
                        by_arg.entry(*e).or_default().push(row.clone());
                    }
                }
            }
            // Value (constructor) direction, as before. The row for a
            // value that is also a field target appears in both maps —
            // both readings are true of it.
            if let Value::Ref(ElemRef::Local(elem)) = value {
                by_value.entry(*elem).or_default().push(row);
            }
        }
        CertRows {
            own,
            deps: deps.to_vec(),
            by_value,
            by_arg,
            by_subject,
            external_subject,
            rel_by_subject,
            rel_by_arg,
            rel_external_subject,
            rel_by_rel,
        }
    }

    /// Every fun-value row producing `elem`, in body order.
    pub fn producers(&self, elem: u32) -> &[CtorRow] {
        self.by_value.get(&elem).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Every fun-value row with `elem` in an argument position, in body
    /// order — the field-access reading (the node walks). The
    /// caller filters by its own pinned fun identities.
    pub fn arg_rows(&self, elem: u32) -> &[CtorRow] {
        self.by_arg.get(&elem).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Every fun-value row whose FIRST argument is `subject`, in body
    /// order — the attribute view (entity-like sorts: `QBlockLattice`).
    /// Same malformation posture as [`Self::producers`]: this REPORTS;
    /// the evaluator refuses on ambiguity.
    pub fn attrs(&self, subject: u32) -> &[AttrRow] {
        self.by_subject
            .get(&subject)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Every subject element carrying at least one attribute row,
    /// ascending — the premise-enumeration surface for admission chase
    /// consumers (the admission-quantification clause: universally quantified entity vars range
    /// over the body's subjects). Sorted so consumers' verdicts and
    /// refusal messages are deterministic across runs.
    pub fn subject_elems(&self) -> Vec<u32> {
        let mut v: Vec<u32> = self.by_subject.keys().copied().collect();
        v.sort_unstable();
        v
    }

    /// Every row whose first argument is an EXTERNAL element ref, in
    /// body order (the external-subject clause). These rows are structurally invisible to
    /// [`Self::subject_elems`]/[`Self::attrs`] (both keyed on local
    /// counters), so a consumer whose posture is "the universal loop
    /// sees every subject" must consult this surface and refuse on the
    /// funs it quantifies over — otherwise external-subject premise
    /// instances silently dodge quantification.
    pub fn external_subject_rows(&self) -> &[AttrRow] {
        &self.external_subject
    }

    /// Every relation-instance row whose FIRST argument is `subject`,
    /// in body order — the membership view (`Simplex/contains`,
    /// `ExtensionSet/contains`). The caller filters by its own pinned
    /// relation identities; same malformation posture as
    /// [`Self::attrs`].
    pub fn rel_attrs(&self, subject: u32) -> &[RelRow] {
        self.rel_by_subject
            .get(&subject)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Every relation-instance row whose first argument is an EXTERNAL
    /// element ref, in body order — the external-subject clause's
    /// relation-row twin (see the field docs for why subject-scoped
    /// sweeps over a local element are complete without it).
    pub fn rel_external_subject_rows(&self) -> &[RelRow] {
        &self.rel_external_subject
    }

    /// Every relation-instance row citing `elem` in ANY argument
    /// position, in body order — the citation reading ([`Self::arg_rows`]'s
    /// relation-row twin), for vocabulary whose wire order puts a
    /// literal field first. The caller filters by its own pinned
    /// relation identities AND verifies the cited position is the one
    /// it means (citation only guarantees membership); same
    /// malformation posture as [`Self::rel_attrs`].
    pub fn rel_rows_citing(&self, elem: u32) -> &[RelRow] {
        self.rel_by_arg.get(&elem).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Every relation-instance row of relation `rel`, in body order —
    /// the whole-context enumeration surface, for consumers whose
    /// demand quantifies globally ("anywhere") rather than from a
    /// known element. Complete over the body's rows regardless of
    /// argument shape: literal- and external-citing rows, invisible
    /// to the element-keyed views, are enumerated here too. The
    /// caller QUANTIFIES over these rows — it must resolve or refuse
    /// every one, never skip what it cannot read; same malformation
    /// posture as [`Self::rel_attrs`].
    pub fn rows_of(&self, rel: Chid) -> &[RelRow] {
        self.rel_by_rel.get(&rel).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Normalize a ref to a pinned identity against this body's tables.
    pub fn norm(&self, r: &ElemRef) -> Chid {
        norm(r, self.own, &self.deps)
    }

    /// A ref's local counter, iff it is a same-body element.
    pub fn local(&self, r: &ElemRef) -> Option<u32> {
        match r {
            ElemRef::Local(n) => Some(*n),
            ElemRef::External { .. } => None,
        }
    }
}

fn norm(r: &ElemRef, own: [u8; 32], deps: &[[u8; 32]]) -> Chid {
    match r {
        ElemRef::Local(n) => (own, *n),
        // Out-of-range dep index yields a sentinel no real identity
        // matches (C-DIX rejects upstream) — the crate-wide convention.
        ElemRef::External { dep_index, counter } => match deps.get(*dep_index as usize) {
            Some(h) => (*h, *counter),
            None => ([0xFFu8; 32], *counter),
        },
    }
}
