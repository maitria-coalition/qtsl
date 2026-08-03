//! `qtsl_init_member` / `qtsl_warrant_member` / `qtsl_spec_wf` /
//! `qtsl_cert_claim_wf`: the guarded-specification and satisfaction-claim
//! side-conditions — the initial-membership demand, the
//! warrant-component membership, the C-SPEC / C-SPEC-GUARD record walk,
//! and the C-CERT-CLAIM per-claim conformance walk, as row-context
//! recomputes.
//!
//! Semantic authority: the Qtsl theory's satisfaction-judgment block
//! ("The satisfaction judgments" — `QSat`, `qsat_warrant`, `qsat_eval`,
//! the initial-membership and warrant-membership demand comments), the
//! guarded-specification block (`spec_guard`, `qsat_guard_warrant`, the
//! region tie), and the Specifications block (the spec-record
//! relations, `spec_consumes` traversal, and the C-SPEC walk comment
//! beside `qtsl_spec_wf`). The chase rows `ax/wf/qsat_init`,
//! `ax/wf/qsat_warrant_member` + `ax/wf/qguard_warrant_member`,
//! `ax/wf/spec_wf`, and `ax/wf/cert_claim_wf` demand these relations;
//! this module is their evaluator.
//!
//! # `qtsl_init_member` (the initial-membership demand)
//!
//! "Discharged per constructor pair at the ground seam …, loudly
//! deferred while unrealized." Realized pairs, both on `qraBox`
//! regions over `SysMech` subjects:
//!
//! - **bag-marking point**: the mechanism's `mech_bag_marking` rows plus
//!   the `mech_bag_wire` bijection give the marking vector `m0` indexed
//!   by wire (a token with a marking row but no wire row, duplicate
//!   wire rows, a shared or out-of-block wire index all REFUSE with
//!   locus — the bijection's conformance verdict belongs to C-BAG, not
//!   here); the region box pairs interval `i` with wire `i`, its length
//!   must equal the block width (mismatch REFUSES — width discipline,
//!   never silent truncation), and the claim holds iff
//!   `lo_w <= m0_w <= hi_w` on every wire, exact rational.
//! - **init boxes**: a mechanism carrying `mech_init_box` rows instead
//!   of bag rows holds iff EVERY init box is contained in the region
//!   box per coordinate (the demonic-union reading); a width mismatch
//!   refuses.
//!
//! Everything else — `qraSublevel`/`qraAffine` regions, `SysWire`
//! composites, holed subjects, mechanisms with neither content family,
//! a mechanism with both — refuses with the unrealized constructor
//! pair named.
//!
//! # `qtsl_warrant_member` (C-CERT-CLAIM membership)
//!
//! `f` is reachable from the spec's consumed ForallSpec set: its own
//! `spec_forall` rows plus recursion through `spec_or` arms (the
//! `spec_consumes` traversal, recomputed post-saturation "through any
//! depth of disjunction"). Element identity is hash-consed cell
//! equality — the component cell is compared, never decoded. A
//! completed walk without a hit decides false; the walk is
//! reachability over a visited set, so or-graph cycles cannot diverge
//! it (acyclicity is C-SPEC's verdict, not this one's).
//!
//! # `qtsl_spec_wf` (C-SPEC + C-SPEC-GUARD)
//!
//! Per the record's own well-formedness walk comment, in order:
//! at-most-one `spec_name`/`spec_iface`/`spec_slack`/`spec_guard`/
//! `spec_or` rows (NOTE: `spec_assume` is zero-or-more by the theory's
//! own comment — it is deliberately NOT counted); component presence
//! (the empty record claims nothing); disjunction exclusive with
//! component rows; or-graph acyclicity (decided false — "admission
//! conformance (C-SPEC), the list-cycle posture"); the guard-vs-warrant
//! agreement (PD-6 store-and-check: for every `qsat_guard_warrant` row
//! whose sat's `QSat/spec` is this spec, a stored `spec_guard` row must
//! exist and its region must be cell-equal to the warrant's
//! `QForallSat/region` (the warrant is a forall-face ENTITY since
//! revision event 6 — which component it warrants is intrinsic via
//! `QForallSat/component`, so the earlier edition's in-row f-field and
//! its refuse-mode root ties are unrepresentable rather than checked)
//! — absent-or-disagreeing decides false, the
//! derived second row on a one-region slot counted post-saturation);
//! and the residual negation-parity walk over the safety-face
//! components. The demo grammar (`SInit`, `SProbGE`, `SAtomLE`/`GE`
//! over `oPoly` observables, `SAnd`, `STrue`, `PAlways`) contains no
//! negation, so parity is trivially lawful; `SNot`, Streett meters,
//! and every constructor outside the implemented set REFUSE with the
//! constructor named (honest incompleteness). Liveness-mark and
//! attitude components likewise refuse — the walk is implemented for
//! the safety face only.
//!
//! # `qtsl_base_exact` (the Θ₀ positive membership — review F-2)
//!
//! "The evaluator admits exactly the Θ₀ grammar and refuses-or-defers
//! everything else, unknown extension constructors included" (the
//! base-stratum refinement block, beside `ax/wf/request_base_demand`
//! and `ax/wf/assume_base_demand` — the PairBase and `spec_assume`
//! demand loci). Tri-state, per the family's verdict discipline:
//!
//! - **true**: `STrue`/`SFalse`; `SAtomLE`/`SAtomGE` whose observable
//!   is an actual `oPoly` image; `SAnd`/`SOr` all of whose members are
//!   base — exactly the Θ₀ grammar, positively walked.
//! - **false** (decided): the formers the refinement itself proves
//!   nonbase — `SNot`, and atoms over the `oChan`/`oGate`/`oInd`
//!   injections; one decidedly-nonbase member decides a whole
//!   `SAnd`/`SOr` false (the `has_nonbase` propagation), even when a
//!   sibling member is undecodable.
//! - **refuse**: an observable outside the four injections ("not
//!   provably nonbase yet not base either"), a state-predicate former
//!   outside the grammar (unknown extension constructors), and the
//!   usual undecidable structure (unconstructed elements, budgets).
//!
//! # `qtsl_cert_claim_wf` (C-CERT-CLAIM)
//!
//! At most one `qsat_warrant` row, at most one `qsat_guard_warrant`
//! row, never both (route exclusivity), at most one `qsat_eval` row —
//! each violation decided false. The hole ledger is realized for the
//! ZERO-HOLE case only: regret components (`SRegretLE` /
//! `SRegretLEMark`, when the closure declares them) and holed subjects
//! (`SysHole` anywhere in the subject tree — composites are walked)
//! REFUSE, named; a closure that never declares the regret/hole
//! vocabulary cannot mint such rows and rides the fast path.
//!
//! Verdict discipline (the CtxArg pattern, inherited from
//! [`crate::trwf`]): a decided violation is `Ok(false)`; anything the
//! row context cannot decide (unconstructed or ambiguous elements,
//! absent exactly-one attributes, out-of-fragment constructors,
//! exhausted budgets) REFUSES, never guesses.
//!
//! Vocabulary-resolution note (the shadowing-tolerant sweep): the
//! event-4 grid re-sort RENAMED the spec-former sorts (StatePred was
//! StateF) and re-founded the atoms (`SAtomLE {c, o}` where the
//! retired generation had a polynomial field), while same-name
//! declarations of the retired generation may survive in other swept
//! revisions (the synthetic fixture stack does exactly this to keep
//! retired-shape families testable). The resolvers here therefore
//! skip same-name declarations whose shape disagrees and pin the
//! declaration whose shape matches the event-4 grammar, refusing on
//! zero matches or on two distinct matching identities — names
//! select, shapes co-select, identities pin.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, GuardKind, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, FieldPred, Ground, OwnedFieldPred, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::collections::{HashMap, HashSet};

/// The guard family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Field names and bytewise order are
/// part of the claim.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_init_member",
        &[("region", "QRegionAtom"), ("sys", "System")],
        RelKind::Guard(GuardKind::InitMember),
    ),
    (
        "qtsl_warrant_member",
        &[("f", "ForallSpec"), ("spec", "Spec")],
        RelKind::Guard(GuardKind::WarrantMember),
    ),
    (
        "qtsl_spec_wf",
        &[("spec", "Spec")],
        RelKind::Guard(GuardKind::SpecWf),
    ),
    (
        "qtsl_cert_claim_wf",
        &[("sat", "QSat")],
        RelKind::Guard(GuardKind::CertClaimWf),
    ),
    (
        "qtsl_base_exact",
        &[("f", "StatePred")],
        RelKind::Guard(GuardKind::BaseExact),
    ),
];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const GUARD_MAX_MARKINGS: usize = 1 << 16;
pub const GUARD_MAX_VEC: usize = 1 << 12;
/// Formula-tree recursion depth cap (stack safety: the step budget
/// alone would admit a recursion deeper than the thread stack).
pub const GUARD_MAX_DEPTH: usize = 1 << 12;
pub const GUARD_MAX_SPECS: usize = 1 << 12;
pub const GUARD_MAX_TREE: usize = 1 << 16;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The guarded-specification vocabulary, pinned at resolution.
#[derive(Debug, Clone)]
pub struct GuardVocab {
    // spec-record relations
    spec_forall: Chid,
    spec_exists: Chid,
    spec_score: Chid,
    spec_name: Chid,
    spec_iface: Chid,
    spec_slack: Chid,
    spec_or: Chid,
    spec_guard: Chid,
    // satisfaction-claim relations
    qsat_warrant: Chid,
    qsat_guard_warrant: Chid,
    qsat_eval: Chid,
    // subject content relations
    mech_bag_marking: Chid,
    mech_bag_wire: Chid,
    mech_init_box: Chid,
    // exactly-one attributes
    qsat_spec: Chid,
    qsat_sys: Chid,
    /// `QForallSat/region` — the warrant entity's region (the
    /// event-6 seam; the component attribute exists too but no walk
    /// here reads it: the membership demand arrives pre-projected as
    /// `qtsl_warrant_member {f, spec}` args).
    qfs_region: Chid,
    // constructors
    sys_mech: Chid,
    sys_wire: Chid,
    sys_hole: Option<Chid>,
    sy_nil: Chid,
    sy_cons: Chid,
    qra_box: Chid,
    qra_sublevel: Chid,
    qra_affine: Chid,
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    s_init: Chid,
    s_prob_ge: Chid,
    s_true: Chid,
    s_false: Chid,
    s_atom_le: Chid,
    s_atom_ge: Chid,
    s_and: Chid,
    s_or: Chid,
    s_not: Chid,
    sl_nil: Chid,
    sl_cons: Chid,
    o_poly: Chid,
    /// The three non-polynomial observable injections — provably
    /// nonbase at atoms (`ax/nonbase_atom_*`). Optional: a closure
    /// that never declares one cannot construct over it either.
    o_chan: Option<Chid>,
    o_gate: Option<Chid>,
    o_ind: Option<Chid>,
    p_always: Chid,
    s_regret_le: Option<Chid>,
    s_regret_le_mark: Option<Chid>,
    // sorts the structural walks key on
    system_sort: Chid,
    syslist_sort: Chid,
    region_sort: Chid,
    box_sort: Chid,
    interval_sort: Chid,
    forall_sort: Chid,
    statepred_sort: Chid,
    spl_sort: Chid,
    stateobs_sort: Chid,
    pathpred_sort: Chid,
    /// Per-sort constructor rosters (sort chid → fun chid → domain), so
    /// "constructed outside the roster" is malformation, distinct from
    /// "not constructed in view" (refusal).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
    /// Declared names, for refusal messages that name the constructor
    /// they defer on.
    names: HashMap<Chid, String>,
}

impl GuardVocab {
    fn name_of(&self, c: Chid) -> &str {
        self.names
            .get(&c)
            .map(String::as_str)
            .unwrap_or("<undeclared fun>")
    }
}

/// Resolve a sort by name across the swept indices, refusing
/// cross-revision ambiguity (the provider-wide posture).
fn sort_by_name(indices: &[&TheoryIndex], name: &str) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        if let Some(c) = index.sort(name) {
            match found {
                None => found = Some(c),
                Some(f) if f == c => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` names two distinct sorts across the swept \
                         revisions — ambiguous, refusing to pick"
                    ))
                }
            }
        }
    }
    found.ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
}

/// The shadowing-tolerant constructor find (module doc): sweep every
/// index, keep only declarations whose codomain AND domain shape match,
/// refuse zero matches and cross-revision ambiguity.
fn find_ctor(
    indices: &[&TheoryIndex],
    name: &str,
    want_cod: Chid,
    check: &dyn Fn(&DomainSig) -> bool,
) -> Result<(Chid, DomainSig), String> {
    let mut found: Option<(Chid, DomainSig)> = None;
    for index in indices {
        let Some(d) = index.fun(name) else { continue };
        if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) || !check(&d.domain) {
            continue; // a same-name declaration of another generation
        }
        match &found {
            None => found = Some((d.chid, d.domain.clone())),
            Some((c, _)) if *c == d.chid => {}
            Some(_) => {
                return Err(format!(
                    "`{name}` has two distinct shape-matching declarations \
                     across the swept revisions — ambiguous, refusing to pick"
                ))
            }
        }
    }
    found.ok_or_else(|| {
        format!("no `{name}` constructor with the expected event-4 shape among the swept revisions")
    })
}

/// The shadowing-tolerant relation find: declared fields (names, in
/// bytewise order) and per-field kind predicates must match.
fn find_rel(indices: &[&TheoryIndex], name: &str, want: &[FieldPred]) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        let Some(d) = index.fun(name) else { continue };
        let shape_ok = d.relational
            && d.codomain.is_none()
            && match &d.domain {
                DomainSig::Record(fields) => {
                    fields.len() == want.len()
                        && fields
                            .iter()
                            .zip(want.iter())
                            .all(|((n, s), (wn, wf))| n == wn && wf(s))
                }
                _ => false,
            };
        if !shape_ok {
            continue;
        }
        match found {
            None => found = Some(d.chid),
            Some(c) if c == d.chid => {}
            Some(_) => {
                return Err(format!(
                    "`{name}` has two distinct shape-matching declarations \
                     across the swept revisions — ambiguous, refusing to pick"
                ))
            }
        }
    }
    found.ok_or_else(|| {
        format!("no `{name}` relation with the expected event-4 shape among the swept revisions")
    })
}

/// The shadowing-tolerant attribute find: unary on `subject`, codomain
/// `want_cod`.
fn find_attr(
    indices: &[&TheoryIndex],
    name: &str,
    subject: Chid,
    want_cod: Chid,
) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        let Some(d) = index.fun(name) else { continue };
        if d.relational
            || d.domain != DomainSig::Unary(SortKey::Elem(subject))
            || d.codomain != Some(SortKey::Elem(want_cod))
        {
            continue;
        }
        match found {
            None => found = Some(d.chid),
            Some(c) if c == d.chid => {}
            Some(_) => {
                return Err(format!(
                    "`{name}` has two distinct shape-matching declarations \
                     across the swept revisions — ambiguous, refusing to pick"
                ))
            }
        }
    }
    found.ok_or_else(|| {
        format!("no `{name}` attribute with the expected event-4 shape among the swept revisions")
    })
}

/// Build the guard vocabulary over the declared indices. `Err` → the
/// family is not claimed (declared-but-unbound, safe-fail; reason on
/// the provider's vocabulary notes).
pub fn build_guard_vocab(indices: &[&TheoryIndex]) -> Result<GuardVocab, String> {
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    let is_str = |s: &SortKey| *s == SortKey::Ground(Ground::Str);
    fn is_elem_eq(want: Chid) -> impl Fn(&SortKey) -> bool {
        move |s: &SortKey| *s == SortKey::Elem(want)
    }
    let unary_of = |want: Chid| move |s: &DomainSig| *s == DomainSig::Unary(SortKey::Elem(want));
    let record_of = |want: Vec<OwnedFieldPred>| {
        move |s: &DomainSig| match s {
            DomainSig::Record(fields) => {
                fields.len() == want.len()
                    && fields
                        .iter()
                        .zip(want.iter())
                        .all(|((n, k), (wn, wf))| n == wn && wf(k))
            }
            _ => false,
        }
    };
    let bx = |f: fn(&SortKey) -> bool| -> Box<dyn Fn(&SortKey) -> bool> { Box::new(f) };
    let bq = || -> Box<dyn Fn(&SortKey) -> bool> {
        Box::new(|s: &SortKey| *s == SortKey::Ground(Ground::Q))
    };
    let be = |want: Chid| -> Box<dyn Fn(&SortKey) -> bool> { Box::new(is_elem_eq(want)) };

    // --- anchor sorts ------------------------------------------------
    let spec_sort = sort_by_name(indices, "Spec")?;
    let system_sort = sort_by_name(indices, "System")?;
    let syslist_sort = sort_by_name(indices, "SystemList")?;
    let mech_sort = sort_by_name(indices, "Mech")?;
    let qsat_sort = sort_by_name(indices, "QSat")?;
    let qfs_sort = sort_by_name(indices, "QForallSat")?;
    let region_sort = sort_by_name(indices, "QRegionAtom")?;
    let forall_sort = sort_by_name(indices, "ForallSpec")?;
    let statepred_sort = sort_by_name(indices, "StatePred")?;
    let spl_sort = sort_by_name(indices, "StatePredList")?;
    let stateobs_sort = sort_by_name(indices, "StateObservable")?;
    let pathpred_sort = sort_by_name(indices, "PathPred")?;
    let box_sort = sort_by_name(indices, "Box")?;
    let interval_sort = sort_by_name(indices, "Interval")?;

    // --- spec-record relations (fields in bytewise order) -------------
    let spec_forall = find_rel(
        indices,
        "spec_forall",
        &[
            ("f", &is_elem_eq(forall_sort)),
            ("spec", &is_elem_eq(spec_sort)),
        ],
    )?;
    let spec_exists = find_rel(
        indices,
        "spec_exists",
        &[("e", &is_elem), ("spec", &is_elem_eq(spec_sort))],
    )?;
    let spec_score = find_rel(
        indices,
        "spec_score",
        &[("h", &is_elem), ("spec", &is_elem_eq(spec_sort))],
    )?;
    let spec_name = find_rel(
        indices,
        "spec_name",
        &[("name", &is_str), ("spec", &is_elem_eq(spec_sort))],
    )?;
    let spec_iface = find_rel(
        indices,
        "spec_iface",
        &[("iface", &is_elem), ("spec", &is_elem_eq(spec_sort))],
    )?;
    let spec_slack = find_rel(
        indices,
        "spec_slack",
        &[("slack", &is_elem), ("spec", &is_elem_eq(spec_sort))],
    )?;
    let spec_or = find_rel(
        indices,
        "spec_or",
        &[
            ("left", &is_elem_eq(spec_sort)),
            ("right", &is_elem_eq(spec_sort)),
            ("spec", &is_elem_eq(spec_sort)),
        ],
    )?;
    let spec_guard = find_rel(
        indices,
        "spec_guard",
        &[
            ("region", &is_elem_eq(region_sort)),
            ("spec", &is_elem_eq(spec_sort)),
        ],
    )?;

    // --- satisfaction-claim relations (the event-6 wire shape: the
    // warrant is a QForallSat entity; the retired edition's in-row
    // f-field is intrinsic to the entity as QForallSat/component) ----
    let warrant_fields: &[FieldPred] = &[
        ("sat", &is_elem_eq(qsat_sort)),
        ("warrant", &is_elem_eq(qfs_sort)),
    ];
    let qsat_warrant = find_rel(indices, "qsat_warrant", warrant_fields)?;
    let qsat_guard_warrant = find_rel(indices, "qsat_guard_warrant", warrant_fields)?;
    let qsat_eval = find_rel(
        indices,
        "qsat_eval",
        &[("eval", &is_elem), ("sat", &is_elem_eq(qsat_sort))],
    )?;

    // --- subject content relations ------------------------------------
    let mech_bag_marking = find_rel(
        indices,
        "mech_bag_marking",
        &[
            ("count", &is_nat),
            ("mech", &is_elem_eq(mech_sort)),
            ("token", &is_elem),
        ],
    )?;
    let mech_bag_wire = find_rel(
        indices,
        "mech_bag_wire",
        &[
            ("mech", &is_elem_eq(mech_sort)),
            ("token", &is_elem),
            ("wire", &is_nat),
        ],
    )?;
    let mech_init_box = find_rel(
        indices,
        "mech_init_box",
        &[
            ("box", &is_elem_eq(box_sort)),
            ("mech", &is_elem_eq(mech_sort)),
        ],
    )?;

    // --- exactly-one attributes ----------------------------------------
    let qsat_spec = find_attr(indices, "QSat/spec", qsat_sort, spec_sort)?;
    let qsat_sys = find_attr(indices, "QSat/sys", qsat_sort, system_sort)?;
    let qfs_region = find_attr(indices, "QForallSat/region", qfs_sort, region_sort)?;

    // --- constructors ----------------------------------------------------
    let (sys_mech, _) = find_ctor(
        indices,
        "SysMech",
        system_sort,
        &record_of(vec![("mech", be(mech_sort))]),
    )?;
    let (sys_wire, _) = find_ctor(
        indices,
        "SysWire",
        system_sort,
        &record_of(vec![("inner", be(syslist_sort)), ("wiring", bx(is_elem))]),
    )?;
    let sys_hole = find_ctor(
        indices,
        "SysHole",
        system_sort,
        &record_of(vec![("iface", bx(is_elem))]),
    )
    .ok()
    .map(|(c, _)| c);
    let (sy_nil, _) = find_ctor(indices, "syNil", syslist_sort, &|s| {
        *s == DomainSig::Nullary
    })?;
    let (sy_cons, _) = find_ctor(
        indices,
        "syCons",
        syslist_sort,
        &record_of(vec![("head", be(system_sort)), ("tail", be(syslist_sort))]),
    )?;
    let (qra_box, _) = find_ctor(indices, "qraBox", region_sort, &unary_of(box_sort))?;
    let (qra_sublevel, _) = find_ctor(
        indices,
        "qraSublevel",
        region_sort,
        &record_of(vec![("cert", bx(is_elem)), ("thr", bq())]),
    )?;
    let (qra_affine, _) = find_ctor(
        indices,
        "qraAffine",
        region_sort,
        &record_of(vec![("row", bx(is_elem)), ("thr", bq())]),
    )?;
    let (box_nil, _) = find_ctor(indices, "boxNil", box_sort, &|s| *s == DomainSig::Nullary)?;
    let (box_cons, _) = find_ctor(
        indices,
        "boxCons",
        box_sort,
        &record_of(vec![("head", be(interval_sort)), ("tail", be(box_sort))]),
    )?;
    let (mk_interval, _) = find_ctor(
        indices,
        "mkInterval",
        interval_sort,
        &record_of(vec![("hi", bq()), ("lo", bq())]),
    )?;
    let (s_init, _) = find_ctor(
        indices,
        "SInit",
        forall_sort,
        &record_of(vec![("arg", be(statepred_sort))]),
    )?;
    let (s_prob_ge, _) = find_ctor(
        indices,
        "SProbGE",
        forall_sort,
        &record_of(vec![("p", bq()), ("path", be(pathpred_sort))]),
    )?;
    let (s_true, _) = find_ctor(indices, "STrue", statepred_sort, &|s| {
        *s == DomainSig::Nullary
    })?;
    let (s_atom_le, _) = find_ctor(
        indices,
        "SAtomLE",
        statepred_sort,
        &record_of(vec![("c", bq()), ("o", be(stateobs_sort))]),
    )?;
    let (s_atom_ge, _) = find_ctor(
        indices,
        "SAtomGE",
        statepred_sort,
        &record_of(vec![("c", bq()), ("o", be(stateobs_sort))]),
    )?;
    let (s_and, _) = find_ctor(indices, "SAnd", statepred_sort, &unary_of(spl_sort))?;
    let (s_false, _) = find_ctor(indices, "SFalse", statepred_sort, &|s| {
        *s == DomainSig::Nullary
    })?;
    let (s_or, _) = find_ctor(indices, "SOr", statepred_sort, &unary_of(spl_sort))?;
    let (s_not, _) = find_ctor(indices, "SNot", statepred_sort, &unary_of(statepred_sort))?;
    let (sl_nil, _) = find_ctor(indices, "slNil", spl_sort, &|s| *s == DomainSig::Nullary)?;
    let (sl_cons, _) = find_ctor(
        indices,
        "slCons",
        spl_sort,
        &record_of(vec![("head", be(statepred_sort)), ("tail", be(spl_sort))]),
    )?;
    let (o_poly, _) = find_ctor(
        indices,
        "oPoly",
        stateobs_sort,
        &record_of(vec![("poly", bx(is_elem))]),
    )?;
    let o_chan = find_ctor(
        indices,
        "oChan",
        stateobs_sort,
        &record_of(vec![("chan", bx(|s| *s == SortKey::Ground(Ground::Nat)))]),
    )
    .ok()
    .map(|(c, _)| c);
    let o_gate = find_ctor(
        indices,
        "oGate",
        stateobs_sort,
        &record_of(vec![("gate", bx(is_elem))]),
    )
    .ok()
    .map(|(c, _)| c);
    let o_ind = find_ctor(
        indices,
        "oInd",
        stateobs_sort,
        &record_of(vec![("arg", be(statepred_sort))]),
    )
    .ok()
    .map(|(c, _)| c);
    let (p_always, _) = find_ctor(indices, "PAlways", pathpred_sort, &unary_of(statepred_sort))?;
    let s_regret_le = find_ctor(
        indices,
        "SRegretLE",
        forall_sort,
        &record_of(vec![
            ("eps", bq()),
            ("pi", be(system_sort)),
            ("ret", bx(is_elem)),
        ]),
    )
    .ok()
    .map(|(c, _)| c);
    // The mark face lives on ExistsSpec — resolved by name + shape
    // without an anchor sort (its codomain is whatever the closure
    // declares ExistsSpec as; the eps/ret record shape plus NOT being
    // a ForallSpec constructor identifies it).
    let s_regret_le_mark = (|| {
        let exists_sort = sort_by_name(indices, "ExistsSpec").ok()?;
        find_ctor(
            indices,
            "SRegretLEMark",
            exists_sort,
            &record_of(vec![("eps", bq()), ("ret", bx(is_elem))]),
        )
        .ok()
        .map(|(c, _)| c)
    })();

    // --- per-sort constructor rosters + the name table -------------------
    let kit_sorts = [
        system_sort,
        syslist_sort,
        region_sort,
        box_sort,
        interval_sort,
        forall_sort,
        statepred_sort,
        spl_sort,
        stateobs_sort,
        pathpred_sort,
    ];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in kit_sorts {
        ctors.entry(s).or_default();
    }
    let mut names: HashMap<Chid, String> = HashMap::new();
    for index in indices {
        for decl in &index.funs {
            names.insert(decl.chid, decl.name.clone());
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
    let _ = is_q; // kept for symmetry with sibling builders

    Ok(GuardVocab {
        spec_forall,
        spec_exists,
        spec_score,
        spec_name,
        spec_iface,
        spec_slack,
        spec_or,
        spec_guard,
        qsat_warrant,
        qsat_guard_warrant,
        qsat_eval,
        mech_bag_marking,
        mech_bag_wire,
        mech_init_box,
        qsat_spec,
        qsat_sys,
        qfs_region,
        sys_mech,
        sys_wire,
        sys_hole,
        sy_nil,
        sy_cons,
        qra_box,
        qra_sublevel,
        qra_affine,
        box_nil,
        box_cons,
        mk_interval,
        s_init,
        s_prob_ge,
        s_true,
        s_false,
        s_atom_le,
        s_atom_ge,
        s_and,
        s_or,
        s_not,
        sl_nil,
        sl_cons,
        o_poly,
        o_chan,
        o_gate,
        o_ind,
        p_always,
        s_regret_le,
        s_regret_le_mark,
        system_sort,
        syslist_sort,
        region_sort,
        box_sort,
        interval_sort,
        forall_sort,
        statepred_sort,
        spl_sort,
        stateobs_sort,
        pathpred_sort,
        ctors,
        names,
    })
}

// ---------------------------------------------------------------------
// The pure combinatorial cores (exposed so tests hit them directly)
// ---------------------------------------------------------------------

/// A decided violation — the named reason behind an `Ok(false)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GuardViolation {
    /// `m0_w` outside `[lo_w, hi_w]` (the initial-membership demand).
    InitCoordinateOutside { wire: usize },
    /// An init box not contained in the region box (demonic union).
    InitBoxNotContained { box_index: usize, axis: usize },
}

impl std::fmt::Display for GuardViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GuardViolation::InitCoordinateOutside { wire } => {
                write!(
                    f,
                    "initial marking coordinate {wire} lies outside the region interval"
                )
            }
            GuardViolation::InitBoxNotContained { box_index, axis } => write!(
                f,
                "init box {box_index}, axis {axis}: not contained in the region box"
            ),
        }
    }
}

/// The bag-marking-point membership: `lo_w <= m0_w <= hi_w` on every
/// wire, exact rational. Caller guarantees equal lengths (width
/// discipline is a refusal upstream, never a silent truncation here).
pub fn check_marking_membership(m0: &[QQ], region: &[(QQ, QQ)]) -> Result<(), GuardViolation> {
    debug_assert_eq!(m0.len(), region.len());
    for (w, (m, (lo, hi))) in m0.iter().zip(region.iter()).enumerate() {
        if lo.cmp_qq(m) == std::cmp::Ordering::Greater
            || m.cmp_qq(hi) == std::cmp::Ordering::Greater
        {
            return Err(GuardViolation::InitCoordinateOutside { wire: w });
        }
    }
    Ok(())
}

/// Per-coordinate interval containment of one init box in the region
/// box (`region.lo <= init.lo` and `init.hi <= region.hi`). Caller
/// guarantees equal lengths.
pub fn check_box_containment(
    box_index: usize,
    region: &[(QQ, QQ)],
    init: &[(QQ, QQ)],
) -> Result<(), GuardViolation> {
    debug_assert_eq!(region.len(), init.len());
    for (axis, ((rlo, rhi), (ilo, ihi))) in region.iter().zip(init.iter()).enumerate() {
        if rlo.cmp_qq(ilo) == std::cmp::Ordering::Greater
            || ihi.cmp_qq(rhi) == std::cmp::Ordering::Greater
        {
            return Err(GuardViolation::InitBoxNotContained { box_index, axis });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Row-context decode + evaluation
// ---------------------------------------------------------------------

fn ctx_err(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index: 0,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a GuardVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                ctx_err(
                    self.name,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: self.name.into(),
                index: 0,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    }

    /// The sole rostered constructor row producing `elem` on `sort`.
    fn sole(&mut self, sort: Chid, elem: u32) -> Result<&'a CtorRow, EvalError> {
        self.step()?;
        let roster = self.v.ctors.get(&sort).expect("kit sorts rostered");
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
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
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`; absence and
    /// duplication both refuse (exactly-one attributes).
    fn sole_attr_required(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Value, EvalError> {
        self.step()?;
        let mut found: Option<&Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "`{what}` stated twice on element {subject} — ambiguous \
                         (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(&row.value);
        }
        found.cloned().ok_or_else(|| {
            ctx_err(
                self.name,
                format!(
                    "element {subject} has no `{what}` row — an exactly-one \
                     attribute is absent, the element denotes nothing in view; \
                     refusing"
                ),
            )
        })
    }

    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            format!("`{what}` is not an exact-Q literal — malformed rows"),
        ))
    }

    fn nat_lit(&self, val: &Value, what: &str) -> Result<u64, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        Err(ctx_err(
            self.name,
            format!("`{what}` is not a Nat literal — malformed rows"),
        ))
    }

    /// Walk a nil/cons list into its head cells (budgeted, cycle-safe).
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        max: usize,
        what: &str,
    ) -> Result<Vec<Value>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head_elem;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} recurs along its own list tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            if out.len() > max {
                return Err(ctx_err(
                    self.name,
                    format!("{what} walk beyond its budget ({max}) — refusing"),
                ));
            }
            let row = self.sole(sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons pair — malformed rows"
                    ),
                ));
            }
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "cons row arity mismatch".into()));
            };
            out.push(head.clone());
            cur = self.elem(tail)?;
        }
    }

    /// DISTINCT relation rows of `rel` whose argument at `pos` is the
    /// local element `subject` (byte-identical rows are one row).
    fn distinct_rel_rows(
        &mut self,
        rel: Chid,
        pos: usize,
        subject: u32,
        arity: usize,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, EvalError> {
        self.step()?;
        let target = Value::Ref(ElemRef::Local(subject));
        let mut out: Vec<&RelRow> = Vec::new();
        for row in self.rows.rel_rows_citing(subject) {
            if row.rel != rel {
                continue;
            }
            if row.args.len() != arity {
                return Err(ctx_err(
                    self.name,
                    format!("`{what}` row arity mismatch — malformed rows"),
                ));
            }
            if row.args[pos] != target {
                continue;
            }
            if out.iter().any(|r| r.args == row.args) {
                continue;
            }
            out.push(row);
        }
        Ok(out)
    }

    /// A Box element's `(lo, hi)` interval list.
    fn box_intervals(&mut self, box_elem: u32) -> Result<Vec<(QQ, QQ)>, EvalError> {
        let cells = self.walk_list(
            self.v.box_sort,
            box_elem,
            self.v.box_nil,
            self.v.box_cons,
            GUARD_MAX_VEC,
            "region/init box",
        )?;
        let mut out = Vec::with_capacity(cells.len());
        for cell in cells {
            let iv = self.elem(&cell)?;
            let row = self.sole(self.v.interval_sort, iv)?;
            if row.fun != self.v.mk_interval {
                return Err(ctx_err(
                    self.name,
                    "box interval element is not an mkInterval — malformed rows".into(),
                ));
            }
            let [hi, lo] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "mkInterval row arity mismatch".into()));
            };
            out.push((
                self.q_lit(lo, "mkInterval/lo")?,
                self.q_lit(hi, "mkInterval/hi")?,
            ));
        }
        Ok(out)
    }

    /// The region element decoded to its `qraBox` interval list; the
    /// other region languages refuse with the constructor pair named.
    fn qra_box_intervals(
        &mut self,
        region: u32,
        against: &str,
    ) -> Result<Vec<(QQ, QQ)>, EvalError> {
        let rrow = self.sole(self.v.region_sort, region)?;
        if rrow.fun == self.v.qra_sublevel || rrow.fun == self.v.qra_affine {
            let which = self.v.name_of(rrow.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "region constructor `{which}` against {against} — this \
                     constructor pair is unrealized at the ground seam \
                     (loudly deferred); refusing, not deciding"
                ),
            ));
        }
        if rrow.fun != self.v.qra_box {
            return Err(ctx_err(
                self.name,
                format!(
                    "element {region} is constructed by a fun outside the \
                     qraBox/qraSublevel/qraAffine roster — malformed rows"
                ),
            ));
        }
        let [bx] = rrow.args.as_slice() else {
            return Err(ctx_err(self.name, "qraBox row arity mismatch".into()));
        };
        let be = self.elem(bx)?;
        self.box_intervals(be)
    }

    /// The subject tree's hole count (`SysMech` = 0, `SysHole` = 1,
    /// `SysWire` = the sum over its inner list), budgeted.
    fn hole_count(&mut self, sys: u32) -> Result<u64, EvalError> {
        let mut stack = vec![sys];
        let mut seen = 0usize;
        let mut holes = 0u64;
        while let Some(s) = stack.pop() {
            seen += 1;
            if seen > GUARD_MAX_TREE {
                return Err(ctx_err(
                    self.name,
                    format!("subject walk beyond its budget ({GUARD_MAX_TREE}) — refusing"),
                ));
            }
            let row = self.sole(self.v.system_sort, s)?;
            if row.fun == self.v.sys_mech {
                continue;
            }
            if Some(row.fun) == self.v.sys_hole {
                holes += 1;
                continue;
            }
            if row.fun == self.v.sys_wire {
                let [inner, _wiring] = row.args.as_slice() else {
                    return Err(ctx_err(self.name, "SysWire row arity mismatch".into()));
                };
                let ie = self.elem(inner)?;
                for cell in self.walk_list(
                    self.v.syslist_sort,
                    ie,
                    self.v.sy_nil,
                    self.v.sy_cons,
                    GUARD_MAX_VEC,
                    "composite inner list",
                )? {
                    stack.push(self.elem(&cell)?);
                }
                continue;
            }
            let which = self.v.name_of(row.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "subject constructor `{which}` — outside the \
                     SysMech/SysWire/SysHole roster in view; refusing"
                ),
            ));
        }
        Ok(holes)
    }

    // --- the residual negation-parity walk (safety face) ---------------

    fn walk_forall(&mut self, f: u32) -> Result<(), EvalError> {
        let row = self.sole(self.v.forall_sort, f)?;
        if row.fun == self.v.s_init {
            let [arg] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SInit row arity mismatch".into()));
            };
            let a = self.elem(arg)?;
            return self.walk_statepred(a);
        }
        if row.fun == self.v.s_prob_ge {
            let [p, path] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SProbGE row arity mismatch".into()));
            };
            self.q_lit(p, "SProbGE/p")?;
            let pe = self.elem(path)?;
            return self.walk_pathpred(pe);
        }
        let which = self.v.name_of(row.fun).to_string();
        Err(ctx_err(
            self.name,
            format!(
                "component former `{which}` — outside the implemented demo \
                 grammar (parity walk deferred for this former); refusing"
            ),
        ))
    }

    fn walk_statepred(&mut self, p: u32) -> Result<(), EvalError> {
        self.step()?;
        let row = self.sole(self.v.statepred_sort, p)?;
        if row.fun == self.v.s_true {
            return Ok(());
        }
        if row.fun == self.v.s_atom_le || row.fun == self.v.s_atom_ge {
            let [c, o] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SAtom row arity mismatch".into()));
            };
            self.q_lit(c, "SAtom/c")?;
            let oe = self.elem(o)?;
            let orow = self.sole(self.v.stateobs_sort, oe)?;
            if orow.fun == self.v.o_poly {
                // Parity is a formula-tree property; the polynomial
                // carries none, so the walk stops here.
                return Ok(());
            }
            let which = self.v.name_of(orow.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "observable former `{which}` — outside the implemented \
                     demo grammar (oPoly only); refusing"
                ),
            ));
        }
        if row.fun == self.v.s_and {
            let [list] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SAnd row arity mismatch".into()));
            };
            let le = self.elem(list)?;
            let members = self.walk_list(
                self.v.spl_sort,
                le,
                self.v.sl_nil,
                self.v.sl_cons,
                GUARD_MAX_VEC,
                "conjunction",
            )?;
            for m in members {
                let me = self.elem(&m)?;
                self.walk_statepred(me)?;
            }
            return Ok(());
        }
        let which = self.v.name_of(row.fun).to_string();
        Err(ctx_err(
            self.name,
            format!(
                "state-predicate former `{which}` — outside the implemented \
                 demo grammar (negation/disjunction parity walk deferred); \
                 refusing"
            ),
        ))
    }

    // --- the Θ₀ positive-membership walk (`qtsl_base_exact`) -----------

    /// Tri-state Θ₀ membership (module doc): `Ok(true)` = base-exact,
    /// `Ok(false)` = provably nonbase (what the refinement's own chase
    /// derives as `StatePred/nonbase`), `Err` = outside the decidable
    /// fragment — an open-sort observable beyond the four injections,
    /// an unknown extension constructor, undecodable structure.
    fn base_statepred(&mut self, p: u32, depth: usize) -> Result<bool, EvalError> {
        self.step()?;
        if depth > GUARD_MAX_DEPTH {
            return Err(ctx_err(
                self.name,
                format!(
                    "state-predicate tree deeper than the recursion budget \
                     ({GUARD_MAX_DEPTH}) — refusing"
                ),
            ));
        }
        let row = self.sole(self.v.statepred_sort, p)?;
        if row.fun == self.v.s_true || row.fun == self.v.s_false {
            return Ok(true); // the constants
        }
        if row.fun == self.v.s_not {
            return Ok(false); // ax/nonbase_not — decidedly nonbase
        }
        if row.fun == self.v.s_atom_le || row.fun == self.v.s_atom_ge {
            let [c, o] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SAtom row arity mismatch".into()));
            };
            self.q_lit(c, "SAtom/c")?;
            let oe = self.elem(o)?;
            let orow = self.sole(self.v.stateobs_sort, oe)?;
            if orow.fun == self.v.o_poly {
                // An ACTUAL polynomial image: the injection row itself
                // is the witness (base-ness is a grammar property; the
                // polynomial's own content carries none of it).
                let [_poly] = orow.args.as_slice() else {
                    return Err(ctx_err(self.name, "oPoly row arity mismatch".into()));
                };
                return Ok(true);
            }
            if Some(orow.fun) == self.v.o_chan
                || Some(orow.fun) == self.v.o_gate
                || Some(orow.fun) == self.v.o_ind
            {
                return Ok(false); // ax/nonbase_atom_* — decidedly nonbase
            }
            let which = self.v.name_of(orow.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "observable former `{which}` — outside the four injections: \
                     not provably nonbase yet not base either (Θ₀ is the \
                     polynomial stratum); refusing"
                ),
            ));
        }
        if row.fun == self.v.s_and || row.fun == self.v.s_or {
            let [list] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "SAnd/SOr row arity mismatch".into()));
            };
            let le = self.elem(list)?;
            let members = self.walk_list(
                self.v.spl_sort,
                le,
                self.v.sl_nil,
                self.v.sl_cons,
                GUARD_MAX_VEC,
                "junction",
            )?;
            // One decidedly-nonbase member decides the junction false
            // (`ax/has_nonbase_*` + `ax/nonbase_and`/`_or`) even when a
            // sibling refuses — scan whole, hold the first refusal.
            let mut deferred: Option<EvalError> = None;
            for m in members {
                let me = self.elem(&m)?;
                match self.base_statepred(me, depth + 1) {
                    Ok(true) => {}
                    Ok(false) => return Ok(false),
                    Err(e) => {
                        if deferred.is_none() {
                            deferred = Some(e);
                        }
                    }
                }
            }
            if let Some(e) = deferred {
                return Err(e);
            }
            return Ok(true);
        }
        let which = self.v.name_of(row.fun).to_string();
        Err(ctx_err(
            self.name,
            format!(
                "state-predicate former `{which}` — outside the Θ₀ grammar and \
                 not provably nonbase (unknown extension constructor); refusing"
            ),
        ))
    }

    fn walk_pathpred(&mut self, p: u32) -> Result<(), EvalError> {
        self.step()?;
        let row = self.sole(self.v.pathpred_sort, p)?;
        if row.fun == self.v.p_always {
            let [arg] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "PAlways row arity mismatch".into()));
            };
            let a = self.elem(arg)?;
            return self.walk_statepred(a);
        }
        let which = self.v.name_of(row.fun).to_string();
        Err(ctx_err(
            self.name,
            format!(
                "path former `{which}` — outside the implemented demo grammar \
                 (PAlways only; Streett meters and negated paths deferred); \
                 refusing"
            ),
        ))
    }
}

// ---------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------

/// `qtsl_init_member`. Args in wire field order: `region`, `sys`.
fn eval_init_member(
    name: &str,
    v: &GuardVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let region = d.elem(args[0])?;
    let sys = d.elem(args[1])?;
    let srow = d.sole(v.system_sort, sys)?;
    if srow.fun == v.sys_wire || Some(srow.fun) == v.sys_hole {
        let which = v.name_of(srow.fun).to_string();
        return Err(ctx_err(
            name,
            format!(
                "subject constructor `{which}` — the initial-membership \
                 discharge is realized for SysMech subjects only (composite \
                 and holed constructor pairs loudly deferred); refusing"
            ),
        ));
    }
    if srow.fun != v.sys_mech {
        return Err(ctx_err(
            name,
            format!(
                "element {sys} is constructed by a fun outside the expected \
                 System roster — malformed rows"
            ),
        ));
    }
    let [mech_cell] = srow.args.as_slice() else {
        return Err(ctx_err(name, "SysMech row arity mismatch".into()));
    };
    let mech = d.elem(mech_cell)?;

    let markings = d.distinct_rel_rows(v.mech_bag_marking, 1, mech, 3, "mech_bag_marking")?;
    let init_boxes = d.distinct_rel_rows(v.mech_init_box, 1, mech, 2, "mech_init_box")?;
    if !markings.is_empty() && !init_boxes.is_empty() {
        return Err(ctx_err(
            name,
            format!(
                "mechanism {mech} carries BOTH bag-marking and init-box \
                 content rows — the content-language exclusivity is violated, \
                 the initial data is ambiguous; refusing"
            ),
        ));
    }

    if !markings.is_empty() {
        // --- the bag-marking point leaf --------------------------------
        if markings.len() > GUARD_MAX_MARKINGS {
            return Err(ctx_err(
                name,
                format!("marking census beyond its budget ({GUARD_MAX_MARKINGS}) — refusing"),
            ));
        }
        let rbox = d.qra_box_intervals(region, "a bag-marking subject")?;
        let p = markings.len();
        if rbox.len() != p {
            return Err(ctx_err(
                name,
                format!(
                    "region box carries {} intervals against the marking \
                     block's width {p} — width discipline, never silent \
                     truncation; refusing",
                    rbox.len()
                ),
            ));
        }
        let wires = d.distinct_rel_rows(v.mech_bag_wire, 0, mech, 3, "mech_bag_wire")?;
        let mut m0: Vec<Option<u64>> = vec![None; p];
        for mrow in &markings {
            let token = &mrow.args[2];
            let count = d.nat_lit(&mrow.args[0], "mech_bag_marking/count")?;
            let matching: Vec<&&RelRow> = wires.iter().filter(|w| &w.args[1] == token).collect();
            let wrow = match matching.as_slice() {
                [] => {
                    return Err(ctx_err(
                        name,
                        format!(
                            "mechanism {mech}: a token species carries a marking \
                             row but no mech_bag_wire row — the count-block \
                             bijection is unwitnessed in view; refusing"
                        ),
                    ))
                }
                [w] => w,
                _ => {
                    return Err(ctx_err(
                        name,
                        format!(
                            "mechanism {mech}: a token species carries multiple \
                             distinct mech_bag_wire rows — the bijection is \
                             ambiguous; refusing"
                        ),
                    ))
                }
            };
            let wire = d.nat_lit(&wrow.args[2], "mech_bag_wire/wire")? as usize;
            if wire >= p {
                return Err(ctx_err(
                    name,
                    format!(
                        "mech_bag_wire cites wire {wire} against a marking \
                         block of width {p} — the dense-bijection clause is \
                         unwitnessed in view; refusing"
                    ),
                ));
            }
            if m0[wire].is_some() {
                return Err(ctx_err(
                    name,
                    format!(
                        "two token species share wire {wire} — the bijection \
                         is ambiguous; refusing"
                    ),
                ));
            }
            m0[wire] = Some(count);
        }
        let m0: Vec<QQ> = m0
            .into_iter()
            .map(|c| {
                let c = c.expect("dense by pigeonhole: p entries, all wires < p, no duplicates");
                QQ::new(BigInt::from(c), BigUint::from(1u64))
            })
            .collect();
        return Ok(check_marking_membership(&m0, &rbox).is_ok());
    }

    if !init_boxes.is_empty() {
        // --- the init-box leaf ------------------------------------------
        let rbox = d.qra_box_intervals(region, "an init-box subject")?;
        for (i, brow) in init_boxes.iter().enumerate() {
            let be = d.elem(&brow.args[0])?;
            let ibox = d.box_intervals(be)?;
            if ibox.len() != rbox.len() {
                return Err(ctx_err(
                    name,
                    format!(
                        "init box {i} carries {} intervals against the region \
                         box's {} — width discipline; refusing",
                        ibox.len(),
                        rbox.len()
                    ),
                ));
            }
            if check_box_containment(i, &rbox, &ibox).is_err() {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    Err(ctx_err(
        name,
        format!(
            "mechanism {mech} carries neither bag-marking nor init-box \
             content rows in view — the subject's initial data is outside \
             the realized constructor pairs (loudly deferred); refusing"
        ),
    ))
}

/// `qtsl_warrant_member`. Args in wire field order: `f`, `spec`.
/// Membership is hash-consed cell equality over the consumed
/// ForallSpec set — the component cell is never decoded.
fn eval_warrant_member(
    name: &str,
    v: &GuardVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    if !matches!(args[0], Value::Ref(_)) {
        return Err(EvalError::ArgDtype {
            name: name.into(),
            index: 0,
            expected: "element ref",
            found: 0xFF,
        });
    }
    let f_cell: &Value = args[0];
    let spec = d.elem(args[1])?;
    let mut stack = vec![spec];
    let mut visited: HashSet<u32> = HashSet::new();
    while let Some(s) = stack.pop() {
        if !visited.insert(s) {
            continue;
        }
        if visited.len() > GUARD_MAX_SPECS {
            return Err(ctx_err(
                name,
                format!("disjunction walk beyond its budget ({GUARD_MAX_SPECS}) — refusing"),
            ));
        }
        for row in d.distinct_rel_rows(v.spec_forall, 1, s, 2, "spec_forall")? {
            if &row.args[0] == f_cell {
                return Ok(true);
            }
        }
        for row in d.distinct_rel_rows(v.spec_or, 2, s, 3, "spec_or")? {
            let (l, r) = (d.elem(&row.args[0])?, d.elem(&row.args[1])?);
            stack.push(l);
            stack.push(r);
        }
    }
    Ok(false)
}

/// `qtsl_spec_wf`. Args in wire field order: `spec`.
fn eval_spec_wf(
    name: &str,
    v: &GuardVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let spec = d.elem(args[0])?;
    let forall_rows = d.distinct_rel_rows(v.spec_forall, 1, spec, 2, "spec_forall")?;
    let exists_rows = d.distinct_rel_rows(v.spec_exists, 1, spec, 2, "spec_exists")?;
    let score_rows = d.distinct_rel_rows(v.spec_score, 1, spec, 2, "spec_score")?;
    let or_rows = d.distinct_rel_rows(v.spec_or, 2, spec, 3, "spec_or")?;
    let name_rows = d.distinct_rel_rows(v.spec_name, 1, spec, 2, "spec_name")?;
    let iface_rows = d.distinct_rel_rows(v.spec_iface, 1, spec, 2, "spec_iface")?;
    let slack_rows = d.distinct_rel_rows(v.spec_slack, 1, spec, 2, "spec_slack")?;
    let guard_rows = d.distinct_rel_rows(v.spec_guard, 1, spec, 2, "spec_guard")?;

    // At-most-one name/iface/slack/guard/disjunction (C-SPEC /
    // C-SPEC-GUARD; spec_assume is zero-or-more by the theory's own
    // comment and deliberately uncounted).
    if name_rows.len() > 1
        || iface_rows.len() > 1
        || slack_rows.len() > 1
        || guard_rows.len() > 1
        || or_rows.len() > 1
    {
        return Ok(false);
    }
    // Component presence: the empty record claims nothing.
    let component_rows = forall_rows.len() + exists_rows.len() + score_rows.len();
    if component_rows == 0 && or_rows.is_empty() {
        return Ok(false);
    }
    // Disjunction exclusive with component rows.
    if !or_rows.is_empty() && component_rows > 0 {
        return Ok(false);
    }
    // Or-graph acyclicity (decided false — the list-cycle posture).
    if !or_rows.is_empty() && has_or_cycle(&mut d, v, spec)? {
        return Ok(false);
    }

    // Guard-vs-warrant agreement (PD-6 store-and-check): every
    // qsat_guard_warrant row whose sat's QSat/spec is this spec must
    // agree with the stored guard region.
    for prow in rows.producers(spec).iter().filter(|r| r.fun == v.qsat_spec) {
        let [sat_cell] = prow.args.as_slice() else {
            return Err(ctx_err(name, "QSat/spec row arity mismatch".into()));
        };
        let sat = d.elem(sat_cell)?;
        for gw in d.distinct_rel_rows(v.qsat_guard_warrant, 0, sat, 2, "qsat_guard_warrant")? {
            let warrant = d.elem(&gw.args[1])?;
            let wregion = d.sole_attr_required(warrant, v.qfs_region, "QForallSat/region")?;
            match guard_rows.as_slice() {
                // A stored guard row must exist (absent decides false —
                // the store-and-check's missing-store case).
                [] => return Ok(false),
                [g] => {
                    if g.args[0] != wregion {
                        // The derived second region on a one-region slot.
                        return Ok(false);
                    }
                }
                _ => unreachable!("counted above"),
            }
        }
    }

    // The residual negation-parity walk (safety face only).
    if !exists_rows.is_empty() || !score_rows.is_empty() {
        return Err(ctx_err(
            name,
            "liveness-mark or attitude components in view — the parity walk \
             is implemented for the safety face only (deferred, named); \
             refusing"
                .into(),
        ));
    }
    for row in &forall_rows {
        let f = d.elem(&row.args[0])?;
        d.walk_forall(f)?;
    }
    Ok(true)
}

/// Or-graph cycle detection from `root` (iterative gray/black DFS over
/// `spec_or` arms; budgeted).
fn has_or_cycle(d: &mut Decoder<'_>, v: &GuardVocab, root: u32) -> Result<bool, EvalError> {
    enum Frame {
        Enter(u32),
        Exit(u32),
    }
    let mut gray: HashSet<u32> = HashSet::new();
    let mut done: HashSet<u32> = HashSet::new();
    let mut stack = vec![Frame::Enter(root)];
    let mut seen = 0usize;
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Enter(s) => {
                if done.contains(&s) {
                    continue;
                }
                if gray.contains(&s) {
                    return Ok(true);
                }
                seen += 1;
                if seen > GUARD_MAX_SPECS {
                    return Err(ctx_err(
                        d.name,
                        format!("or-graph walk beyond its budget ({GUARD_MAX_SPECS}) — refusing"),
                    ));
                }
                gray.insert(s);
                stack.push(Frame::Exit(s));
                for row in d.distinct_rel_rows(v.spec_or, 2, s, 3, "spec_or")? {
                    let (l, r) = (d.elem(&row.args[0])?, d.elem(&row.args[1])?);
                    stack.push(Frame::Enter(l));
                    stack.push(Frame::Enter(r));
                }
            }
            Frame::Exit(s) => {
                gray.remove(&s);
                done.insert(s);
            }
        }
    }
    Ok(false)
}

/// `qtsl_cert_claim_wf`. Args in wire field order: `sat`.
fn eval_cert_claim_wf(
    name: &str,
    v: &GuardVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let sat = d.elem(args[0])?;
    let warrants = d.distinct_rel_rows(v.qsat_warrant, 0, sat, 2, "qsat_warrant")?;
    let guards = d.distinct_rel_rows(v.qsat_guard_warrant, 0, sat, 2, "qsat_guard_warrant")?;
    let evals = d.distinct_rel_rows(v.qsat_eval, 1, sat, 2, "qsat_eval")?;
    // At-most-one per family; never both warrant routes.
    if warrants.len() > 1 || guards.len() > 1 || evals.len() > 1 {
        return Ok(false);
    }
    if !warrants.is_empty() && !guards.is_empty() {
        return Ok(false);
    }

    // The hole ledger, zero-hole case only.
    let spec_val = d.sole_attr_required(sat, v.qsat_spec, "QSat/spec")?;
    let sys_val = d.sole_attr_required(sat, v.qsat_sys, "QSat/sys")?;
    let spec = d.elem(&spec_val)?;
    let sys = d.elem(&sys_val)?;

    // Regret census over the consumed components (through disjunction),
    // only where the closure declares the regret vocabulary at all.
    if v.s_regret_le.is_some() || v.s_regret_le_mark.is_some() {
        let mut stack = vec![spec];
        let mut visited: HashSet<u32> = HashSet::new();
        while let Some(s) = stack.pop() {
            if !visited.insert(s) {
                continue;
            }
            if visited.len() > GUARD_MAX_SPECS {
                return Err(ctx_err(
                    name,
                    format!("disjunction walk beyond its budget ({GUARD_MAX_SPECS}) — refusing"),
                ));
            }
            if let Some(srl) = v.s_regret_le {
                for row in d.distinct_rel_rows(v.spec_forall, 1, s, 2, "spec_forall")? {
                    let f = d.elem(&row.args[0])?;
                    let producers = rows.producers(f);
                    if producers.iter().any(|r| r.fun == srl) {
                        return Err(ctx_err(
                            name,
                            "regret component (SRegretLE) among the consumed \
                             components — the holed shapes are outside this \
                             leg; refusing"
                                .into(),
                        ));
                    }
                    if producers.is_empty() {
                        return Err(ctx_err(
                            name,
                            format!(
                                "component element {f} is unconstructed in view — \
                                 the hole ledger cannot adjudicate its regret \
                                 face; refusing"
                            ),
                        ));
                    }
                }
            }
            if let Some(srlm) = v.s_regret_le_mark {
                for row in d.distinct_rel_rows(v.spec_exists, 1, s, 2, "spec_exists")? {
                    let e = d.elem(&row.args[0])?;
                    let producers = rows.producers(e);
                    if producers.iter().any(|r| r.fun == srlm) {
                        return Err(ctx_err(
                            name,
                            "regret mark (SRegretLEMark) among the consumed \
                             components — the holed shapes are outside this \
                             leg; refusing"
                                .into(),
                        ));
                    }
                    if producers.is_empty() {
                        return Err(ctx_err(
                            name,
                            format!(
                                "liveness-mark element {e} is unconstructed in \
                                 view — the hole ledger cannot adjudicate its \
                                 regret face; refusing"
                            ),
                        ));
                    }
                }
            }
            for row in d.distinct_rel_rows(v.spec_or, 2, s, 3, "spec_or")? {
                let (l, r) = (d.elem(&row.args[0])?, d.elem(&row.args[1])?);
                stack.push(l);
                stack.push(r);
            }
        }
    }

    // The subject's hole count (zero-hole demand).
    let holes = d.hole_count(sys)?;
    if holes > 0 {
        return Err(ctx_err(
            name,
            format!(
                "subject carries {holes} hole(s) (SysHole) — the holed \
                 shapes are outside this leg (exactly-one-hole ledger \
                 deferred); refusing"
            ),
        ));
    }
    Ok(true)
}

/// `qtsl_base_exact`. Args in wire field order: `f`.
fn eval_base_exact(
    name: &str,
    v: &GuardVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let f = d.elem(args[0])?;
    d.base_statepred(f, 0)
}

/// Family dispatch (provider.rs routes here).
pub(crate) fn eval_guard(
    name: &str,
    v: &GuardVocab,
    kind: GuardKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        GuardKind::InitMember => eval_init_member(name, v, args, rows),
        GuardKind::WarrantMember => eval_warrant_member(name, v, args, rows),
        GuardKind::SpecWf => eval_spec_wf(name, v, args, rows),
        GuardKind::CertClaimWf => eval_cert_claim_wf(name, v, args, rows),
        GuardKind::BaseExact => eval_base_exact(name, v, args, rows),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn marking_membership() {
        let m0 = [q(1, 1), q(0, 1)];
        // The degenerate box at m0.
        assert!(check_marking_membership(&m0, &[(q(1, 1), q(1, 1)), (q(0, 1), q(0, 1))]).is_ok());
        // A fat box around it.
        assert!(check_marking_membership(&m0, &[(q(0, 1), q(2, 1)), (q(-1, 2), q(1, 2))]).is_ok());
        // The GInitOutside mutant: +1 on wire 0, both ends.
        assert_eq!(
            check_marking_membership(&m0, &[(q(2, 1), q(2, 1)), (q(0, 1), q(0, 1))]),
            Err(GuardViolation::InitCoordinateOutside { wire: 0 })
        );
        // Upper violation on wire 1.
        assert_eq!(
            check_marking_membership(
                &[q(1, 1), q(3, 1)],
                &[(q(1, 1), q(1, 1)), (q(0, 1), q(2, 1))]
            ),
            Err(GuardViolation::InitCoordinateOutside { wire: 1 })
        );
        // Exact rational boundaries are inclusive (closed intervals).
        assert!(check_marking_membership(&[q(1, 2)], &[(q(1, 2), q(1, 2))]).is_ok());
    }

    #[test]
    fn box_containment() {
        let region = [(q(0, 1), q(2, 1)), (q(0, 1), q(2, 1))];
        assert!(
            check_box_containment(0, &region, &[(q(0, 1), q(1, 1)), (q(1, 1), q(2, 1))]).is_ok()
        );
        // Equality is containment.
        assert!(check_box_containment(0, &region, &region.clone()).is_ok());
        // Overhang on the hi end, axis 1.
        assert_eq!(
            check_box_containment(2, &region, &[(q(0, 1), q(1, 1)), (q(0, 1), q(3, 1))]),
            Err(GuardViolation::InitBoxNotContained {
                box_index: 2,
                axis: 1
            })
        );
        // Underhang on the lo end, axis 0.
        assert_eq!(
            check_box_containment(0, &region, &[(q(-1, 1), q(1, 1)), (q(0, 1), q(1, 1))]),
            Err(GuardViolation::InitBoxNotContained {
                box_index: 0,
                axis: 0
            })
        );
    }
}
