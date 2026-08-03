//! The angelic-selection family: the positional-selection witness's
//! seven side-conditions (`qtsl_asel_reach` / `_cover` / `_enabled` /
//! `_closed` / `_ratecap` / `_relay` / `_attach`), as row-context
//! recomputes, fail-closed.
//!
//! Semantic authority: the Qtsl theory's angelic-liveness block
//! ("Angelic liveness: the positional-selection witness" —
//! `ASelKind`/`ASelWitness`/`ASelCell`, `asel_exit`, `asel_warrant`,
//! the seven side-condition declarations and their chase demands
//! `ax/wf/asel_*`), the TrClock four-wing former (`tkRace {majorant}`
//! / `tkDemonic {dwellMin}` / `tkForced {dwell}` / `tkCarved {floor,
//! ceil}` — the carved-window wing is revision event 5, whose
//! finite-ceil rows this family consumes as the free non-Zeno timing
//! leg the theory's window comment names), the
//! manifest stratum (`mech_manifest`, `Manifest/modes`, `Mode/domain`),
//! the Transition content stratum where it is syntactic (`tr_scale`
//! scale views, `mkKernelCite`'s image box, `Transition/grain` — the
//! optional content group below), and the compiled verdict form
//! (event-6 face-typed: `qvfMk
//! {exists_face: QExistsEntryList, forall_face: QForallSatList}`,
//! `qsat_verdict`, with `qsat_zeno_budget` for the both-slots
//! refusal).
//!
//! # Per-relation contracts (tri-state, the crate's verdict discipline)
//!
//! - **`qtsl_asel_reach {wit}`** — identity + agreement only ("this
//!   family only ties identity and agreement, never re-proves reach"):
//!   the witness's `sys`/`eps`/`reach` attributes decode, the reach
//!   warrant carries its region attribute, and every claim consuming
//!   the reach warrant (a `qsat_warrant` or `qsat_guard_warrant` row
//!   citing it in the warrant slot) has `QSat/sys` cell-equal to the
//!   witness's system — disagreement decides false; ZERO consuming
//!   claims in view refuse (`QRegionSat` carries no subject attribute,
//!   so the subject tie is undecidable without a consumer).
//! - **`qtsl_asel_cover {wit}`** — fully decidable box coverage, per
//!   mode: over `qraBox` reach regions and `SysMech` subjects only
//!   (everything else refuses, named), for every mode of the subject's
//!   manifest, (region ∩ `Mode/domain`) ⊆ ∪ {`ASelCell/dom` of the
//!   witness's cells on that mode} — decided by exact-ℚ slab
//!   decomposition ([`check_box_cover`]): clip covers to the target,
//!   cut every axis at every endpoint, and test one midpoint per
//!   elementary cell (membership is constant on open cells and the
//!   covers are closed, so all-midpoints-covered decides coverage
//!   exactly). An empty mode intersection is vacuously covered; an
//!   `mlNil` manifest is vacuously true; width mismatches and inverted
//!   intervals refuse; the elementary-cell count is budgeted.
//! - **`qtsl_asel_enabled {cell}`** — ATTACHMENT before enabledness
//!   (the theory's ordering: "an unattached transition can be fired by
//!   no resolution of the witnessed System, so no active-region test
//!   may precede this check"): no `sys_transition` row for the choice
//!   decides FALSE; the cell's mode outside the subject's manifest
//!   decides FALSE. Then the dom-in-active-region facet, realized for
//!   the syntactic fragment (the active region is DERIVED — the
//!   Transition former's own comment: "there is no guard field. The
//!   active region is the kernel's non-stay support"): (c1) the GRAIN
//!   gate — `grWhole` passes; `grVariant {ix}` demands the cell's mode
//!   sit at position ix of the manifest's ordered mode list (position
//!   IS the variant index), mismatch decides FALSE; `grTuple`/`grPath`
//!   refuse (marked-population strata — box geometry inapplicable);
//!   (c2) the SUPPORT facet — a `tr_scale` choice's support is
//!   `{rate > 0}` gated on the mixture carrying non-stay mass
//!   (constant weights): an all-stay mixture decides FALSE, and strict
//!   positivity of the rate polynomial over dom runs on the exact-ℚ
//!   Bernstein scan ([`crate::bernbox::box_sign_strict`]) — certified
//!   decides TRUE, an in-dom nonpositive witness point decides FALSE,
//!   Bernstein-inconclusive refuses; a `tr_kernel` choice's support
//!   rides the cited hypernet's opaque digest — REFUSES, named (the
//!   certificate-stratum support warrant is the staged growth).
//!   Closures without the content vocabulary keep the R3/R4 refusal.
//! - **`qtsl_asel_closed {cell}`** — structural decode (wit, choice,
//!   dom, and the warrant region as `qraBox`), then the
//!   landing-enclosure facet over the same content decode: the
//!   enclosure is the DECLARED box (the former's out-wire — a
//!   `tr_kernel` choice's `mkKernelCite/image`, a `tr_scale` choice's
//!   `srNext` images), and every enclosure box inside the warrant
//!   region decides TRUE / a protruding one decides FALSE (the row
//!   obligation's subject is the enclosure, not the exact reachable
//!   image); a cemetery branch refuses (the death outcome's
//!   admissibility is not exposed at this stratum); an all-stay
//!   mixture is vacuously closed.
//! - **`qtsl_asel_ratecap {cell}`** — dwell cells only (other kinds
//!   decide false): eps ≤ 0 decides false; the exit roster (dedup by
//!   transition element) must attach to the witness's system (an
//!   unattached member decides false) and must contain every attached
//!   transition (a sub-roster refuses: activity-on-dom is not
//!   relationally exposed, so roster ⊇ attached is the decidable
//!   sufficient condition for completeness); per member, `tkRace
//!   {enFin q}` adds q to the majorant sum (a nonpositive q refuses —
//!   malformed under the positivity report), `tkRace {enInf}` refuses
//!   (an instant row's activity on dom is undecidable here),
//!   `tkDemonic`/`tkForced` contribute 0 with their floors recomputed
//!   strictly positive (≤ 0 decides false; an infinite dwellMin is the
//!   demonic dead point, refused); `tkCarved` joins the floor-capped
//!   class (event 5 — the consumption sentence's ratecap face):
//!   floor ≤ 0 decides false (a chattering window floor, the demonic
//!   posture), an inverted finite window refuses (a row that can never
//!   fire — the dead-point posture, `ax/wf/tr_carved_window_ordered`
//!   named), a lawful window contributes 0 (a `tr_dwell_gate` row is
//!   harmless here: the gate refines the window, never widens it, so
//!   the strict floor still caps the wing); verdict: sum · eps ≤ 1,
//!   exact ℚ.
//! - **`qtsl_asel_relay {cell}`** — relay cells only (other kinds
//!   decide false), decidable-false facets first: an unattached choice
//!   decides false; a `tkRace {enFin}` choice decides false (a racing
//!   row is not zero-discretionary-delay); demonic/forced floors ≤ 0
//!   decide false (infinite dwellMin refuses — dead point); a carved
//!   choice is relay-eligible exactly as a demonic one (theory's
//!   words; its finite ceil additionally bounds the hop's dwell —
//!   the window wing's free non-Zeno timing leg): floor ≤ 0 decides
//!   false, an inverted finite window refuses (dead point), and a
//!   `tr_dwell_gate` row on the CHOICE refuses (the gate's sign-fiber
//!   rides an opaque hypernet cite — earliest-permitted-time
//!   fireability is undecidable in view); any OTHER
//!   attached `tkRace {enInf}` row refuses (only-instant-on-dom is
//!   undecidable without the active-region stratum); then the
//!   landing-in-dwell-union facet over the content decode: enclosure
//!   boxes (as in `closed`) covered by the union of the witness's
//!   dwell cells' doms ([`check_box_cover`] reused) decides TRUE /
//!   uncovered decides FALSE — realized for single-mode manifests
//!   (multi-mode landing resolution rides the endo/grain stratum,
//!   refused named).
//! - **`qtsl_asel_attach {mark, wit}`** — decidable where the
//!   compiled-form group resolves and the rows in view are
//!   unambiguous (absence, producer ambiguity, and unresolved
//!   positions all refuse), per the theory's event-6 attach comment:
//!   (a) a second distinct witness
//!   warranted for the mark decides false (at-most-one per mark,
//!   C-CERT-CLAIM kin; keying is BY ENTITY); (b) the mark must sit in
//!   an exists_face list of its claims' compiled forms — membership
//!   through the REGION BRIDGE: a `qxeMk {e, region}` entry citing
//!   the mark's own `QRegionSat/region` ELEMENT (citation identity —
//!   producers emit the mark and its entry against the same region
//!   element; formula/component correspondence stays with
//!   `qtsl_verdict_compile` and the grounded walk), found by the
//!   budgeted upward walk from the bridge entries' `qxeCons` cells to
//!   `qvfMk` exists_face slots, complete for single-body context; no
//!   placement refuses ("not compiled or not consumed in view"); a
//!   mark in a forall_face list is structurally unrepresentable
//!   (members are QForallSat entities); (c) every claim whose
//!   compiled form's exists_face list carries the mark must have
//!   `QSat/sys` cell-equal to the witness's system (shared marks
//!   demand one agreed witness System); zero consuming claims refuse;
//!   (d) the both-slots refusal, GLOBAL BY ENTITY (the budget
//!   family's polarity comment: "one entity warranted as a mark
//!   anywhere and budget-indexed on the forall face anywhere is
//!   refused"): EVERY `qsat_zeno_budget` row in view is swept —
//!   rows on non-consuming claims included, riding the row
//!   context's whole-context enumeration surface rather than any
//!   element-keyed view. Per row: the priced claim's sole compiled
//!   form (C-CERT-CLAIM kin — a second `qsat_verdict` attachment
//!   refuses), the form's sole `qvfMk` row (P-FUN kin), and the
//!   row's position down that form's forall_face spine; an indexed
//!   entry carrying the mark's region cell decides FALSE (warranted
//!   on the angelic face AND envelope-priced on the forall face). A
//!   row the walk cannot resolve in view — an external claim ref,
//!   no compiled form, no qvfMk producer, an unresolvable position
//!   — refuses: the walk cannot rule the mark out.
//!
//! Vocabulary resolution: the angelic vocabulary is REQUIRED — the
//! family self-unclaims (declared-but-unbound, safe-fail) where the
//! closure lacks it. (`tkCarved` is part of the required clock kit:
//! it minted at revision event 5 and this family's own required
//! vocabulary is event-6-shaped, so no closure the family serves can
//! lack it.) The compiled-form group (`QVerdictForm`, the
//! face-typed `qvfMk`, `qxeMk`/`qxeCons`/`qfsCons`,
//! `QForallSat/region`, `qsat_verdict`, `qsat_zeno_budget`) is
//! OPTIONAL: `attach` refuses where it is absent; the other six
//! relations never consult it. The CONTENT group (`tr_kernel` /
//! `tr_scale` / `tr_dwell_gate`, `mkScaleView` + the branch kit,
//! `mkKernelCite`, `Transition/grain` + the grain kit, the Poly
//! decoder) is likewise OPTIONAL: `enabled`'s support facet and
//! `closed`/`relay`'s landing facets refuse where it is absent; the
//! other relations never consult it (except `relay`'s carved-choice
//! gate check, which consults `tr_dwell_gate` alone and skips where
//! that relation is undeclared — a gate row of an undeclared relation
//! is invisible to every evaluator, the standing single-body posture). (Note the REQUIRED vocabulary is
//! itself event-6-shaped — `QForallSat` and the 2-field warrant
//! relations — so a genuinely pre-event-6 closure un-claims the
//! whole family before attach's refusal is reachable; the
//! attach-specific refusal arises on closures carrying the required
//! angelic vocabulary without the compiled group.) The resolvers
//! are the shadowing-tolerant sweep ([`crate::guard`] module doc):
//! names select, shapes co-select, identities pin.
//!
//! Event-6 note (the verdict-stratum re-cut): the warrant relations
//! are the 2-field entity shape (`{sat, warrant: QForallSat}`), so on
//! event-6 closures a `qsat_warrant` row can no longer cite a
//! QRegionSat reach warrant — `reach`'s consuming-claims walk then
//! finds nothing and refuses (subject tie undecidable), the standing
//! fail-closed posture, until producers emit QForallSat consumers.
//! (History: the group was left e5-keyed fail-closed at the e6 mint;
//! a later revision moved the resolver
//! and the walk together, as the mint's resolver note directed. The
//! retired {floors, marks} walk and its A-1 both-slots reading live
//! in git history.)

use crate::bernbox::{box_sign_strict, StrictBoxSign};
use crate::error::EvalError;
use crate::polycanon::{build_polycanon_vocab, decode_stored_poly, PolyCanonVocab, StoredPoly};
use crate::qpoly::{Mono, QPoly};
use crate::qq::QQ;
use crate::roster::{ASelKind, EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, FieldPred, Ground, OwnedFieldPred, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// The angelic-selection family's rows of the claimed roster
/// (concatenated at registration — provider.rs). Field names and
/// bytewise order are part of the claim.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_asel_reach",
        &[("wit", "ASelWitness")],
        RelKind::ASel(ASelKind::Reach),
    ),
    (
        "qtsl_asel_cover",
        &[("wit", "ASelWitness")],
        RelKind::ASel(ASelKind::Cover),
    ),
    (
        "qtsl_asel_enabled",
        &[("cell", "ASelCell")],
        RelKind::ASel(ASelKind::Enabled),
    ),
    (
        "qtsl_asel_closed",
        &[("cell", "ASelCell")],
        RelKind::ASel(ASelKind::Closed),
    ),
    (
        "qtsl_asel_ratecap",
        &[("cell", "ASelCell")],
        RelKind::ASel(ASelKind::Ratecap),
    ),
    (
        "qtsl_asel_relay",
        &[("cell", "ASelCell")],
        RelKind::ASel(ASelKind::Relay),
    ),
    (
        "qtsl_asel_attach",
        &[("mark", "QRegionSat"), ("wit", "ASelWitness")],
        RelKind::ASel(ASelKind::Attach),
    ),
];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const ASEL_MAX_VEC: usize = 1 << 12;
/// Elementary-cell budget for the cover slab decomposition.
pub const ASEL_MAX_CELLS: usize = 1 << 16;
/// Upward-walk budget (attach's list-spine climb).
pub const ASEL_MAX_WALK: usize = 1 << 12;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The optional compiled-form group (`attach` refuses where absent) —
/// the event-6 face-typed verdict form: `qvfMk {exists_face:
/// QExistsEntryList, forall_face: QForallSatList}`, the exists-entry
/// bridge (`qxeMk {e, region}` — the mark-entity bridge is the REGION
/// CELL: producer emits the mark and its exists entry citing the same
/// region element), the two list spines, the verdict relation, and
/// the zeno-budget pricing row for the both-slots refusal.
#[derive(Debug, Clone)]
pub struct CompiledFormVocab {
    qvf_mk: Chid,
    qxe_mk: Chid,
    qxe_cons: Chid,
    qfs_cons: Chid,
    qfs_region: Chid,
    qsat_verdict: Chid,
    qsat_zeno_budget: Chid,
}

/// The optional content-staging group — the syntactic slice of the
/// Transition content stratum that `enabled`'s support facet,
/// `closed`'s landing facet, and `relay`'s landing-in-dwell-union
/// facet read: the two content presentations, the scale view's tagged
/// mixture, the kernel citation's declared image box, the grain kit,
/// and the stored-Poly decoder for rate observables.
#[derive(Debug, Clone)]
pub struct ContentVocab {
    // relations
    tr_kernel: Chid,
    tr_scale: Chid,
    // constructors
    mk_scale_view: Chid,
    sb_nil: Chid,
    sb_cons: Chid,
    sr_next: Chid,
    sr_stay: Chid,
    sr_cemetery: Chid,
    mk_kernel_cite: Chid,
    /// `hnDigest {sha256hex}` — message nicety only (a kernel-cite
    /// refusal that names its digest is a better instrument).
    hn_digest: Option<Chid>,
    gr_whole: Chid,
    gr_variant: Chid,
    gr_tuple: Chid,
    gr_path: Chid,
    // exactly-one attributes
    tr_grain: Chid,
    // sorts the structural walks key on
    scaleview_sort: Chid,
    branchlist_sort: Chid,
    stepres_sort: Chid,
    kernelcite_sort: Chid,
    trgrain_sort: Chid,
    hypref_sort: Chid,
    /// The stored-Poly decoder ([`crate::polycanon`]) over the swept
    /// `Poly` sort.
    poly: PolyCanonVocab,
}

/// The angelic-selection vocabulary, pinned at resolution.
#[derive(Debug, Clone)]
pub struct AselVocab {
    // constructors
    ask_dwell: Chid,
    ask_relay: Chid,
    sys_mech: Chid,
    sys_wire: Chid,
    sys_hole: Option<Chid>,
    ml_nil: Chid,
    ml_cons: Chid,
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    qra_box: Chid,
    qra_sublevel: Chid,
    qra_affine: Chid,
    tk_race: Chid,
    tk_demonic: Chid,
    tk_forced: Chid,
    tk_carved: Chid,
    en_fin: Chid,
    en_inf: Chid,
    // exactly-one attributes
    wit_sys: Chid,
    wit_eps: Chid,
    wit_reach: Chid,
    cell_wit: Chid,
    cell_dom: Chid,
    cell_mode: Chid,
    cell_kind: Chid,
    cell_choice: Chid,
    mode_domain: Chid,
    manifest_modes: Chid,
    tr_clock: Chid,
    qsat_sys: Chid,
    qrs_region: Chid,
    // relations
    asel_exit: Chid,
    asel_warrant: Chid,
    sys_transition: Chid,
    mech_manifest: Chid,
    qsat_warrant: Chid,
    qsat_guard_warrant: Chid,
    /// The carved-window gate refinement (`tr_dwell_gate {gate, tr}`)
    /// — resolved independently of the content group: `relay`'s
    /// carved-choice gate check consults it alone, and skips where
    /// the relation is undeclared (rows of an undeclared relation are
    /// invisible in view — the standing single-body posture).
    tr_dwell_gate: Option<Chid>,
    // sorts the structural walks key on
    aselkind_sort: Chid,
    system_sort: Chid,
    modelist_sort: Chid,
    trclock_sort: Chid,
    ennrat_sort: Chid,
    region_sort: Chid,
    box_sort: Chid,
    interval_sort: Chid,
    /// The optional compiled-form group.
    compiled: Option<CompiledFormVocab>,
    /// The optional content-staging group.
    content: Option<ContentVocab>,
    /// Per-sort constructor rosters (sort chid → fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
    /// Declared names, for refusal messages.
    names: HashMap<Chid, String>,
}

impl AselVocab {
    fn name_of(&self, c: Chid) -> &str {
        self.names
            .get(&c)
            .map(String::as_str)
            .unwrap_or("<undeclared fun>")
    }

    /// Whether the OPTIONAL compiled-form group resolved (`attach`
    /// refuses where it did not; the other six relations never
    /// consult it). Exposed so closure-level gates can assert the
    /// event-6 vocabulary actually bound — family claiming alone
    /// does not imply it, because every member failure is erased to
    /// `None` at resolution.
    pub fn compiled_resolved(&self) -> bool {
        self.compiled.is_some()
    }

    /// Whether the OPTIONAL content-staging group resolved (the
    /// enabled/closed/relay landing facets refuse where it did not).
    pub fn content_resolved(&self) -> bool {
        self.content.is_some()
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

/// The shadowing-tolerant constructor find ([`crate::guard`] module
/// doc): sweep every index, keep only declarations whose codomain AND
/// domain shape match, refuse zero matches and ambiguity.
fn find_ctor(
    indices: &[&TheoryIndex],
    name: &str,
    want_cod: Chid,
    check: &dyn Fn(&DomainSig) -> bool,
) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        let Some(d) = index.fun(name) else { continue };
        if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) || !check(&d.domain) {
            continue; // a same-name declaration of another generation
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
        format!("no `{name}` constructor with the expected angelic-revision shape among the swept revisions")
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
        format!("no `{name}` relation with the expected angelic-revision shape among the swept revisions")
    })
}

/// The shadowing-tolerant attribute find: unary on `subject`, codomain
/// the element sort `want_cod`.
fn find_attr(
    indices: &[&TheoryIndex],
    name: &str,
    subject: Chid,
    want_cod: Chid,
) -> Result<Chid, String> {
    find_attr_by(indices, name, subject, &SortKey::Elem(want_cod))
}

/// The ground-codomain twin (`ASelWitness/eps : ASelWitness -> Q`).
fn find_attr_ground(
    indices: &[&TheoryIndex],
    name: &str,
    subject: Chid,
    want: Ground,
) -> Result<Chid, String> {
    find_attr_by(indices, name, subject, &SortKey::Ground(want))
}

fn find_attr_by(
    indices: &[&TheoryIndex],
    name: &str,
    subject: Chid,
    want_cod: &SortKey,
) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        let Some(d) = index.fun(name) else { continue };
        if d.relational
            || d.domain != DomainSig::Unary(SortKey::Elem(subject))
            || d.codomain.as_ref() != Some(want_cod)
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
        format!("no `{name}` attribute with the expected angelic-revision shape among the swept revisions")
    })
}

/// Build the angelic-selection vocabulary over the declared indices.
/// `Err` → the family is not claimed (declared-but-unbound, safe-fail;
/// reason on the provider's vocabulary notes).
pub fn build_asel_vocab(indices: &[&TheoryIndex]) -> Result<AselVocab, String> {
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    fn is_elem_eq(want: Chid) -> impl Fn(&SortKey) -> bool {
        move |s: &SortKey| *s == SortKey::Elem(want)
    }
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
    let bn = || -> Box<dyn Fn(&SortKey) -> bool> {
        Box::new(|s: &SortKey| *s == SortKey::Ground(Ground::Nat))
    };
    let bsh = || -> Box<dyn Fn(&SortKey) -> bool> {
        Box::new(|s: &SortKey| *s == SortKey::Ground(Ground::Shape))
    };
    let bstr = || -> Box<dyn Fn(&SortKey) -> bool> {
        Box::new(|s: &SortKey| *s == SortKey::Ground(Ground::Str))
    };
    let be = |want: Chid| -> Box<dyn Fn(&SortKey) -> bool> { Box::new(is_elem_eq(want)) };
    let nullary = |s: &DomainSig| *s == DomainSig::Nullary;
    let unary_of = |want: Chid| move |s: &DomainSig| *s == DomainSig::Unary(SortKey::Elem(want));

    // --- anchor sorts (the REQUIRED angelic vocabulary) ---------------
    let aselkind_sort = sort_by_name(indices, "ASelKind")?;
    let aselwit_sort = sort_by_name(indices, "ASelWitness")?;
    let aselcell_sort = sort_by_name(indices, "ASelCell")?;
    let system_sort = sort_by_name(indices, "System")?;
    let mech_sort = sort_by_name(indices, "Mech")?;
    let manifest_sort = sort_by_name(indices, "Manifest")?;
    let mode_sort = sort_by_name(indices, "Mode")?;
    let modelist_sort = sort_by_name(indices, "ModeList")?;
    let transition_sort = sort_by_name(indices, "Transition")?;
    let trclock_sort = sort_by_name(indices, "TrClock")?;
    let ennrat_sort = sort_by_name(indices, "EnnRat")?;
    let box_sort = sort_by_name(indices, "Box")?;
    let interval_sort = sort_by_name(indices, "Interval")?;
    let qrs_sort = sort_by_name(indices, "QRegionSat")?;
    let qfs_sort = sort_by_name(indices, "QForallSat")?;
    let region_sort = sort_by_name(indices, "QRegionAtom")?;
    let qsat_sort = sort_by_name(indices, "QSat")?;
    let forall_sort = sort_by_name(indices, "ForallSpec")?;
    let _ = forall_sort; // anchor demanded, no longer a warrant field (event 6)

    // --- constructors ---------------------------------------------------
    let ask_dwell = find_ctor(indices, "askDwell", aselkind_sort, &nullary)?;
    let ask_relay = find_ctor(indices, "askRelay", aselkind_sort, &nullary)?;
    let sys_mech = find_ctor(
        indices,
        "SysMech",
        system_sort,
        &record_of(vec![("mech", be(mech_sort))]),
    )?;
    let sys_wire = find_ctor(
        indices,
        "SysWire",
        system_sort,
        &record_of(vec![("inner", bx(is_elem)), ("wiring", bx(is_elem))]),
    )?;
    let sys_hole = find_ctor(
        indices,
        "SysHole",
        system_sort,
        &record_of(vec![("iface", bx(is_elem))]),
    )
    .ok();
    let ml_nil = find_ctor(indices, "mlNil", modelist_sort, &nullary)?;
    let ml_cons = find_ctor(
        indices,
        "mlCons",
        modelist_sort,
        &record_of(vec![("head", be(mode_sort)), ("tail", be(modelist_sort))]),
    )?;
    let box_nil = find_ctor(indices, "boxNil", box_sort, &nullary)?;
    let box_cons = find_ctor(
        indices,
        "boxCons",
        box_sort,
        &record_of(vec![("head", be(interval_sort)), ("tail", be(box_sort))]),
    )?;
    let mk_interval = find_ctor(
        indices,
        "mkInterval",
        interval_sort,
        &record_of(vec![("hi", bq()), ("lo", bq())]),
    )?;
    let qra_box = find_ctor(indices, "qraBox", region_sort, &unary_of(box_sort))?;
    let qra_sublevel = find_ctor(
        indices,
        "qraSublevel",
        region_sort,
        &record_of(vec![("cert", bx(is_elem)), ("thr", bq())]),
    )?;
    let qra_affine = find_ctor(
        indices,
        "qraAffine",
        region_sort,
        &record_of(vec![("row", bx(is_elem)), ("thr", bq())]),
    )?;
    let tk_race = find_ctor(
        indices,
        "tkRace",
        trclock_sort,
        &record_of(vec![("majorant", be(ennrat_sort))]),
    )?;
    let tk_demonic = find_ctor(
        indices,
        "tkDemonic",
        trclock_sort,
        &record_of(vec![("dwellMin", be(ennrat_sort))]),
    )?;
    let tk_forced = find_ctor(
        indices,
        "tkForced",
        trclock_sort,
        &record_of(vec![("dwell", bq())]),
    )?;
    // The carved-window wing (revision event 5). Bytewise field order
    // is (ceil, floor) — the order-pinned shape check makes the
    // positional decode downstream safe by construction (the donor
    // pattern, trwf).
    let tk_carved = find_ctor(
        indices,
        "tkCarved",
        trclock_sort,
        &record_of(vec![("ceil", be(ennrat_sort)), ("floor", bq())]),
    )?;
    let en_fin = find_ctor(indices, "enFin", ennrat_sort, &record_of(vec![("q", bq())]))?;
    let en_inf = find_ctor(indices, "enInf", ennrat_sort, &nullary)?;

    // --- exactly-one attributes ------------------------------------------
    let wit_sys = find_attr(indices, "ASelWitness/sys", aselwit_sort, system_sort)?;
    let wit_eps = find_attr_ground(indices, "ASelWitness/eps", aselwit_sort, Ground::Q)?;
    let wit_reach = find_attr(indices, "ASelWitness/reach", aselwit_sort, qrs_sort)?;
    let cell_wit = find_attr(indices, "ASelCell/wit", aselcell_sort, aselwit_sort)?;
    let cell_dom = find_attr(indices, "ASelCell/dom", aselcell_sort, box_sort)?;
    let cell_mode = find_attr(indices, "ASelCell/mode", aselcell_sort, mode_sort)?;
    let cell_kind = find_attr(indices, "ASelCell/kind", aselcell_sort, aselkind_sort)?;
    let cell_choice = find_attr(indices, "ASelCell/choice", aselcell_sort, transition_sort)?;
    let mode_domain = find_attr(indices, "Mode/domain", mode_sort, box_sort)?;
    let manifest_modes = find_attr(indices, "Manifest/modes", manifest_sort, modelist_sort)?;
    let tr_clock = find_attr(indices, "Transition/clock", transition_sort, trclock_sort)?;
    let qsat_sys = find_attr(indices, "QSat/sys", qsat_sort, system_sort)?;
    let qrs_region = find_attr(indices, "QRegionSat/region", qrs_sort, region_sort)?;

    // --- relations (fields in bytewise order) -----------------------------
    let asel_exit = find_rel(
        indices,
        "asel_exit",
        &[
            ("cell", &is_elem_eq(aselcell_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;
    let asel_warrant = find_rel(
        indices,
        "asel_warrant",
        &[
            ("mark", &is_elem_eq(qrs_sort)),
            ("wit", &is_elem_eq(aselwit_sort)),
        ],
    )?;
    let sys_transition = find_rel(
        indices,
        "sys_transition",
        &[
            ("sys", &is_elem_eq(system_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;
    let mech_manifest = find_rel(
        indices,
        "mech_manifest",
        &[
            ("manifest", &is_elem_eq(manifest_sort)),
            ("mech", &is_elem_eq(mech_sort)),
        ],
    )?;
    // The event-6 wire shape: the warrant is a QForallSat ENTITY
    // (component/region intrinsic via its attributes); the retired
    // edition's in-row f-field is unrepresentable.
    let warrant_fields: &[FieldPred] = &[
        ("sat", &is_elem_eq(qsat_sort)),
        ("warrant", &is_elem_eq(qfs_sort)),
    ];
    let qsat_warrant = find_rel(indices, "qsat_warrant", warrant_fields)?;
    let qsat_guard_warrant = find_rel(indices, "qsat_guard_warrant", warrant_fields)?;

    // --- the carved-window gate refinement (independent of the content
    // group — relay's carved-choice check consults it alone) --------------
    let tr_dwell_gate = (|| -> Option<Chid> {
        let hypref_sort = sort_by_name(indices, "HypernetRef").ok()?;
        let is_gate = is_elem_eq(hypref_sort);
        let is_tr = is_elem_eq(transition_sort);
        let gate_fields: &[FieldPred] = &[("gate", &is_gate), ("tr", &is_tr)];
        find_rel(indices, "tr_dwell_gate", gate_fields).ok()
    })();

    // --- the OPTIONAL compiled-form group ---------------------------------
    // The event-6 face-typed verdict form (re-taught WITH the
    // QForallSat producer pass, as the mint's resolver note
    // directed): `qvfMk {exists_face: QExistsEntryList, forall_face:
    // QForallSatList}` — field order bytewise, exists_face first.
    // The mark-entity BRIDGE is the region cell: a QRegionSat mark
    // "sits in an exists_face list" (the theory's attach comment)
    // through a `qxeMk {e, region}` entry whose region argument is
    // the mark's own `QRegionSat/region` element — producers emit the
    // mark and its entry citing the SAME region element, so the walk
    // checks citation identity, never semantic equality (formula/
    // component correspondence stays with qtsl_verdict_compile and
    // the grounded walk, where the theory puts it). A mark in a
    // FORALL_FACE list is structurally unrepresentable at event 6
    // (members are QForallSat entities), so the retired
    // floors-decides-false arm is replaced by the theory's own
    // both-slots statement, read GLOBALLY BY ENTITY: any
    // qsat_zeno_budget row in view — on a consuming claim or not —
    // whose position resolves to a forall_face entry carrying the
    // mark's region cell decides FALSE (warranted AND
    // envelope-priced). Where the group is absent (a pre-event-6
    // closure), `attach` refuses loudly — fail-closed, message
    // honest.
    let compiled = (|| -> Option<CompiledFormVocab> {
        let verdictform_sort = sort_by_name(indices, "QVerdictForm").ok()?;
        let qxelist_sort = sort_by_name(indices, "QExistsEntryList").ok()?;
        let qfslist_sort = sort_by_name(indices, "QForallSatList").ok()?;
        let qxe_sort = sort_by_name(indices, "QExistsEntry").ok()?;
        let exists_sort = sort_by_name(indices, "ExistsSpec").ok()?;
        let crossbudget_sort = sort_by_name(indices, "CrossBudget").ok()?;
        let qvf_mk = find_ctor(
            indices,
            "qvfMk",
            verdictform_sort,
            &record_of(vec![
                ("exists_face", be(qxelist_sort)),
                ("forall_face", be(qfslist_sort)),
            ]),
        )
        .ok()?;
        let qxe_mk = find_ctor(
            indices,
            "qxeMk",
            qxe_sort,
            &record_of(vec![("e", be(exists_sort)), ("region", be(region_sort))]),
        )
        .ok()?;
        let qxe_cons = find_ctor(
            indices,
            "qxeCons",
            qxelist_sort,
            &record_of(vec![("head", be(qxe_sort)), ("tail", be(qxelist_sort))]),
        )
        .ok()?;
        let qfs_cons = find_ctor(
            indices,
            "qfsCons",
            qfslist_sort,
            &record_of(vec![("head", be(qfs_sort)), ("tail", be(qfslist_sort))]),
        )
        .ok()?;
        let qfs_region = find_attr(indices, "QForallSat/region", qfs_sort, region_sort).ok()?;
        let qsat_verdict = find_rel(
            indices,
            "qsat_verdict",
            &[
                ("form", &is_elem_eq(verdictform_sort)),
                ("sat", &is_elem_eq(qsat_sort)),
            ],
        )
        .ok()?;
        let qsat_zeno_budget = find_rel(
            indices,
            "qsat_zeno_budget",
            &[
                ("cb", &is_elem_eq(crossbudget_sort)),
                ("pos", &is_nat),
                ("sat", &is_elem_eq(qsat_sort)),
            ],
        )
        .ok()?;
        Some(CompiledFormVocab {
            qvf_mk,
            qxe_mk,
            qxe_cons,
            qfs_cons,
            qfs_region,
            qsat_verdict,
            qsat_zeno_budget,
        })
    })();

    // --- the OPTIONAL content-staging group --------------------------------
    // The syntactic slice of the Transition content stratum. The
    // active region is DERIVED (the former's own comment: "there is
    // no guard field. The active region is the kernel's non-stay
    // support"), so this group reads the support and the landing
    // enclosures exactly where they are already row bytes: scale-view
    // mixtures + rate polynomials, kernel citations' declared image
    // boxes, and the grain kit. Where the group is absent the
    // enabled/closed/relay landing facets refuse loudly — fail-closed,
    // message honest (the R3/R4 posture those facets carried before
    // this staging).
    let content = (|| -> Option<ContentVocab> {
        let scaleview_sort = sort_by_name(indices, "ScaleView").ok()?;
        let branchlist_sort = sort_by_name(indices, "StepBranchList").ok()?;
        let stepres_sort = sort_by_name(indices, "StepRes").ok()?;
        let kernelcite_sort = sort_by_name(indices, "KernelCite").ok()?;
        let trgrain_sort = sort_by_name(indices, "TrGrain").ok()?;
        let sslist_sort = sort_by_name(indices, "SelSpecList").ok()?;
        let hypref_sort = sort_by_name(indices, "HypernetRef").ok()?;
        let polyvec_sort = sort_by_name(indices, "PolyVec").ok()?;
        let poly_sort = sort_by_name(indices, "Poly").ok()?;
        let is_kc = is_elem_eq(kernelcite_sort);
        let is_sv = is_elem_eq(scaleview_sort);
        let is_tr = is_elem_eq(transition_sort);
        let kernel_fields: &[FieldPred] = &[("kernel", &is_kc), ("tr", &is_tr)];
        let tr_kernel = find_rel(indices, "tr_kernel", kernel_fields).ok()?;
        let scale_fields: &[FieldPred] = &[("scale", &is_sv), ("tr", &is_tr)];
        let tr_scale = find_rel(indices, "tr_scale", scale_fields).ok()?;
        let mk_scale_view = find_ctor(
            indices,
            "mkScaleView",
            scaleview_sort,
            &record_of(vec![("mix", be(branchlist_sort)), ("rate", be(poly_sort))]),
        )
        .ok()?;
        let sb_nil = find_ctor(indices, "sbNil", branchlist_sort, &nullary).ok()?;
        let sb_cons = find_ctor(
            indices,
            "sbCons",
            branchlist_sort,
            &record_of(vec![
                ("step", be(stepres_sort)),
                ("tail", be(branchlist_sort)),
                ("weight", bq()),
            ]),
        )
        .ok()?;
        let sr_next = find_ctor(
            indices,
            "srNext",
            stepres_sort,
            &record_of(vec![("image", be(box_sort)), ("reset", be(polyvec_sort))]),
        )
        .ok()?;
        let sr_stay = find_ctor(indices, "srStay", stepres_sort, &nullary).ok()?;
        let sr_cemetery = find_ctor(indices, "srCemetery", stepres_sort, &nullary).ok()?;
        let mk_kernel_cite = find_ctor(
            indices,
            "mkKernelCite",
            kernelcite_sort,
            &record_of(vec![
                ("cemetery", bn()),
                ("hypernet", be(hypref_sort)),
                ("image", be(box_sort)),
                ("next", bn()),
                ("noise", bsh()),
                ("stay", bn()),
            ]),
        )
        .ok()?;
        let hn_digest = find_ctor(
            indices,
            "hnDigest",
            hypref_sort,
            &record_of(vec![("sha256hex", bstr())]),
        )
        .ok();
        let gr_whole = find_ctor(indices, "grWhole", trgrain_sort, &nullary).ok()?;
        let gr_variant = find_ctor(
            indices,
            "grVariant",
            trgrain_sort,
            &record_of(vec![("ix", bn())]),
        )
        .ok()?;
        let gr_tuple = find_ctor(
            indices,
            "grTuple",
            trgrain_sort,
            &record_of(vec![("pre", be(sslist_sort))]),
        )
        .ok()?;
        let gr_path = find_ctor(
            indices,
            "grPath",
            trgrain_sort,
            &record_of(vec![
                ("inner", be(trgrain_sort)),
                ("outer", be(trgrain_sort)),
            ]),
        )
        .ok()?;
        let tr_grain =
            find_attr(indices, "Transition/grain", transition_sort, trgrain_sort).ok()?;
        let poly = build_polycanon_vocab(indices, poly_sort).ok()?;
        Some(ContentVocab {
            tr_kernel,
            tr_scale,
            mk_scale_view,
            sb_nil,
            sb_cons,
            sr_next,
            sr_stay,
            sr_cemetery,
            mk_kernel_cite,
            hn_digest,
            gr_whole,
            gr_variant,
            gr_tuple,
            gr_path,
            tr_grain,
            scaleview_sort,
            branchlist_sort,
            stepres_sort,
            kernelcite_sort,
            trgrain_sort,
            hypref_sort,
            poly,
        })
    })();

    // --- per-sort constructor rosters + the name table --------------------
    let mut kit_sorts = vec![
        aselkind_sort,
        system_sort,
        modelist_sort,
        trclock_sort,
        ennrat_sort,
        region_sort,
        box_sort,
        interval_sort,
    ];
    if let Some(c) = &content {
        kit_sorts.extend([
            c.scaleview_sort,
            c.branchlist_sort,
            c.stepres_sort,
            c.kernelcite_sort,
            c.trgrain_sort,
            c.hypref_sort,
        ]);
    }
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
    let _ = (is_nat, is_q); // kept for symmetry with sibling builders

    Ok(AselVocab {
        ask_dwell,
        ask_relay,
        sys_mech,
        sys_wire,
        sys_hole,
        ml_nil,
        ml_cons,
        box_nil,
        box_cons,
        mk_interval,
        qra_box,
        qra_sublevel,
        qra_affine,
        tk_race,
        tk_demonic,
        tk_forced,
        tk_carved,
        en_fin,
        en_inf,
        wit_sys,
        wit_eps,
        wit_reach,
        cell_wit,
        cell_dom,
        cell_mode,
        cell_kind,
        cell_choice,
        mode_domain,
        manifest_modes,
        tr_clock,
        qsat_sys,
        qrs_region,
        asel_exit,
        asel_warrant,
        sys_transition,
        mech_manifest,
        qsat_warrant,
        qsat_guard_warrant,
        tr_dwell_gate,
        aselkind_sort,
        system_sort,
        modelist_sort,
        trclock_sort,
        ennrat_sort,
        region_sort,
        box_sort,
        interval_sort,
        compiled,
        content,
        ctors,
        names,
    })
}

// ---------------------------------------------------------------------
// The pure combinatorial core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// Exact-ℚ slab-decomposition cover check: does the union of the
/// closed boxes `covers` contain the closed box `target`? All boxes
/// the same width (caller-enforced — width mismatch is a refusal
/// upstream, never silent truncation here). The elementary-cell count
/// is budgeted (`Err` = budget exceeded, a refusal upstream).
///
/// Method: clip each cover to the target (dropping empty clips), cut
/// every axis at every surviving endpoint plus the target's own, and
/// test the midpoint of every elementary cell for membership in some
/// clipped cover. Membership is constant on each open elementary cell
/// (no endpoint crosses its interior), covers are closed (a box
/// containing an open cell contains its closure), and the closed
/// elementary cells tile the target — so all-midpoints-covered decides
/// coverage EXACTLY, both directions. Degenerate axes contribute their
/// single point as the "midpoint".
///
/// Returns `Ok(None)` = covered; `Ok(Some(witness))` = decidedly
/// uncovered, with the uncovered midpoint as the witness.
pub fn check_box_cover(
    target: &[(QQ, QQ)],
    covers: &[Vec<(QQ, QQ)>],
    max_cells: usize,
) -> Result<Option<Vec<QQ>>, String> {
    // An empty target axis = vacuously covered (callers pre-clip; kept
    // for totality).
    if target
        .iter()
        .any(|(lo, hi)| lo.cmp_qq(hi) == Ordering::Greater)
    {
        return Ok(None);
    }
    let n = target.len();
    // Clip covers to the target; drop empty clips.
    let mut clipped: Vec<Vec<(QQ, QQ)>> = Vec::new();
    'next: for c in covers {
        debug_assert_eq!(c.len(), n);
        let mut cl = Vec::with_capacity(n);
        for ((tlo, thi), (clo, chi)) in target.iter().zip(c.iter()) {
            let lo = if clo.cmp_qq(tlo) == Ordering::Greater {
                clo.clone()
            } else {
                tlo.clone()
            };
            let hi = if chi.cmp_qq(thi) == Ordering::Less {
                chi.clone()
            } else {
                thi.clone()
            };
            if lo.cmp_qq(&hi) == Ordering::Greater {
                continue 'next;
            }
            cl.push((lo, hi));
        }
        clipped.push(cl);
    }
    // Per-axis cuts: target endpoints + every clipped endpoint.
    let mut segs: Vec<Vec<(QQ, QQ)>> = Vec::with_capacity(n);
    let mut count: usize = 1;
    for a in 0..n {
        let mut cuts = vec![target[a].0.clone(), target[a].1.clone()];
        for c in &clipped {
            cuts.push(c[a].0.clone());
            cuts.push(c[a].1.clone());
        }
        cuts.sort_by(|x, y| x.cmp_qq(y));
        cuts.dedup_by(|x, y| x.cmp_qq(y) == Ordering::Equal);
        let axis_segs: Vec<(QQ, QQ)> = if cuts.len() == 1 {
            vec![(cuts[0].clone(), cuts[0].clone())]
        } else {
            cuts.windows(2)
                .map(|w| (w[0].clone(), w[1].clone()))
                .collect()
        };
        count = count.saturating_mul(axis_segs.len());
        if count > max_cells {
            return Err(format!(
                "cover slab decomposition beyond its budget ({max_cells} elementary cells)"
            ));
        }
        segs.push(axis_segs);
    }
    // Odometer over the elementary cells; midpoint membership.
    let half = QQ::new(BigInt::from(1), BigUint::from(2u64));
    let mut idx = vec![0usize; n];
    loop {
        let mid: Vec<QQ> = (0..n)
            .map(|a| {
                let (lo, hi) = &segs[a][idx[a]];
                lo.add(hi).mul(&half)
            })
            .collect();
        let covered = clipped.iter().any(|c| {
            c.iter().zip(mid.iter()).all(|((lo, hi), m)| {
                lo.cmp_qq(m) != Ordering::Greater && m.cmp_qq(hi) != Ordering::Greater
            })
        });
        if !covered {
            return Ok(Some(mid));
        }
        // Odometer increment (n == 0: the single 0-D point is done).
        let mut a = 0;
        loop {
            if a == n {
                return Ok(None);
            }
            idx[a] += 1;
            if idx[a] < segs[a].len() {
                break;
            }
            idx[a] = 0;
            a += 1;
        }
    }
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

/// One transition clock, decoded to its wing (finite payloads exact ℚ).
enum ClockRead {
    RaceFin(QQ),
    RaceInf,
    DemonicFin(QQ),
    DemonicInf,
    Forced(QQ),
    /// `tkCarved {floor, ceil: enFin q}` — the carved window at a
    /// finite ceiling (a deadline: at the ceiling the row fires by
    /// itself — the forced wing's law at the window's top).
    CarvedFin {
        floor: QQ,
        ceil: QQ,
    },
    /// `tkCarved {floor, ceil: enInf}` — the carved window open above
    /// (the scheduler's idling member stays lawful, exactly as on the
    /// demonic wing).
    CarvedInf {
        floor: QQ,
    },
}

/// The choice's content presentation, decoded to its syntactic slice.
enum ContentRead {
    /// `tr_kernel` — the `mkKernelCite` element (support opaque behind
    /// the digest; the declared image box is in-body data).
    Kernel(u32),
    /// `tr_scale` — the mixture's classified branches plus the rate
    /// polynomial (support = `{rate > 0}` gated on non-stay mass).
    Scale {
        /// The `srNext` branches' landing image box elements.
        next_images: Vec<u32>,
        /// Whether any cemetery branch is present (the landing facets
        /// refuse on it — the death outcome's admissibility is not
        /// exposed at this stratum; the support facet counts it as
        /// non-stay mass and reads on).
        cemetery: bool,
        /// Whether any non-stay branch (next or cemetery) is present.
        nonstay: bool,
        /// The rate polynomial, decoded exact-ℚ.
        rate: QPoly,
    },
}

/// A stored Poly folded to its canonical [`QPoly`] (summing duplicate
/// monomials, dropping zero coefficients — the polynomial IS the sum
/// of its terms; representation canonicality stays with
/// [`crate::polycanon`]). `Err` = an exponent beyond `u32` — refusal
/// territory (the bernbox budgets would refuse such degrees anyway).
fn stored_to_qpoly(sp: &StoredPoly) -> Result<QPoly, String> {
    let mut map: BTreeMap<Mono, QQ> = BTreeMap::new();
    for (expts, coeff) in &sp.terms {
        let mut mono: Mono = Vec::new();
        for (v, e) in expts.iter().enumerate() {
            if *e == 0 {
                continue;
            }
            let e32 = u32::try_from(*e)
                .map_err(|_| "polynomial exponent beyond u32 — pathological rows".to_string())?;
            mono.push((v as u64, e32));
        }
        let entry = map.entry(mono).or_insert_with(QQ::zero);
        *entry = entry.add(coeff);
    }
    map.retain(|_, c| !c.is_zero());
    Ok(QPoly(map))
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a AselVocab,
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

    fn attr_elem(&mut self, subject: u32, fun: Chid, what: &str) -> Result<u32, EvalError> {
        let v = self.sole_attr_required(subject, fun, what)?;
        self.elem(&v)
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

    /// EVERY distinct row of `rel` in the context, regardless of
    /// which elements it cites (byte-identical rows are one row) —
    /// [`Self::distinct_rel_rows`]'s global-quantification twin,
    /// riding the row context's whole-context enumeration surface:
    /// rows citing external refs, or no elements at all, are
    /// included, and the caller must resolve or refuse each one.
    fn all_rel_rows(
        &mut self,
        rel: Chid,
        arity: usize,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, EvalError> {
        self.step()?;
        let mut out: Vec<&RelRow> = Vec::new();
        for row in self.rows.rows_of(rel) {
            if row.args.len() != arity {
                return Err(ctx_err(
                    self.name,
                    format!("`{what}` row arity mismatch — malformed rows"),
                ));
            }
            if out.iter().any(|r| r.args == row.args) {
                continue;
            }
            out.push(row);
        }
        Ok(out)
    }

    /// The positional-attachment adapter: resolve a zeno-budget row's
    /// `pos` cell down a forall_face `qfsCons` spine to the indexed
    /// `QForallSat` entry.
    ///
    /// POSITION BASE: zero-based, spine-structural — position 0 is
    /// the head of the spine, position n+1 is position n of the tail
    /// (C-CERT-AXES kin: "positions contiguous from zero"). This
    /// method is deliberately the walk's ONLY reader of the position
    /// field: the positional address is expected to dissolve into a
    /// direct entity citation at a future revision of the pricing
    /// row's shape, at which point this adapter deletes whole and
    /// its caller compares cited entries directly.
    ///
    /// Fail-closed: a non-literal or non-Nat position, an ambiguous
    /// spine (multiple qfsCons producers — the sole() posture), a
    /// cyclic tail, an arity-violating row, and a position beyond
    /// the spine in view all refuse — an unresolved position cannot
    /// rule the mark out.
    fn priced_entry(
        &mut self,
        cf: &CompiledFormVocab,
        forall_list: u32,
        pos_cell: &Value,
    ) -> Result<u32, EvalError> {
        let pos = match pos_cell {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => n,
                _ => {
                    return Err(ctx_err(
                        self.name,
                        "qsat_zeno_budget position is not a Nat literal — \
                         malformed rows"
                            .into(),
                    ))
                }
            },
            _ => {
                return Err(ctx_err(
                    self.name,
                    "qsat_zeno_budget position is not a literal — malformed rows".into(),
                ))
            }
        };
        let mut cur = forall_list;
        let mut k = pos;
        let mut spine_visited: HashSet<u32> = HashSet::new();
        loop {
            if !spine_visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    "forall_face spine recurs along its own tail — refusing".into(),
                ));
            }
            self.step()?;
            // Exact-one spine producer (the sole() posture): a second
            // qfsCons row producing this list element would let body
            // order steer position resolution — refuse.
            let mut prod: Option<&CtorRow> = None;
            for r in self.rows.producers(cur) {
                if r.fun != cf.qfs_cons {
                    continue;
                }
                if prod.is_some() {
                    return Err(ctx_err(
                        self.name,
                        format!(
                            "forall_face list element {cur} is produced by \
                             multiple qfsCons rows — ambiguous structure \
                             (P-FUN territory), refusing"
                        ),
                    ));
                }
                prod = Some(r);
            }
            let Some(r) = prod else {
                // nil (or unconstructed) before the indexed position:
                // the pricing row indexes beyond the list in view —
                // undecidable, refuse.
                return Err(ctx_err(
                    self.name,
                    format!(
                        "qsat_zeno_budget position {pos} does not resolve \
                         in the forall_face list in view — the both-slots \
                         facet is undecidable; refusing"
                    ),
                ));
            };
            let [head, tail] = r.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    "qfsCons row arity mismatch — malformed rows".into(),
                ));
            };
            if k == 0 {
                return self.elem(head);
            }
            cur = self.elem(tail)?;
            k -= 1;
        }
    }

    /// A Box element's `(lo, hi)` interval list. Inverted intervals
    /// (`lo > hi`) REFUSE — the angelic contract's interval discipline.
    fn box_intervals(&mut self, box_elem: u32, what: &str) -> Result<Vec<(QQ, QQ)>, EvalError> {
        let cells = self.walk_list(
            self.v.box_sort,
            box_elem,
            self.v.box_nil,
            self.v.box_cons,
            ASEL_MAX_VEC,
            what,
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
            let lo = self.q_lit(lo, "mkInterval/lo")?;
            let hi = self.q_lit(hi, "mkInterval/hi")?;
            if lo.cmp_qq(&hi) == Ordering::Greater {
                return Err(ctx_err(
                    self.name,
                    format!("{what}: inverted interval (lo > hi) — malformed box; refusing"),
                ));
            }
            out.push((lo, hi));
        }
        Ok(out)
    }

    /// The region element decoded to its `qraBox` interval list; the
    /// other region languages refuse with the constructor named.
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
                    "region constructor `{which}` against {against} — outside \
                     the realized qraBox fragment (loudly deferred); refusing, \
                     not deciding"
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
        self.box_intervals(be, against)
    }

    /// The cell's `ASelKind`, as the constructor chid.
    fn cell_kind(&mut self, cell: u32) -> Result<Chid, EvalError> {
        let k = self.attr_elem(cell, self.v.cell_kind, "ASelCell/kind")?;
        Ok(self.sole(self.v.aselkind_sort, k)?.fun)
    }

    /// The set of transitions attached to `sys` (`sys_transition`
    /// rows, dedup by transition element).
    fn attached_transitions(&mut self, sys: u32) -> Result<BTreeSet<u32>, EvalError> {
        let rows = self.distinct_rel_rows(self.v.sys_transition, 0, sys, 2, "sys_transition")?;
        let mut out = BTreeSet::new();
        for r in rows {
            out.insert(self.elem(&r.args[1])?);
        }
        Ok(out)
    }

    /// The subject's manifest mode roster: `sys` must be `SysMech`
    /// (composite/holed subjects refuse, named), with exactly one
    /// `mech_manifest` row; returns the ordered mode elements.
    fn manifest_mode_elems(&mut self, sys: u32) -> Result<Vec<u32>, EvalError> {
        let srow = self.sole(self.v.system_sort, sys)?;
        if srow.fun == self.v.sys_wire || Some(srow.fun) == self.v.sys_hole {
            let which = self.v.name_of(srow.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "subject constructor `{which}` — the angelic manifest walk \
                     is realized for SysMech subjects only (composite and holed \
                     constructor pairs loudly deferred); refusing"
                ),
            ));
        }
        if srow.fun != self.v.sys_mech {
            return Err(ctx_err(
                self.name,
                format!(
                    "element {sys} is constructed by a fun outside the expected \
                     System roster — malformed rows"
                ),
            ));
        }
        let [mech_cell] = srow.args.as_slice() else {
            return Err(ctx_err(self.name, "SysMech row arity mismatch".into()));
        };
        let mech = self.elem(mech_cell)?;
        let mans = self.distinct_rel_rows(self.v.mech_manifest, 1, mech, 2, "mech_manifest")?;
        let manifest = match mans.as_slice() {
            [] => {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "mechanism {mech} carries no manifest content family in \
                         view — the mode roster is undecidable; refusing"
                    ),
                ))
            }
            [m] => self.elem(&m.args[0])?,
            _ => {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "mechanism {mech} carries multiple mech_manifest rows — \
                         ambiguous manifest; refusing"
                    ),
                ))
            }
        };
        let ml = self.attr_elem(manifest, self.v.manifest_modes, "Manifest/modes")?;
        let cells = self.walk_list(
            self.v.modelist_sort,
            ml,
            self.v.ml_nil,
            self.v.ml_cons,
            ASEL_MAX_VEC,
            "manifest mode list",
        )?;
        let mut out = Vec::with_capacity(cells.len());
        for c in cells {
            out.push(self.elem(&c)?);
        }
        Ok(out)
    }

    /// An `EnnRat` element: `Ok(None)` = the infinite point (`enInf`),
    /// `Ok(Some(q))` = `enFin {q}`.
    fn ennrat(&mut self, val: &Value) -> Result<Option<QQ>, EvalError> {
        let ee = self.elem(val)?;
        let erow = self.sole(self.v.ennrat_sort, ee)?;
        if erow.fun == self.v.en_inf {
            return Ok(None);
        }
        if erow.fun == self.v.en_fin {
            let [q] = erow.args.as_slice() else {
                return Err(ctx_err(self.name, "enFin row arity mismatch".into()));
            };
            return Ok(Some(self.q_lit(q, "enFin/q")?));
        }
        Err(ctx_err(
            self.name,
            "EnnRat element outside the enFin/enInf roster — malformed rows".into(),
        ))
    }

    /// One transition's clock, decoded to its wing.
    fn clock_of(&mut self, tr: u32) -> Result<ClockRead, EvalError> {
        let c = self.attr_elem(tr, self.v.tr_clock, "Transition/clock")?;
        let crow = self.sole(self.v.trclock_sort, c)?;
        if crow.fun == self.v.tk_race || crow.fun == self.v.tk_demonic {
            let race = crow.fun == self.v.tk_race;
            let [en] = crow.args.as_slice() else {
                return Err(ctx_err(self.name, "clock wing row arity mismatch".into()));
            };
            return Ok(match (self.ennrat(en)?, race) {
                (None, true) => ClockRead::RaceInf,
                (None, false) => ClockRead::DemonicInf,
                (Some(q), true) => ClockRead::RaceFin(q),
                (Some(q), false) => ClockRead::DemonicFin(q),
            });
        }
        if crow.fun == self.v.tk_forced {
            let [d] = crow.args.as_slice() else {
                return Err(ctx_err(self.name, "tkForced row arity mismatch".into()));
            };
            return Ok(ClockRead::Forced(self.q_lit(d, "tkForced/dwell")?));
        }
        if crow.fun == self.v.tk_carved {
            // Bytewise field order: (ceil, floor) — pinned by the
            // vocabulary's order-pinned shape check.
            let [ceil, floor] = crow.args.as_slice() else {
                return Err(ctx_err(self.name, "tkCarved row arity mismatch".into()));
            };
            let floor = self.q_lit(floor, "tkCarved/floor")?;
            return Ok(match self.ennrat(ceil)? {
                Some(ceil) => ClockRead::CarvedFin { floor, ceil },
                None => ClockRead::CarvedInf { floor },
            });
        }
        let which = self.v.name_of(crow.fun).to_string();
        Err(ctx_err(
            self.name,
            format!(
                "clock constructor `{which}` — outside the tkRace/tkDemonic/\
                 tkForced/tkCarved roster in view; refusing"
            ),
        ))
    }

    /// The cells of a witness (`ASelCell/wit == wit`), each re-verified
    /// through its own exactly-one attribute (an ambiguous wit row on a
    /// candidate refuses).
    fn cells_of_witness(&mut self, wit: u32) -> Result<Vec<u32>, EvalError> {
        let mut seen: BTreeSet<u32> = BTreeSet::new();
        let candidates: Vec<u32> = self
            .rows
            .producers(wit)
            .iter()
            .filter(|r| r.fun == self.v.cell_wit)
            .filter_map(|r| r.args.first())
            .map(|c| self.elem(c))
            .collect::<Result<Vec<_>, _>>()?;
        for cell in candidates {
            if !seen.insert(cell) {
                continue;
            }
            // Re-verify: the candidate's sole wit attribute is this wit
            // (catches double-stated / ambiguous membership).
            let w = self.attr_elem(cell, self.v.cell_wit, "ASelCell/wit")?;
            if w != wit {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "cell {cell} carries conflicting ASelCell/wit rows — \
                         ambiguous membership; refusing"
                    ),
                ));
            }
        }
        Ok(seen.into_iter().collect())
    }

    /// The choice's grain gate: `Ok(None)` = `grWhole`, `Ok(Some(ix))`
    /// = `grVariant {ix}`; the tuple/path grains refuse (the
    /// marked-population strata ride the Bag former — box geometry is
    /// inapplicable at this staging).
    fn grain_gate(&mut self, ct: &ContentVocab, choice: u32) -> Result<Option<u64>, EvalError> {
        let g = self.attr_elem(choice, ct.tr_grain, "Transition/grain")?;
        let grow = self.sole(ct.trgrain_sort, g)?;
        if grow.fun == ct.gr_whole {
            return Ok(None);
        }
        if grow.fun == ct.gr_variant {
            let [ix] = grow.args.as_slice() else {
                return Err(ctx_err(self.name, "grVariant row arity mismatch".into()));
            };
            let Value::Lit(l) = ix else {
                return Err(ctx_err(
                    self.name,
                    "grVariant/ix is not a literal — malformed rows".into(),
                ));
            };
            let LiteralView::Nat(n) = l.view() else {
                return Err(ctx_err(
                    self.name,
                    "grVariant/ix is not a Nat literal — malformed rows".into(),
                ));
            };
            return Ok(Some(n));
        }
        if grow.fun == ct.gr_tuple || grow.fun == ct.gr_path {
            let which = self.v.name_of(grow.fun).to_string();
            return Err(ctx_err(
                self.name,
                format!(
                    "the choice's grain is `{which}` — the marked-population \
                     and nested-selection strata ride the Bag former, where \
                     the box geometry this family realizes is inapplicable; \
                     refusing"
                ),
            ));
        }
        Err(ctx_err(
            self.name,
            "TrGrain element outside the grWhole/grVariant/grTuple/grPath \
             roster — malformed rows"
                .into(),
        ))
    }

    /// Walk the scale view's `sbNil`/`sbCons` branch spine into
    /// `(step, weight)` cells (budgeted, cycle-safe — `sbCons` is
    /// 3-ary, so [`Self::walk_list`] does not apply).
    fn walk_branches(
        &mut self,
        ct: &ContentVocab,
        head: u32,
    ) -> Result<Vec<(Value, Value)>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} recurs along its own branch tail \
                         (P-ACYCLIC territory) — refusing"
                    ),
                ));
            }
            if out.len() > ASEL_MAX_VEC {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "scale-view mixture walk beyond its budget ({ASEL_MAX_VEC}) — refusing"
                    ),
                ));
            }
            let row = self.sole(ct.branchlist_sort, cur)?;
            if row.fun == ct.sb_nil {
                return Ok(out);
            }
            if row.fun != ct.sb_cons {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "element {cur} is constructed by a fun outside the \
                         expected sbNil/sbCons pair — malformed rows"
                    ),
                ));
            }
            // Bytewise field order: (step, tail, weight).
            let [step, tail, weight] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "sbCons row arity mismatch".into()));
            };
            out.push((step.clone(), weight.clone()));
            cur = self.elem(tail)?;
        }
    }

    /// The choice's sole `mkKernelCite` row (shape-validated).
    fn kcite_row(&mut self, ct: &ContentVocab, kc: u32) -> Result<&'a CtorRow, EvalError> {
        let kcrow = self.sole(ct.kernelcite_sort, kc)?;
        if kcrow.fun != ct.mk_kernel_cite {
            return Err(ctx_err(
                self.name,
                "KernelCite element is not an mkKernelCite — malformed rows".into(),
            ));
        }
        if kcrow.args.len() != 6 {
            return Err(ctx_err(
                self.name,
                "mkKernelCite row arity mismatch — malformed rows".into(),
            ));
        }
        Ok(kcrow)
    }

    /// Best-effort digest naming for the kernel-support refusal (a
    /// refusal that names its digest is a better instrument); never
    /// refuses on its own account.
    fn digest_hint(&mut self, ct: &ContentVocab, kcrow: &CtorRow) -> String {
        let Some(hn) = ct.hn_digest else {
            return "an unnamed digest".into();
        };
        // Bytewise mkKernelCite fields: (cemetery, hypernet, image,
        // next, noise, stay).
        let Ok(h) = self.elem(&kcrow.args[1]) else {
            return "an external digest ref".into();
        };
        for row in self.rows.producers(h) {
            if row.fun != hn {
                continue;
            }
            if let Some(Value::Lit(l)) = row.args.first() {
                if let LiteralView::Str(s) = l.view() {
                    let prefix: String = s.chars().take(12).collect();
                    return format!("hnDigest {prefix}…");
                }
            }
        }
        "an unresolved digest".into()
    }

    /// The choice's content presentation, decoded to its syntactic
    /// slice (exactly one of `tr_kernel`/`tr_scale` — zero refuses as
    /// undecidable, co-presence refuses under
    /// `ax/wf/tr_content_excl`, same-kind multiplicity refuses as
    /// ambiguous).
    fn content_of(&mut self, ct: &ContentVocab, choice: u32) -> Result<ContentRead, EvalError> {
        let kernels = self.distinct_rel_rows(ct.tr_kernel, 1, choice, 2, "tr_kernel")?;
        let scales = self.distinct_rel_rows(ct.tr_scale, 1, choice, 2, "tr_scale")?;
        match (kernels.len(), scales.len()) {
            (0, 0) => Err(ctx_err(
                self.name,
                format!(
                    "choice {choice} carries no content presentation in view \
                     (no tr_kernel or tr_scale row) — the derived facets are \
                     undecidable; refusing"
                ),
            )),
            (1, 0) => {
                let kc = self.elem(&kernels[0].args[0])?;
                self.kcite_row(ct, kc)?;
                Ok(ContentRead::Kernel(kc))
            }
            (0, 1) => {
                let sv = self.elem(&scales[0].args[0])?;
                let svrow = self.sole(ct.scaleview_sort, sv)?;
                if svrow.fun != ct.mk_scale_view {
                    return Err(ctx_err(
                        self.name,
                        "ScaleView element is not an mkScaleView — malformed rows".into(),
                    ));
                }
                // Bytewise field order: (mix, rate).
                let [mix, rate] = svrow.args.as_slice() else {
                    return Err(ctx_err(self.name, "mkScaleView row arity mismatch".into()));
                };
                let mix_head = self.elem(mix)?;
                let rate = rate.clone();
                let branches = self.walk_branches(ct, mix_head)?;
                let mut next_images = Vec::new();
                let mut cemetery = false;
                for (step, weight) in &branches {
                    // Weights are strictly positive convex coefficients
                    // (ax/wf/branch_weight_range); outside (0, 1] is
                    // malformed under the report.
                    let w = self.q_lit(weight, "sbCons/weight")?;
                    if w.cmp_qq(&QQ::zero()) != Ordering::Greater
                        || w.cmp_qq(&QQ::one()) == Ordering::Greater
                    {
                        return Err(ctx_err(
                            self.name,
                            "scale-view branch weight outside (0, 1] — malformed \
                             under the weight-range report \
                             (ax/wf/branch_weight_range); refusing"
                                .into(),
                        ));
                    }
                    let se = self.elem(step)?;
                    let srow = self.sole(ct.stepres_sort, se)?;
                    if srow.fun == ct.sr_stay {
                        continue;
                    }
                    if srow.fun == ct.sr_cemetery {
                        cemetery = true;
                        continue;
                    }
                    if srow.fun == ct.sr_next {
                        // Bytewise field order: (image, reset).
                        let [image, _reset] = srow.args.as_slice() else {
                            return Err(ctx_err(self.name, "srNext row arity mismatch".into()));
                        };
                        next_images.push(self.elem(image)?);
                        continue;
                    }
                    return Err(ctx_err(
                        self.name,
                        "StepRes element outside the srNext/srStay/srCemetery \
                         roster — malformed rows"
                            .into(),
                    ));
                }
                let nonstay = cemetery || !next_images.is_empty();
                let sp = decode_stored_poly(self.name, &ct.poly, &[&rate], self.rows)?;
                let rate = stored_to_qpoly(&sp)
                    .map_err(|why| ctx_err(self.name, format!("{why}; refusing")))?;
                Ok(ContentRead::Scale {
                    next_images,
                    cemetery,
                    nonstay,
                    rate,
                })
            }
            (1, 1) => Err(ctx_err(
                self.name,
                format!(
                    "choice {choice} carries both content presentations — \
                     malformed under ax/wf/tr_content_excl; refusing"
                ),
            )),
            _ => Err(ctx_err(
                self.name,
                format!(
                    "choice {choice} carries multiple content rows — ambiguous \
                     content (C-TR-CONTENT territory); refusing"
                ),
            )),
        }
    }

    /// The choice's landing enclosure boxes — the DECLARED
    /// over-approximations the former's out-wire carries (a kernel
    /// citation's `image`; a scale view's `srNext` images). A cemetery
    /// branch refuses (the death outcome's admissibility for the
    /// witnessed law is not exposed at this stratum); an all-stay
    /// mixture returns the empty list (vacuously enclosed).
    fn landing_enclosures(
        &mut self,
        ct: &ContentVocab,
        content: &ContentRead,
    ) -> Result<Vec<Vec<(QQ, QQ)>>, EvalError> {
        match content {
            ContentRead::Kernel(kc) => {
                let kcrow = self.kcite_row(ct, *kc)?;
                // Bytewise mkKernelCite fields: (cemetery, hypernet,
                // image, next, noise, stay).
                let image = self.elem(&kcrow.args[2])?;
                Ok(vec![self.box_intervals(image, "a kernel-cite image")?])
            }
            ContentRead::Scale {
                next_images,
                cemetery,
                ..
            } => {
                if *cemetery {
                    return Err(ctx_err(
                        self.name,
                        "the choice's mixture carries a cemetery branch — the \
                         death outcome's admissibility for the witnessed law \
                         is not exposed at this stratum; refusing"
                            .into(),
                    ));
                }
                let mut out = Vec::with_capacity(next_images.len());
                for image in next_images {
                    out.push(self.box_intervals(*image, "an srNext image")?);
                }
                Ok(out)
            }
        }
    }
}

// ---------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------

/// `qtsl_asel_reach`. Args in wire field order: `wit`.
fn eval_reach(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let wit = d.elem(args[0])?;
    let sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    let eps = d.sole_attr_required(wit, v.wit_eps, "ASelWitness/eps")?;
    d.q_lit(&eps, "ASelWitness/eps")?;
    let reach = d.attr_elem(wit, v.wit_reach, "ASelWitness/reach")?;
    // The warrant's region attribute must be present (the cover target).
    d.sole_attr_required(reach, v.qrs_region, "QRegionSat/region")?;
    // The subject tie arrives via consuming claims (QRegionSat carries
    // no subject attribute): every qsat_warrant / qsat_guard_warrant
    // row citing the reach warrant must agree on the subject.
    let consuming_w = d.distinct_rel_rows(v.qsat_warrant, 1, reach, 2, "qsat_warrant")?;
    let consuming_g =
        d.distinct_rel_rows(v.qsat_guard_warrant, 1, reach, 2, "qsat_guard_warrant")?;
    if consuming_w.is_empty() && consuming_g.is_empty() {
        return Err(ctx_err(
            name,
            format!(
                "reach warrant {reach} is consumed by no claim in view — the \
                 subject tie is undecidable; refusing"
            ),
        ));
    }
    let sats: Vec<u32> = consuming_w
        .iter()
        .chain(consuming_g.iter())
        .map(|r| d.elem(&r.args[0]))
        .collect::<Result<Vec<_>, _>>()?;
    for sat in sats {
        let ssys = d.attr_elem(sat, v.qsat_sys, "QSat/sys")?;
        if ssys != sys {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `qtsl_asel_cover`. Args in wire field order: `wit`.
fn eval_cover(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let wit = d.elem(args[0])?;
    let sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    let reach = d.attr_elem(wit, v.wit_reach, "ASelWitness/reach")?;
    let region = d.attr_elem(reach, v.qrs_region, "QRegionSat/region")?;
    let target = d.qra_box_intervals(region, "the cover target")?;
    let modes = d.manifest_mode_elems(sys)?;
    if modes.is_empty() {
        // mlNil manifest: no mode, nothing to cover — vacuously true.
        return Ok(true);
    }
    // The witness's cells, with mode + dom decoded once.
    let cells = d.cells_of_witness(wit)?;
    let mut geoms: Vec<(u32, u32)> = Vec::with_capacity(cells.len()); // (cell, mode)
    for cell in &cells {
        let m = d.attr_elem(*cell, v.cell_mode, "ASelCell/mode")?;
        geoms.push((*cell, m));
    }
    let mut dom_cache: HashMap<u32, Vec<(QQ, QQ)>> = HashMap::new();
    for m in &modes {
        let mdom_e = d.attr_elem(*m, v.mode_domain, "Mode/domain")?;
        let mdom = d.box_intervals(mdom_e, "a mode domain")?;
        if mdom.len() != target.len() {
            return Err(ctx_err(
                name,
                format!(
                    "mode domain carries {} intervals against the cover \
                     target's {} — width discipline, never silent truncation; \
                     refusing",
                    mdom.len(),
                    target.len()
                ),
            ));
        }
        // The per-mode target: region ∩ Mode/domain (empty ⇒ vacuous).
        let mut tgt: Vec<(QQ, QQ)> = Vec::with_capacity(target.len());
        let mut empty = false;
        for ((tlo, thi), (mlo, mhi)) in target.iter().zip(mdom.iter()) {
            let lo = if mlo.cmp_qq(tlo) == Ordering::Greater {
                mlo.clone()
            } else {
                tlo.clone()
            };
            let hi = if mhi.cmp_qq(thi) == Ordering::Less {
                mhi.clone()
            } else {
                thi.clone()
            };
            if lo.cmp_qq(&hi) == Ordering::Greater {
                empty = true;
                break;
            }
            tgt.push((lo, hi));
        }
        if empty {
            continue; // vacuously covered on this mode
        }
        // Covering boxes: the doms of this mode's cells.
        let mut covers: Vec<Vec<(QQ, QQ)>> = Vec::new();
        for (cell, cm) in &geoms {
            if cm != m {
                continue;
            }
            if !dom_cache.contains_key(cell) {
                let dom_e = d.attr_elem(*cell, v.cell_dom, "ASelCell/dom")?;
                let dom = d.box_intervals(dom_e, "a cell dom")?;
                dom_cache.insert(*cell, dom);
            }
            let dom = &dom_cache[cell];
            if dom.len() != target.len() {
                return Err(ctx_err(
                    name,
                    format!(
                        "cell {cell} dom carries {} intervals against the cover \
                         target's {} — width discipline; refusing",
                        dom.len(),
                        target.len()
                    ),
                ));
            }
            covers.push(dom.clone());
        }
        match check_box_cover(&tgt, &covers, ASEL_MAX_CELLS) {
            Ok(None) => {}
            Ok(Some(_witness)) => return Ok(false),
            Err(why) => return Err(ctx_err(name, format!("{why} — refusing"))),
        }
    }
    Ok(true)
}

/// `qtsl_asel_enabled`. Args in wire field order: `cell`.
fn eval_enabled(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cell = d.elem(args[0])?;
    let wit = d.attr_elem(cell, v.cell_wit, "ASelCell/wit")?;
    let choice = d.attr_elem(cell, v.cell_choice, "ASelCell/choice")?;
    let mode = d.attr_elem(cell, v.cell_mode, "ASelCell/mode")?;
    let dom_e = d.attr_elem(cell, v.cell_dom, "ASelCell/dom")?;
    let dom = d.box_intervals(dom_e, "the cell dom")?;
    let sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    // (a) ATTACHMENT first — an unattached transition can be fired by
    // no resolution of the witnessed System: decidedly nonconformant.
    let attached = d.attached_transitions(sys)?;
    if !attached.contains(&choice) {
        return Ok(false);
    }
    // (b) The cell's mode belongs to the subject's manifest.
    let modes = d.manifest_mode_elems(sys)?;
    if !modes.contains(&mode) {
        return Ok(false);
    }
    // (c) The dom-in-active-region facet, over the content stratum's
    // syntactic slice. The active region is DERIVED — the Transition
    // former's own comment: "there is no guard field. The active
    // region is the kernel's non-stay support" — so this facet reads
    // the support exactly where it is row bytes, and refuses where it
    // rides an opaque citation.
    let Some(ct) = &v.content else {
        return Err(ctx_err(
            name,
            "the choice's active region rides the kernel-cite/grain stratum, \
             and the content vocabulary (tr_kernel/tr_scale/Transition/grain) \
             did not resolve on this closure — refusing"
                .into(),
        ));
    };
    // (c1) The grain gate: a variant-grain choice is active only on
    // its own variant — the cell's mode must sit at the grain's index
    // in the manifest's ordered mode list (position IS the variant
    // index; the theory's manifest comment).
    if let Some(ix) = d.grain_gate(ct, choice)? {
        if modes.iter().filter(|m| **m == mode).count() > 1 {
            return Err(ctx_err(
                name,
                "the cell's mode appears at multiple manifest positions — \
                 its variant index is ambiguous; refusing"
                    .into(),
            ));
        }
        let pos = modes
            .iter()
            .position(|m| *m == mode)
            .expect("facet (b) verified manifest membership");
        if pos as u64 != ix {
            return Ok(false); // active only on variant ix, dom rides another
        }
    }
    // (c2) The support facet.
    match d.content_of(ct, choice)? {
        ContentRead::Kernel(kc) => {
            let kcrow = d.kcite_row(ct, kc)?;
            let digest = d.digest_hint(ct, kcrow);
            Err(ctx_err(
                name,
                format!(
                    "the choice's active region is the cited kernel's non-stay \
                     support, opaque behind {digest} — certificate-stratum \
                     content (the support-warrant row family is the named \
                     event-7 growth); refusing"
                ),
            ))
        }
        ContentRead::Scale { nonstay, rate, .. } => {
            if !nonstay {
                return Ok(false); // an all-stay mixture: empty support
            }
            // dom ⊆ {rate > 0}: strict positivity on a closed box,
            // exact-ℚ Bernstein (sound both directions on its decided
            // arms; inconclusive refuses — fail-closed).
            match box_sign_strict(&rate, &dom)
                .map_err(|why| ctx_err(name, format!("{why} — refusing")))?
            {
                StrictBoxSign::PosCertified => Ok(true),
                StrictBoxSign::NonposWitness => Ok(false),
                StrictBoxSign::Unknown => Err(ctx_err(
                    name,
                    "the rate polynomial is not sign-decided over the cell dom \
                     at its own multidegree (Bernstein-inconclusive, no \
                     subdivision at this staging) — the support facet is \
                     undecidable; refusing"
                        .into(),
                )),
            }
        }
    }
}

/// `qtsl_asel_closed`. Args in wire field order: `cell`. An all-refuse
/// fiber past the structural decode (the carillon R3/R4 posture).
fn eval_closed(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cell = d.elem(args[0])?;
    let wit = d.attr_elem(cell, v.cell_wit, "ASelCell/wit")?;
    let choice = d.attr_elem(cell, v.cell_choice, "ASelCell/choice")?;
    let dom_e = d.attr_elem(cell, v.cell_dom, "ASelCell/dom")?;
    d.box_intervals(dom_e, "the cell dom")?;
    let reach = d.attr_elem(wit, v.wit_reach, "ASelWitness/reach")?;
    let region = d.attr_elem(reach, v.qrs_region, "QRegionSat/region")?;
    let target = d.qra_box_intervals(region, "the landing target")?;
    // The landing-enclosure facet, over the content stratum's
    // syntactic slice: the enclosure is the DECLARED box the former's
    // out-wire carries (a kernel citation's `image`; a scale view's
    // `srNext` images) — the row obligation's subject is the
    // enclosure, not the exact reachable image, so a protruding
    // enclosure decides false.
    let Some(ct) = &v.content else {
        return Err(ctx_err(
            name,
            "the choice's landing enclosure rides the content stratum \
             (tr_kernel/tr_scale), whose vocabulary did not resolve on this \
             closure — the kernel-cite/grain staging is absent; refusing"
                .into(),
        ));
    };
    d.grain_gate(ct, choice)?;
    let content = d.content_of(ct, choice)?;
    let enclosures = d.landing_enclosures(ct, &content)?;
    for enc in &enclosures {
        if enc.len() != target.len() {
            return Err(ctx_err(
                name,
                format!(
                    "a landing enclosure carries {} intervals against the \
                     warrant region's {} — width discipline, never silent \
                     truncation; refusing",
                    enc.len(),
                    target.len()
                ),
            ));
        }
        for ((elo, ehi), (tlo, thi)) in enc.iter().zip(target.iter()) {
            // Per-axis containment: [elo, ehi] ⊆ [tlo, thi].
            if tlo.cmp_qq(elo) == Ordering::Greater || ehi.cmp_qq(thi) == Ordering::Greater {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// `qtsl_asel_ratecap`. Args in wire field order: `cell`.
fn eval_ratecap(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cell = d.elem(args[0])?;
    if d.cell_kind(cell)? != v.ask_dwell {
        return Ok(false); // the dwell-species obligation, off-species
    }
    let wit = d.attr_elem(cell, v.cell_wit, "ASelCell/wit")?;
    let eps_val = d.sole_attr_required(wit, v.wit_eps, "ASelWitness/eps")?;
    let eps = d.q_lit(&eps_val, "ASelWitness/eps")?;
    if eps.cmp_qq(&QQ::zero()) != Ordering::Greater {
        return Ok(false); // a nonpositive dwell floor prices nothing
    }
    let sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    // The exit roster, dedup BY TRANSITION ELEMENT.
    let exits = d.distinct_rel_rows(v.asel_exit, 0, cell, 2, "asel_exit")?;
    let mut roster: BTreeSet<u32> = BTreeSet::new();
    for r in exits {
        roster.insert(d.elem(&r.args[1])?);
    }
    let attached = d.attached_transitions(sys)?;
    // A roster member not attached to the witnessed System: decidedly
    // nonconformant (it charges the cap with a row no resolution owns).
    for tr in &roster {
        if !attached.contains(tr) {
            return Ok(false);
        }
    }
    // An attached transition missing from the roster: activity-on-dom
    // is not relationally exposed, so completeness is undecidable for a
    // sub-roster — roster ⊇ attached is the decidable sufficient
    // condition.
    for tr in &attached {
        if !roster.contains(tr) {
            return Err(ctx_err(
                name,
                format!(
                    "attached transition {tr} is missing from the exit roster — \
                     activity-on-dom is not relationally exposed, completeness \
                     is undecidable for a sub-roster (roster ⊇ attached is the \
                     decidable sufficient condition); refusing"
                ),
            ));
        }
    }
    // Clocks per roster member: race majorants sum; demonic/forced
    // floors recompute strictly positive and contribute zero.
    let mut sum = QQ::zero();
    for tr in &roster {
        match d.clock_of(*tr)? {
            ClockRead::RaceFin(q) => {
                if q.cmp_qq(&QQ::zero()) != Ordering::Greater {
                    return Err(ctx_err(
                        name,
                        format!(
                            "roster transition {tr} carries a nonpositive race \
                             majorant — malformed under the positivity report \
                             (ax/wf/tr_majorant_pos); refusing"
                        ),
                    ));
                }
                sum = sum.add(&q);
            }
            ClockRead::RaceInf => {
                return Err(ctx_err(
                    name,
                    format!(
                        "roster transition {tr} is an instant-clocked attached \
                         row — no-instant-active-on-dom is undecidable without \
                         the active-region stratum; refusing"
                    ),
                ));
            }
            ClockRead::DemonicFin(dq) => {
                if dq.cmp_qq(&QQ::zero()) != Ordering::Greater {
                    return Ok(false); // a chattering scheduler floor
                }
            }
            ClockRead::DemonicInf => {
                return Err(ctx_err(
                    name,
                    format!(
                        "roster transition {tr} carries an infinite dwell floor \
                         — the demonic dead point (ax/qtsl/tr_dwellmin_finite); \
                         refusing"
                    ),
                ));
            }
            ClockRead::Forced(dq) => {
                if dq.cmp_qq(&QQ::zero()) != Ordering::Greater {
                    return Ok(false); // a second instant species
                }
            }
            // The carved-window wing joins the floor-capped class
            // (event 5 — the consumption sentence's ratecap face: a
            // window row's strict floor is the structural cap, so it
            // contributes no majorant; a finite ceil only helps). A
            // tr_dwell_gate row is harmless here: the gate REFINES the
            // window (never widens it — the theory's gate comment), so
            // the strict floor still caps the wing.
            ClockRead::CarvedFin { floor, ceil } => {
                if floor.cmp_qq(&QQ::zero()) != Ordering::Greater {
                    return Ok(false); // a chattering window floor
                }
                if ceil.cmp_qq(&floor) == Ordering::Less {
                    return Err(ctx_err(
                        name,
                        format!(
                            "roster transition {tr} carries an inverted carved \
                             window (finite ceil below floor) — a row that can \
                             never fire, malformed under the window-order \
                             report (ax/wf/tr_carved_window_ordered); refusing"
                        ),
                    ));
                }
            }
            ClockRead::CarvedInf { floor } => {
                if floor.cmp_qq(&QQ::zero()) != Ordering::Greater {
                    return Ok(false); // a chattering window floor
                }
            }
        }
    }
    // The rate cap and the angelic dwell floor are one number read by
    // two quantifiers: sum · eps ≤ 1, exact ℚ.
    Ok(sum.mul(&eps).cmp_qq(&QQ::one()) != Ordering::Greater)
}

/// `qtsl_asel_relay`. Args in wire field order: `cell`.
/// Decidable-false facets first; never true at this staging (the
/// landing-in-dwell-union facet rides the kernel-cite stratum).
fn eval_relay(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cell = d.elem(args[0])?;
    if d.cell_kind(cell)? != v.ask_relay {
        return Ok(false); // the relay-species obligation, off-species
    }
    let wit = d.attr_elem(cell, v.cell_wit, "ASelCell/wit")?;
    let choice = d.attr_elem(cell, v.cell_choice, "ASelCell/choice")?;
    let dom_e = d.attr_elem(cell, v.cell_dom, "ASelCell/dom")?;
    d.box_intervals(dom_e, "the cell dom")?;
    let sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    let attached = d.attached_transitions(sys)?;
    if !attached.contains(&choice) {
        return Ok(false); // an unattached choice fires under no resolution
    }
    // Zero DISCRETIONARY delay: instant-clocked, or demonic/forced/
    // carved past its strictly positive declared floor (the physical
    // dwell is the hop's own bought time, never scheduler discretion;
    // a carved choice is relay-eligible exactly as a demonic one — the
    // theory's words — and its finite ceil additionally bounds the
    // hop's dwell: the window wing's free non-Zeno timing leg,
    // consumed through this row).
    let mut choice_is_carved = false;
    match d.clock_of(choice)? {
        ClockRead::RaceFin(_) => return Ok(false), // a racing row waits
        ClockRead::RaceInf => {}
        ClockRead::DemonicFin(dq) | ClockRead::Forced(dq) => {
            if dq.cmp_qq(&QQ::zero()) != Ordering::Greater {
                return Ok(false);
            }
        }
        ClockRead::DemonicInf => {
            return Err(ctx_err(
                name,
                "the choice carries an infinite dwell floor — the demonic dead \
                 point (ax/qtsl/tr_dwellmin_finite); refusing"
                    .into(),
            ));
        }
        ClockRead::CarvedFin { floor, ceil } => {
            if floor.cmp_qq(&QQ::zero()) != Ordering::Greater {
                return Ok(false); // a chattering window floor
            }
            if ceil.cmp_qq(&floor) == Ordering::Less {
                return Err(ctx_err(
                    name,
                    "the choice carries an inverted carved window (finite ceil \
                     below floor) — a row that can never fire, malformed under \
                     the window-order report (ax/wf/tr_carved_window_ordered); \
                     refusing"
                        .into(),
                ));
            }
            choice_is_carved = true;
        }
        ClockRead::CarvedInf { floor } => {
            if floor.cmp_qq(&QQ::zero()) != Ordering::Greater {
                return Ok(false); // a chattering window floor
            }
            choice_is_carved = true;
        }
    }
    // A dwell gate on the carved CHOICE: the gate's sign-fiber rides
    // an opaque hypernet cite (the gate REFINES the window, so the
    // earliest-permitted-time reading — and fireability itself, at an
    // empty fiber — is undecidable in view). Where the relation is
    // undeclared, gate rows are unrepresentable and the check is
    // vacuous (the standing single-body posture).
    if choice_is_carved {
        if let Some(gate_rel) = v.tr_dwell_gate {
            let gates = d.distinct_rel_rows(gate_rel, 1, choice, 2, "tr_dwell_gate")?;
            if !gates.is_empty() {
                return Err(ctx_err(
                    name,
                    "the choice's carved window is refined by a dwell gate — \
                     the gate's sign-fiber rides an opaque hypernet cite, so \
                     zero-discretionary-delay fireability is undecidable in \
                     view; refusing"
                        .into(),
                ));
            }
        }
    }
    // "The only instant row active on dom": any OTHER attached
    // instant-clocked row makes the facet undecidable (activity is not
    // relationally exposed); none passes the facet.
    for tr in &attached {
        if *tr == choice {
            continue;
        }
        if matches!(d.clock_of(*tr)?, ClockRead::RaceInf) {
            return Err(ctx_err(
                name,
                format!(
                    "another instant-clocked attached row ({tr}) in view — \
                     activity-on-dom is not relationally exposed, the \
                     only-instant-row facet is undecidable; refusing"
                ),
            ));
        }
    }
    // The landing-in-dwell-union facet (the anti-cascade discipline),
    // over the content stratum's syntactic slice: the choice's DECLARED
    // enclosure boxes covered by the union of the witness's dwell
    // cells' doms. Realized for single-mode manifests (a landing box's
    // chart is mode-resolvable there; variant-crossing resolution
    // rides the endo/grain stratum) and non-tuple grains.
    let Some(ct) = &v.content else {
        return Err(ctx_err(
            name,
            "the relay landing-in-dwell-union facet reads the content \
             stratum (tr_kernel/tr_scale/Transition/grain), whose vocabulary \
             did not resolve on this closure — the kernel-cite/grain staging \
             is absent; refusing"
                .into(),
        ));
    };
    d.grain_gate(ct, choice)?;
    let modes = d.manifest_mode_elems(sys)?;
    if modes.len() > 1 {
        return Err(ctx_err(
            name,
            "the subject's manifest carries multiple modes — a landing box's \
             mode is not resolvable at this staging (variant-crossing \
             landings ride the endo/grain stratum); refusing"
                .into(),
        ));
    }
    let content = d.content_of(ct, choice)?;
    let enclosures = d.landing_enclosures(ct, &content)?;
    let cells = d.cells_of_witness(wit)?;
    let mut dwell_doms: Vec<Vec<(QQ, QQ)>> = Vec::new();
    for c2 in cells {
        if d.cell_kind(c2)? != v.ask_dwell {
            continue;
        }
        let dd = d.attr_elem(c2, v.cell_dom, "ASelCell/dom")?;
        dwell_doms.push(d.box_intervals(dd, "a dwell cell dom")?);
    }
    for enc in &enclosures {
        for dd in &dwell_doms {
            if dd.len() != enc.len() {
                return Err(ctx_err(
                    name,
                    format!(
                        "a dwell cell dom carries {} intervals against the \
                         landing enclosure's {} — width discipline, never \
                         silent truncation; refusing",
                        dd.len(),
                        enc.len()
                    ),
                ));
            }
        }
        match check_box_cover(enc, &dwell_doms, ASEL_MAX_CELLS) {
            Ok(None) => {}
            Ok(Some(_witness)) => return Ok(false),
            Err(why) => return Err(ctx_err(name, format!("{why} — refusing"))),
        }
    }
    Ok(true)
}

/// `qtsl_asel_attach`. Args in wire field order: `mark`, `wit`.
fn eval_attach(
    name: &str,
    v: &AselVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let mark = d.elem(args[0])?;
    let wit = d.elem(args[1])?;
    let wit_sys = d.attr_elem(wit, v.wit_sys, "ASelWitness/sys")?;
    // (a) At most one witness per mark (keying BY ENTITY): the row
    // under evaluation plus every asel_warrant row citing the mark.
    let warrants = d.distinct_rel_rows(v.asel_warrant, 0, mark, 2, "asel_warrant")?;
    let mut wits: BTreeSet<u32> = BTreeSet::new();
    wits.insert(wit);
    for r in warrants {
        wits.insert(d.elem(&r.args[1])?);
    }
    if wits.len() > 1 {
        return Ok(false);
    }
    let Some(cf) = &v.compiled else {
        return Err(ctx_err(
            name,
            "compiled-form vocabulary (the event-6 face-typed qvfMk / \
             qsat_verdict group) absent from the closure — mark placement \
             is undecidable; refusing"
                .into(),
        ));
    };
    // (b) The mark's exists-face placements, by the region bridge +
    // the upward walk (revision event 6): the mark's region cell,
    // then every qxeMk entry citing that region ELEMENT (args
    // bytewise (e, region) — citation identity, never semantic
    // equality: producers emit the mark and its entry against the
    // same region element by construction), then qxeCons tail-links
    // climbed to qvfMk exists_face slots (args bytewise (exists_face,
    // forall_face)). A mark in a forall_face list is structurally
    // unrepresentable (members are QForallSat entities), so no
    // floor-face arm exists; the both-slots refusal is (d) below.
    // Complete for single-body context.
    let mark_region = d.attr_elem(mark, v.qrs_region, "QRegionSat/region")?;
    let region_cell = Value::Ref(ElemRef::Local(mark_region));
    let mut stack: Vec<u32> = Vec::new();
    for r in rows.arg_rows(mark_region) {
        if r.fun == cf.qxe_mk && r.args.get(1) == Some(&region_cell) {
            // The bridge entry element; its qxeCons cells seed the
            // spine climb.
            let entry = d.elem(&r.value)?;
            // Exact-one bridge producer (the sole() posture — the row
            // context reports duplicate producers; the evaluator is
            // the loud party): a second qxeMk row producing this
            // entry would make its region citation ambiguous.
            let mk_producers = rows
                .producers(entry)
                .iter()
                .filter(|p| p.fun == cf.qxe_mk)
                .count();
            if mk_producers > 1 {
                return Err(ctx_err(
                    name,
                    format!(
                        "bridge entry {entry} is produced by multiple qxeMk \
                         rows — ambiguous structure (P-FUN territory), \
                         refusing"
                    ),
                ));
            }
            let entry_cell = Value::Ref(ElemRef::Local(entry));
            for c in rows.arg_rows(entry) {
                if c.fun == cf.qxe_cons && c.args.first() == Some(&entry_cell) {
                    stack.push(d.elem(&c.value)?);
                }
            }
        }
    }
    let mut visited: HashSet<u32> = HashSet::new();
    // The forms whose exists_face carries the mark — (c)'s
    // enumeration root. ((d) no longer roots here: its sweep is
    // global by entity.)
    let mut mark_forms: BTreeSet<u32> = BTreeSet::new();
    let mut steps = 0usize;
    while let Some(l) = stack.pop() {
        if !visited.insert(l) {
            continue;
        }
        steps += 1;
        if steps > ASEL_MAX_WALK {
            return Err(ctx_err(
                name,
                format!("mark-placement walk beyond its budget ({ASEL_MAX_WALK}) — refusing"),
            ));
        }
        let l_cell = Value::Ref(ElemRef::Local(l));
        for r in rows.arg_rows(l) {
            if r.fun == cf.qxe_cons && r.args.get(1) == Some(&l_cell) {
                stack.push(d.elem(&r.value)?);
            }
            if r.fun == cf.qvf_mk && r.args.first() == Some(&l_cell) {
                let form = d.elem(&r.value)?;
                // Exact-one form producer (the sole() posture): a
                // second qvfMk row producing the same form element
                // would let body order pick which forall_face list
                // the both-slots check reads — ambiguity must refuse,
                // never resolve by overwrite.
                let qvf_producers = rows
                    .producers(form)
                    .iter()
                    .filter(|p| p.fun == cf.qvf_mk)
                    .count();
                if qvf_producers > 1 {
                    return Err(ctx_err(
                        name,
                        format!(
                            "form {form} is produced by multiple qvfMk rows — \
                             ambiguous structure (P-FUN territory), refusing"
                        ),
                    ));
                }
                // Arity-validate the qvfMk row at first contact even
                // though (d) re-derives the forall list per priced
                // claim — a malformed row refuses here, never waits
                // for a pricing row to expose it.
                if r.args.get(1).is_none() {
                    return Err(ctx_err(
                        name,
                        "qvfMk row arity mismatch — malformed rows".into(),
                    ));
                }
                mark_forms.insert(form);
            }
        }
    }
    if mark_forms.is_empty() {
        return Err(ctx_err(
            name,
            format!(
                "mark {mark} (via its region cell) sits in no exists_face \
                 list in view — not compiled or not consumed; the subject \
                 tie is undecidable; refusing"
            ),
        ));
    }
    // (c) Subject agreement across every consuming claim (shared marks
    // demand one agreed witness System).
    let mut any_sat = false;
    for form in &mark_forms {
        let verdicts = d.distinct_rel_rows(cf.qsat_verdict, 0, *form, 2, "qsat_verdict")?;
        for r in verdicts {
            let sat = d.elem(&r.args[1])?;
            any_sat = true;
            // C-CERT-CLAIM kin ("zero rows = not compiled; at most
            // one is admission conformance"): a claim carrying a
            // second qsat_verdict form attachment makes the pricing
            // walk's form resolution ambiguous — refuse.
            let sat_forms = d.distinct_rel_rows(cf.qsat_verdict, 1, sat, 2, "qsat_verdict")?;
            let mut forms_of_sat: BTreeSet<u32> = BTreeSet::new();
            for fr in sat_forms {
                forms_of_sat.insert(d.elem(&fr.args[0])?);
            }
            if forms_of_sat.len() > 1 {
                return Err(ctx_err(
                    name,
                    format!(
                        "claim {sat} carries multiple qsat_verdict form \
                         attachments — ambiguous compiled form \
                         (C-CERT-CLAIM territory); refusing"
                    ),
                ));
            }
            let ssys = d.attr_elem(sat, v.qsat_sys, "QSat/sys")?;
            if ssys != wit_sys {
                return Ok(false);
            }
        }
    }
    if !any_sat {
        return Err(ctx_err(
            name,
            format!(
                "mark {mark} rides exists_face lists of forms with no \
                 qsat_verdict row in view — not compiled or not consumed; \
                 the subject tie is undecidable; refusing"
            ),
        ));
    }
    // (d) The both-slots refusal, GLOBAL BY ENTITY — the budget
    // family's polarity comment: "one entity warranted as a mark
    // anywhere and budget-indexed on the forall face anywhere is
    // refused." The sweep therefore enumerates EVERY qsat_zeno_budget
    // row in view (the whole-context surface — an element-keyed view
    // would structurally miss rows on claims the mark walk never
    // reached, the confirmed fail-open this widening repairs). Per
    // row (args bytewise (cb, pos, sat)): resolve the priced claim,
    // its sole compiled form, that form's forall_face list, and the
    // row's position down the spine; an indexed QForallSat entry
    // carrying the mark's region cell means the mark is both
    // warranted (exists face, angelic) and envelope-priced (forall
    // face) — decide FALSE. A row the walk cannot resolve in view
    // (external claim ref, no compiled form, no qvfMk producer,
    // unresolvable position) refuses: the walk cannot rule the mark
    // out.
    let budgets = d.all_rel_rows(cf.qsat_zeno_budget, 3, "qsat_zeno_budget")?;
    for b in budgets {
        let sat = d.elem(&b.args[2])?;
        // The priced claim's sole compiled form (C-CERT-CLAIM kin —
        // the same at-most-one demand (c) makes of consuming claims).
        let sat_forms = d.distinct_rel_rows(cf.qsat_verdict, 1, sat, 2, "qsat_verdict")?;
        let mut forms_of_sat: BTreeSet<u32> = BTreeSet::new();
        for fr in sat_forms {
            forms_of_sat.insert(d.elem(&fr.args[0])?);
        }
        if forms_of_sat.len() > 1 {
            return Err(ctx_err(
                name,
                format!(
                    "claim {sat} carries multiple qsat_verdict form \
                     attachments — ambiguous compiled form \
                     (C-CERT-CLAIM territory); refusing"
                ),
            ));
        }
        let Some(&form) = forms_of_sat.iter().next() else {
            return Err(ctx_err(
                name,
                format!(
                    "qsat_zeno_budget row prices claim {sat} with no \
                     qsat_verdict row in view — the priced form is \
                     unresolvable, the walk cannot rule the mark out; \
                     refusing"
                ),
            ));
        };
        // The form's forall_face list (exact-one qvfMk producer —
        // the sole() posture).
        let mut prod: Option<&CtorRow> = None;
        for r in rows.producers(form) {
            if r.fun != cf.qvf_mk {
                continue;
            }
            if prod.is_some() {
                return Err(ctx_err(
                    name,
                    format!(
                        "form {form} is produced by multiple qvfMk rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ),
                ));
            }
            prod = Some(r);
        }
        let Some(r) = prod else {
            return Err(ctx_err(
                name,
                format!(
                    "priced claim {sat}'s compiled form {form} has no \
                     qvfMk row in view — the forall face is unresolvable, \
                     the walk cannot rule the mark out; refusing"
                ),
            ));
        };
        let forall_list = match r.args.get(1) {
            Some(v) => d.elem(v)?,
            None => {
                return Err(ctx_err(
                    name,
                    "qvfMk row arity mismatch — malformed rows".into(),
                ))
            }
        };
        let entry = d.priced_entry(cf, forall_list, &b.args[1])?;
        let entry_region = d.attr_elem(entry, cf.qfs_region, "QForallSat/region")?;
        if entry_region == mark_region {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Family dispatch (provider.rs routes here).
pub(crate) fn eval_asel(
    name: &str,
    v: &AselVocab,
    kind: ASelKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        ASelKind::Reach => eval_reach(name, v, args, rows),
        ASelKind::Cover => eval_cover(name, v, args, rows),
        ASelKind::Enabled => eval_enabled(name, v, args, rows),
        ASelKind::Closed => eval_closed(name, v, args, rows),
        ASelKind::Ratecap => eval_ratecap(name, v, args, rows),
        ASelKind::Relay => eval_relay(name, v, args, rows),
        ASelKind::Attach => eval_attach(name, v, args, rows),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn bx(axes: &[(i64, i64)]) -> Vec<(QQ, QQ)> {
        axes.iter().map(|(lo, hi)| (q(*lo, 1), q(*hi, 1))).collect()
    }

    #[test]
    fn cover_1d_exact() {
        // [0,2] = [0,1] ∪ [1,2].
        assert_eq!(
            check_box_cover(&bx(&[(0, 2)]), &[bx(&[(0, 1)]), bx(&[(1, 2)])], 1 << 16),
            Ok(None)
        );
    }

    #[test]
    fn cover_1d_gap() {
        // [0,1] ∪ [3/2,2] misses (1, 3/2); the witness midpoint is 5/4.
        let covers = vec![bx(&[(0, 1)]), vec![(q(3, 2), q(2, 1))]];
        let got = check_box_cover(&bx(&[(0, 2)]), &covers, 1 << 16).unwrap();
        assert_eq!(got, Some(vec![q(5, 4)]));
    }

    #[test]
    fn cover_2d_l_shape() {
        // Left column ∪ bottom row cover the L; the top-right quadrant
        // is the hole — the slab check must find a midpoint inside it.
        let target = bx(&[(0, 2), (0, 2)]);
        let covers = vec![bx(&[(0, 1), (0, 2)]), bx(&[(0, 2), (0, 1)])];
        let got = check_box_cover(&target, &covers, 1 << 16).unwrap();
        assert_eq!(got, Some(vec![q(3, 2), q(3, 2)]));
        // Fill the hole: covered.
        let mut full = covers.clone();
        full.push(bx(&[(1, 2), (1, 2)]));
        assert_eq!(check_box_cover(&target, &full, 1 << 16), Ok(None));
    }

    #[test]
    fn cover_degenerate_axis() {
        // A point axis still demands coverage: {1} × [0,2].
        let target = vec![(q(1, 1), q(1, 1)), (q(0, 1), q(2, 1))];
        assert_eq!(
            check_box_cover(&target, &[bx(&[(0, 2), (0, 2)])], 1 << 16),
            Ok(None)
        );
        let got = check_box_cover(&target, &[bx(&[(0, 2), (0, 1)])], 1 << 16).unwrap();
        assert!(got.is_some(), "the uncovered half of the segment is found");
    }

    #[test]
    fn cover_empty_target_vacuous() {
        // An inverted target axis = empty target = vacuously covered.
        let target = vec![(q(2, 1), q(1, 1))];
        assert_eq!(check_box_cover(&target, &[], 1 << 16), Ok(None));
    }

    #[test]
    fn cover_no_covers_uncovered() {
        let got = check_box_cover(&bx(&[(0, 1)]), &[], 1 << 16).unwrap();
        assert_eq!(got, Some(vec![q(1, 2)]));
    }

    #[test]
    fn cover_budget_refuses() {
        // 33 covers × 1 axis → 66 cuts → >32 segments against budget 4.
        let covers: Vec<Vec<(QQ, QQ)>> =
            (0..33).map(|i| vec![(q(i, 100), q(i + 1, 100))]).collect();
        assert!(check_box_cover(&bx(&[(0, 1)]), &covers, 4).is_err());
    }
}
