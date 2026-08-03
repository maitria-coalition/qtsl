//! The carillon discharge-plan family: the R2–R5 grid/region/manifest
//! recomputes, evaluated over rows.
//!
//! Vocabulary refreshed to the event-3 closure (alongside the
//! syswire refresh): the Transition-former restructure
//! removed jump and switch content from the manifest stratum —
//! `Manifest/transitions`, `Mode/jumps`, `mkJump`, and the
//! `Transition/{src,dst,reset_image}` attributes are no longer
//! declared ("no guard field, no forced flag, no rate field, and no
//! source/target fields on transitions: each was presentation, and
//! each is derived from kernel structure, carried by the grain, or
//! owned by the clock" — the theory's deliberately-absent block).
//! Transition content now rides `sys_transition` attachments whose
//! kernels are CITED (`tr_kernel`/`KernelCite`), with reset
//! polynomials keyed at the certificate stratum (the `prReset`
//! roles) — none of it relationally exposed at this family's
//! single-body row grain. Consequently R3/R4 are claim-and-refuse
//! fibers (below), R2/R5 keep their full recomputes, and the family's
//! box anchor resolves through `qraBox`'s domain rather than the
//! retired manifest slice. The R3/R4 PURE checks and their
//! cross-implementation corpus tie are deliberately retained
//! (`check_dbar_closure`, `check_gap_a` and kin below): they are the
//! reference semantics the successor arm re-wires onto
//! certificate-stratum reset rows when that staging lands.
//!
//! Four relations, one vocabulary group (grid-complex + box-list
//! rows), ported from the carillon producer's executable references —
//! each evaluator is the sole authority its certificate's claim is
//! read against (recompute, don't trust):
//!
//! - **`qtsl_cell_cover [cells: Shape, cx: QGridCx, region: Box]`**
//!   (R2): the named grid cells of `cx` jointly cover the region box —
//!   fail-closed on holes. Reference: `_cells_covering` /
//!   `_cells_covering_box` (`carillon_discharge.py:329-394`), re-homed
//!   onto the unified grid arena: `cells` names top cells of the
//!   complex by canonical index ([`crate::gridcx::enumerate_cells`],
//!   axis 0 fastest in the degenerate leaf), and coverage is decided
//!   against the grid's own cut lists. The check is COVERAGE
//!   (`region ⊆ ∪ cells`): named cells that miss the region are
//!   harmless extra obligations for the consuming rule, never a hole.
//! - **`qtsl_dbar_closure [dbar: Box, m: Manifest, mode: Mode]`**
//!   (R3; the event-3 declaration cites the mode as an ENTITY, the
//!   certificate-table convention — the pre-event-3 form took a Str
//!   name): `dbar` IS the mode's one-jump closed domain — the
//!   per-axis interval hull of the mode's domain with every reset
//!   image landing in the mode. Reference: `Manifest.closed_domain`
//!   (`carillon/manifest.py:218-231`), held in the pure core
//!   ([`check_dbar_closure`]). The ROW fiber REFUSES (the R8-style
//!   loud deferral): the required reset images ride kernel cites and
//!   certificate-stratum reset roles, not relationally exposed in
//!   single-body context — when that staging lands in the theory,
//!   this arm grows the recompute against the entity-cited mode.
//! - **`qtsl_gap_a [m: Manifest]`** (R4): every reset image in the
//!   manifest is contained in the destination mode's domain.
//!   Reference: `_image_contained` / `_gap_a_notes`
//!   (`carillon/compile.py:210-273`), held in the pure core
//!   ([`check_gap_a`]: stop region empty — the sound direction; 1-D
//!   as specced, n-D refuses). The ROW fiber REFUSES exactly as R3's:
//!   same retired stratum, same deferral, same growth point.
//! - **`qtsl_lowbound_boxes [cover: QBoxList, dbar: Box, region:
//!   QRegionAtom]`** (R5): `cover` is an EXACT box cover of
//!   `region ∩ dbar` — every cover box inside the intersection, and
//!   their union equal to it ("scope equality, not
//!   over-approximation"). Reference: `_region_boxes`
//!   (`carillon_discharge.py:520-570`). At this declaration's grain
//!   the region is a single atom: `qraBox` resolves; every other
//!   `QRegionAtom` constructor (`qraSublevel`, `qraAffine`) is the
//!   RCert/eps-rounded/non-linear seam the reference names — REFUSED,
//!   never guessed.
//!
//! # Adjudicated boundaries (for review eyes)
//!
//! - **The zip trap, refused** (pure core — corpus-tied). The python
//!   `closed_domain` hulls with `zip(box, img)`, which would silently
//!   TRUNCATE an image whose arity disagrees with the domain's. Here
//!   every image of mismatched arity refuses — a claim about
//!   malformed manifests is not decidable content.
//! - **Dangling mode references refuse** (pure core — corpus-tied). A
//!   transition whose `src` or `dst` names no mode (or names two)
//!   refuses; the python reference would silently skip a dangling
//!   `src` in its mode-major loop.
//! - **Degenerate or inverted region boxes refuse `qtsl_cell_cover`**
//!   (the reference's own named seam: "Bernstein cells need
//!   full-dimensional simplices" — `carillon_discharge.py:361-365`;
//!   its 1-D path's vacuous pass on an empty scope is a quirk this
//!   port deliberately does not preserve).
//! - **Grid wire violations decide FALSE** (the
//!   [`crate::morse`] `GridCxWire` precedent: ill-formed certificate
//!   content is a decided violation); **v0 profile refusals REFUSE**
//!   (multi-patch, Kuhn groups, non-identity charts — schema-valid
//!   content this checker cannot decide).
//! - **Out-of-range or non-ascending `cells` decide FALSE** (declared
//!   Shape content — the bllattice declared-index precedent; the
//!   Shape carrier is an ascending set literal, so descent and
//!   duplication are canonicality violations, not undecidables).
//! - **Empty cover boxes decide FALSE** for `qtsl_lowbound_boxes` (the
//!   reference never emits an inverted box: provably-empty
//!   intersections return `[]`, not `[∅]`).
//! - **An empty intersection demands an empty cover**, exactly
//!   (`[] = provably empty` — the reference's own contract).
//!
//! The python twins in the frozen corpus
//! (`tests/fixtures/carillon_pyref_gen.py`) have no refusal channel,
//! so the corpus carries in-domain shapes only (matched arities, 1-D
//! gap-A manifests, box atoms) — the refusal classes are pinned by
//! the dedicated battery instead.
//!
//! Verdict discipline (the crate's): decided violations of the
//! recompute are `Ok(false)`; missing/conflicting/ambiguous rows,
//! external references, non-box atoms, n-D gap-A manifests, arity
//! mismatches, and exhausted budgets REFUSE with a reason, never
//! guessing.

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{CarillonKind, EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

const F_CELL_COVER: &[(&str, &str)] = &[("cells", "Shape"), ("cx", "QGridCx"), ("region", "Box")];
const F_DBAR: &[(&str, &str)] = &[("dbar", "Box"), ("m", "Manifest"), ("mode", "Mode")];
const F_GAP_A: &[(&str, &str)] = &[("m", "Manifest")];
const F_FLOOR: &[(&str, &str)] = &[
    ("cover", "QBoxList"),
    ("dbar", "Box"),
    ("region", "QRegionAtom"),
];

/// The carillon family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_cell_cover",
        F_CELL_COVER,
        RelKind::Carillon(CarillonKind::CellCover),
    ),
    (
        "qtsl_dbar_closure",
        F_DBAR,
        RelKind::Carillon(CarillonKind::DbarClosure),
    ),
    ("qtsl_gap_a", F_GAP_A, RelKind::Carillon(CarillonKind::GapA)),
    (
        "qtsl_lowbound_boxes",
        F_FLOOR,
        RelKind::Carillon(CarillonKind::FloorBoxes),
    ),
];

/// Structural-walk node budget (refusal beyond, never divergence).
const MAX_DECODE_STEPS: usize = 1 << 20;

/// Enumeration budgets: the named-cell set of a cover claim and the
/// sub-cell grid of a floor-cover equality check (refusal beyond).
pub const CELL_COVER_BUDGET: usize = 1 << 20;
pub const FLOOR_COVER_BUDGET: u64 = 1 << 20;

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// The carillon family's resolved vocabulary: the unified-arena grid
/// complex, the box-list and box-atom constructors (the QtslCert
/// side), and the Qtsl box kit, name-selected once at construction
/// and shape-verified (names select, shapes verify, identities pin).
///
/// The manifest slice this vocabulary used to pin —
/// `Manifest/transitions`, `Mode/{name,domain,jumps}`, `mkJump`, the
/// `Transition/{src,dst,reset_image}` attributes and the trl/jl list
/// kits — was RETIRED from the theory at the event-3 closure (the
/// Transition-former restructure; module doc). Resolving any of those
/// names would un-claim the whole family against the real closure, so
/// none is resolved: R3/R4 refuse at evaluation grain instead.
#[derive(Debug, Clone)]
pub struct CarillonVocab {
    // Boxes (the Qtsl Box cons-list; shared by every box field here).
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    // The unified-arena grid complex (the morse family's wire, own
    // pinned copies — the third decoder of this wire; the
    // admission/morse two-family seam is recorded debt (DEBT-5), and
    // this family deepens it knowingly: unification is anneal
    // material, not lane material).
    qgc_mk: Chid,
    qpt_leaf: Chid,
    qpt_split: Chid,
    qgl_nil: Chid,
    qgl_cons: Chid,
    qgen_interval: Chid,
    qgen_kuhn: Chid,
    qch_identity: Chid,
    qch_digest: Chid,
    qrl_nil: Chid,
    qrl_cons: Chid,
    // The certificate box list + the box region atom.
    qbx_nil: Chid,
    qbx_cons: Chid,
    qra_box: Chid,
    /// Per-sort constructor rosters (the `sole` filter): every
    /// declared constructor whose codomain is one of the family's
    /// element sorts — including the non-box `QRegionAtom`
    /// constructors, so a sublevel/affine atom resolves to a NAMED
    /// refusal rather than "no constructor row".
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the carillon vocabulary over the declared indices. `Err` →
/// the family is not claimed (declared-but-unbound, safe-fail).
///
/// The Box sort is anchored through `qraBox`'s unary domain (the
/// region atom cites a Box), not through the retired manifest slice —
/// the event-3 refresh (module doc).
pub fn build_carillon_vocab(
    indices: &[&TheoryIndex],
    gridcx_sort: Chid,
    boxlist_sort: Chid,
    region_sort: Chid,
) -> Result<CarillonVocab, String> {
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
    let nullary = |sig: &DomainSig| -> Result<(), String> {
        if *sig == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };
    enum F {
        Ground(Ground),
        Elem(Chid),
        Capture,
        AnyElem,
    }
    let record = |sig: &DomainSig, want: &[(&str, F)]| -> Result<Vec<Chid>, String> {
        let DomainSig::Record(fields) = sig else {
            return Err("expected a record domain".into());
        };
        if fields.len() != want.len() {
            return Err(format!(
                "expected {} fields, found {}",
                want.len(),
                fields.len()
            ));
        }
        let mut captured = Vec::new();
        for ((name, sort), (want_name, want_sort)) in fields.iter().zip(want) {
            if name != want_name {
                return Err(format!("field `{name}` where `{want_name}` expected"));
            }
            match (want_sort, sort) {
                (F::Ground(g), SortKey::Ground(found)) if found == g => {}
                (F::Elem(c), SortKey::Elem(found)) if found == c => {}
                (F::Capture, SortKey::Elem(found)) => captured.push(*found),
                (F::AnyElem, SortKey::Elem(_)) => {}
                _ => return Err(format!("field `{name}` has an unexpected sort")),
            }
        }
        Ok(captured)
    };
    // --- the box anchor: `qraBox`'s unary domain ------------------------
    // (The retired manifest slice used to anchor Box via Mode/domain;
    // the event-3 refresh anchors through the region atom instead.
    // Resolved across ALL swept indices with ambiguity refused — the
    // syswire `mkPortEq` pattern.)
    let mut qra: Option<(Chid, Chid)> = None; // (qraBox, box sort)
    for index in indices {
        let Some(d) = index.fun("qraBox") else {
            continue;
        };
        if d.relational || d.codomain != Some(SortKey::Elem(region_sort)) {
            return Err("`qraBox` is not a constructor of the region-atom sort".into());
        }
        let DomainSig::Unary(SortKey::Elem(b)) = d.domain else {
            return Err("`qraBox`: expected a unary constructor on the Box sort".into());
        };
        if qra.is_some() {
            return Err("`qraBox` names two distinct constructors across the \
                        swept revisions — ambiguous, refusing to pick"
                .into());
        }
        qra = Some((d.chid, b));
    }
    let Some((qra_box, box_sort)) = qra else {
        return Err("no `qraBox` constructor among the swept revisions".into());
    };

    // --- boxes (shared by every box field in the family) --------------
    let (box_nil, _) = find("boxNil", box_sort, &nullary)?;
    let (box_cons, bc_sig) = find("boxCons", box_sort, &|s| {
        record(s, &[("head", F::Capture), ("tail", F::Elem(box_sort))]).map(|_| ())
    })?;
    let interval_sort = record(
        &bc_sig,
        &[("head", F::Capture), ("tail", F::Elem(box_sort))],
    )
    .expect("checked above")[0];
    let (mk_interval, _) = find("mkInterval", interval_sort, &|s| {
        record(
            s,
            &[("hi", F::Ground(Ground::Q)), ("lo", F::Ground(Ground::Q))],
        )
        .map(|_| ())
    })?;

    // --- the unified-arena grid complex (QtslCert) ---------------------
    let (qgc_mk, mk_sig) = find("qgcMk", gridcx_sort, &|s| {
        record(s, &[("dom", F::Elem(box_sort)), ("tree", F::Capture)]).map(|_| ())
    })?;
    let patchtree_sort = record(&mk_sig, &[("dom", F::Elem(box_sort)), ("tree", F::Capture)])
        .expect("checked above")[0];
    let (qpt_leaf, leaf_sig) = find("qptLeaf", patchtree_sort, &|s| {
        record(
            s,
            &[
                ("chart", F::Capture),
                ("gens", F::Capture),
                ("part", F::Ground(Ground::Shape)),
            ],
        )
        .map(|_| ())
    })?;
    let captured = record(
        &leaf_sig,
        &[
            ("chart", F::Capture),
            ("gens", F::Capture),
            ("part", F::Ground(Ground::Shape)),
        ],
    )
    .expect("checked above");
    let (chartref_sort, genlist_sort) = (captured[0], captured[1]);
    let (qpt_split, _) = find("qptSplit", patchtree_sort, &|s| {
        record(
            s,
            &[
                ("axis", F::Ground(Ground::Nat)),
                ("cut", F::Ground(Ground::Q)),
                ("hi", F::Elem(patchtree_sort)),
                ("lo", F::Elem(patchtree_sort)),
            ],
        )
        .map(|_| ())
    })?;
    let (qgl_nil, _) = find("qglNil", genlist_sort, &nullary)?;
    let (qgl_cons, glc_sig) = find("qglCons", genlist_sort, &|s| {
        record(s, &[("gen", F::Capture), ("tail", F::Elem(genlist_sort))]).map(|_| ())
    })?;
    let groupgen_sort = record(
        &glc_sig,
        &[("gen", F::Capture), ("tail", F::Elem(genlist_sort))],
    )
    .expect("checked above")[0];
    let (qgen_interval, gi_sig) = find("qgenInterval", groupgen_sort, &|s| {
        record(s, &[("cuts", F::Capture)]).map(|_| ())
    })?;
    let ratlist_sort = record(&gi_sig, &[("cuts", F::Capture)]).expect("checked above")[0];
    let (qgen_kuhn, _) = find("qgenKuhn", groupgen_sort, &|s| {
        record(s, &[("res", F::AnyElem), ("splits", F::AnyElem)]).map(|_| ())
    })?;
    let (qch_identity, _) = find("qchIdentity", chartref_sort, &nullary)?;
    let (qch_digest, _) = find("qchDigest", chartref_sort, &|s| {
        record(s, &[("sha256hex", F::Ground(Ground::Str))]).map(|_| ())
    })?;
    let (qrl_nil, _) = find("qrlNil", ratlist_sort, &nullary)?;
    let (qrl_cons, _) = find("qrlCons", ratlist_sort, &|s| {
        record(
            s,
            &[
                ("head", F::Ground(Ground::Q)),
                ("tail", F::Elem(ratlist_sort)),
            ],
        )
        .map(|_| ())
    })?;

    // --- the certificate box list + the box region atom ----------------
    let (qbx_nil, _) = find("qbxNil", boxlist_sort, &nullary)?;
    let (qbx_cons, _) = find("qbxCons", boxlist_sort, &|s| {
        record(
            s,
            &[("head", F::Elem(box_sort)), ("tail", F::Elem(boxlist_sort))],
        )
        .map(|_| ())
    })?;
    // (`qraBox` resolved up front — the box anchor.)

    // --- per-sort constructor rosters ----------------------------------
    let family_sorts = [
        box_sort,
        interval_sort,
        gridcx_sort,
        patchtree_sort,
        chartref_sort,
        genlist_sort,
        groupgen_sort,
        ratlist_sort,
        boxlist_sort,
        region_sort,
    ];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in family_sorts {
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

    Ok(CarillonVocab {
        box_nil,
        box_cons,
        mk_interval,
        qgc_mk,
        qpt_leaf,
        qpt_split,
        qgl_nil,
        qgl_cons,
        qgen_interval,
        qgen_kuhn,
        qch_identity,
        qch_digest,
        qrl_nil,
        qrl_cons,
        qbx_nil,
        qbx_cons,
        qra_box,
        ctors,
    })
}

// ---------------------------------------------------------------------
// Decoded data (pure — the core checks run on this, so tests hit the
// combinatorics directly)
// ---------------------------------------------------------------------

/// A closed box as per-axis `(lo, hi)` pairs, exact ℚ.
pub type QBox = Vec<(QQ, QQ)>;

/// One decoded mode: its name, closed domain box, and the reset-image
/// boxes of its spontaneous jumps (which land in-mode).
#[derive(Debug, Clone)]
pub struct ModeData {
    pub name: String,
    pub domain: QBox,
    pub jump_images: Vec<QBox>,
}

/// One decoded transition: source and destination mode names and the
/// reset-image box.
#[derive(Debug, Clone)]
pub struct TransitionData {
    pub src: String,
    pub dst: String,
    pub reset_image: QBox,
}

/// The R3/R4 pure checks' input shape. Since the event-3 refresh no
/// row decode constructs it (the manifest slice left the theory —
/// module doc): it is built directly by the unit tests and the frozen
/// cross-implementation corpus replay, holding the reference
/// semantics for the successor arm that re-wires the decode onto
/// certificate-stratum reset rows.
#[derive(Debug, Clone)]
pub struct ManifestData {
    pub modes: Vec<ModeData>,
    pub transitions: Vec<TransitionData>,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CarillonViolation {
    /// R3: the claimed `dbar` differs from the recomputed hull on the
    /// named axis (or in arity).
    DbarMismatch { axis: usize },
    /// R4: a reset image escapes its destination domain.
    ImageEscapes { what: &'static str, index: usize },
    /// R2: the grid wire is ill-formed (the morse `GridCxWire`
    /// precedent — decided certificate content).
    GridCxWire(crate::gridcx::WireViolation),
    /// R2: the `cells` Shape is not a strictly ascending set literal.
    CellsNotAscending { index: usize },
    /// R2: a named cell index is outside the complex's cell count.
    CellOutOfRange { index: u64, count: u64 },
    /// R2: the region escapes the complex's ambient box (no cell can
    /// cover the overhang).
    RegionEscapesDom { axis: usize },
    /// R2: a grid cell meeting the region is not named (the hole).
    CoverageHole { cell: u64 },
    /// R5: a cover box is inverted on the named axis (the reference
    /// returns `[]` for a provably-empty scope, never `[∅]`).
    EmptyCoverBox { part: usize, axis: usize },
    /// R5: a cover box escapes the intersection (exactness's ⊆ half).
    CoverBoxEscapes { part: usize, axis: usize },
    /// R5: a nonempty cover against a provably-empty intersection.
    CoverNotEmpty,
    /// R5: the cover's union misses part of the intersection.
    FloorCoverageHole,
}

impl std::fmt::Display for CarillonViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CarillonViolation::DbarMismatch { axis } => {
                write!(
                    f,
                    "dbar differs from the recomputed closed-domain hull at axis {axis}"
                )
            }
            CarillonViolation::ImageEscapes { what, index } => {
                write!(
                    f,
                    "{what} {index}: reset image escapes the destination domain"
                )
            }
            CarillonViolation::GridCxWire(w) => write!(f, "grid wire: {w}"),
            CarillonViolation::CellsNotAscending { index } => {
                write!(
                    f,
                    "cells[{index}] breaks strict ascent — not a canonical set literal"
                )
            }
            CarillonViolation::CellOutOfRange { index, count } => {
                write!(
                    f,
                    "cell index {index} outside the complex's {count} top cell(s)"
                )
            }
            CarillonViolation::RegionEscapesDom { axis } => {
                write!(f, "region escapes the ambient box at axis {axis}")
            }
            CarillonViolation::CoverageHole { cell } => {
                write!(
                    f,
                    "coverage hole: grid cell {cell} meets the region and is not named"
                )
            }
            CarillonViolation::EmptyCoverBox { part, axis } => {
                write!(f, "cover box {part} is inverted at axis {axis}")
            }
            CarillonViolation::CoverBoxEscapes { part, axis } => {
                write!(
                    f,
                    "cover box {part} escapes the intersection at axis {axis}"
                )
            }
            CarillonViolation::CoverNotEmpty => {
                write!(
                    f,
                    "the intersection is provably empty but the cover is nonempty"
                )
            }
            CarillonViolation::FloorCoverageHole => {
                write!(f, "the cover's union misses part of the intersection")
            }
        }
    }
}

// ---------------------------------------------------------------------
// The pure checks (exact ℚ, no division anywhere)
// ---------------------------------------------------------------------

fn le(a: &QQ, b: &QQ) -> bool {
    a.cmp_qq(b) != std::cmp::Ordering::Greater
}
fn lt(a: &QQ, b: &QQ) -> bool {
    a.cmp_qq(b) == std::cmp::Ordering::Less
}
fn qq_eq(a: &QQ, b: &QQ) -> bool {
    a.cmp_qq(b) == std::cmp::Ordering::Equal
}
fn qq_min(a: &QQ, b: &QQ) -> QQ {
    if le(a, b) {
        a.clone()
    } else {
        b.clone()
    }
}
fn qq_max(a: &QQ, b: &QQ) -> QQ {
    if le(a, b) {
        b.clone()
    } else {
        a.clone()
    }
}

/// The one-jump closed-domain hull: the mode's domain hulled per axis
/// with every image box. `Err` = an image's arity disagrees with the
/// domain's (the zip trap, refused — the reference's `zip` would
/// silently truncate it).
pub fn closed_domain_hull(domain: &QBox, images: &[QBox]) -> Result<QBox, String> {
    let mut hull = domain.clone();
    for (i, img) in images.iter().enumerate() {
        if img.len() != hull.len() {
            return Err(format!(
                "reset image {i} has arity {}, domain has {} — refusing \
                 (a truncated hull is not the declared relation)",
                img.len(),
                hull.len()
            ));
        }
        for (axis, (lo, hi)) in img.iter().enumerate() {
            hull[axis].0 = qq_min(&hull[axis].0, lo);
            hull[axis].1 = qq_max(&hull[axis].1, hi);
        }
    }
    Ok(hull)
}

/// Resolve a mode by name. `Err` = no such mode, or the reference is
/// ambiguous (two modes with the name) — refused, never picked.
fn mode_by_name<'a>(m: &'a ManifestData, name: &str) -> Result<&'a ModeData, String> {
    let mut found: Option<&ModeData> = None;
    for mode in &m.modes {
        if mode.name == name {
            if found.is_some() {
                return Err(format!(
                    "mode name `{name}` is declared twice — ambiguous reference, refusing"
                ));
            }
            found = Some(mode);
        }
    }
    found.ok_or_else(|| format!("`{name}` names no mode of the manifest — refusing"))
}

/// R3: `dbar` equals the recomputed closed-domain hull of `mode`
/// (its own spontaneous-jump images + every transition landing at it).
pub fn check_dbar_closure(
    dbar: &QBox,
    m: &ManifestData,
    mode_name: &str,
) -> Result<Result<(), CarillonViolation>, String> {
    let mode = mode_by_name(m, mode_name)?;
    let mut images: Vec<&QBox> = mode.jump_images.iter().collect();
    for t in &m.transitions {
        if t.dst == mode_name {
            images.push(&t.reset_image);
        }
    }
    let owned: Vec<QBox> = images.into_iter().cloned().collect();
    let hull = closed_domain_hull(&mode.domain, &owned)?;
    if dbar.len() != hull.len() {
        return Ok(Err(CarillonViolation::DbarMismatch { axis: 0 }));
    }
    for (axis, ((clo, chi), (hlo, hhi))) in dbar.iter().zip(&hull).enumerate() {
        if !qq_eq(clo, hlo) || !qq_eq(chi, hhi) {
            return Ok(Err(CarillonViolation::DbarMismatch { axis }));
        }
    }
    Ok(Ok(()))
}

/// R4: every reset image is contained in its destination mode's
/// domain, with the stop region empty (the declaration carries none;
/// strictly harder than the reference's stop-enlarged check — the
/// sound direction). 1-D as specced: any relevant box of arity ≠ 1
/// refuses (the n-D sweep is producer work). An inverted image (empty
/// — no landings) is vacuously contained, as in the reference.
pub fn check_gap_a(m: &ManifestData) -> Result<Result<(), CarillonViolation>, String> {
    let contained_1d = |img: &QBox, dom: &QBox, what: &'static str| -> Result<bool, String> {
        if img.len() != 1 || dom.len() != 1 {
            return Err(format!(
                "{what}: image arity {} / domain arity {} — the gap-A sweep is \
                 1-D as specced (n-D is producer work), refusing",
                img.len(),
                dom.len()
            ));
        }
        let (ilo, ihi) = &img[0];
        let (dlo, dhi) = &dom[0];
        if lt(ihi, ilo) {
            return Ok(true); // empty image: no landings.
        }
        Ok(le(dlo, ilo) && le(ihi, dhi))
    };
    for (mi, mode) in m.modes.iter().enumerate() {
        for (ji, img) in mode.jump_images.iter().enumerate() {
            if !contained_1d(img, &mode.domain, "spontaneous jump")? {
                return Ok(Err(CarillonViolation::ImageEscapes {
                    what: "spontaneous jump",
                    index: mi * 1000 + ji,
                }));
            }
        }
    }
    for (ti, t) in m.transitions.iter().enumerate() {
        // Both endpoints must resolve (dangling references refuse —
        // the reference's mode-major loop would silently skip a
        // dangling src; a checker must not).
        mode_by_name(m, &t.src)?;
        let dst = mode_by_name(m, &t.dst)?;
        if !contained_1d(&t.reset_image, &dst.domain, "transition")? {
            return Ok(Err(CarillonViolation::ImageEscapes {
                what: "transition",
                index: ti,
            }));
        }
    }
    Ok(Ok(()))
}

/// R2, the pure core: the named cells of a validated v0 grid cover the
/// region box. `cuts` are the per-axis FULL cut lists (endpoints
/// included — [`crate::gridcx::degenerate_cuts`]'s payload, converted
/// to exact ℚ); linearization is axis 0 fastest (convention 1, the
/// enumeration's pinned degenerate case).
pub fn check_cell_cover(
    cells: &[u64],
    cuts: &[Vec<QQ>],
    region: &QBox,
) -> Result<Result<(), CarillonViolation>, String> {
    // The cells literal is an ascending set (canonical Shape carrier).
    for (i, w) in cells.windows(2).enumerate() {
        if w[0] >= w[1] {
            return Ok(Err(CarillonViolation::CellsNotAscending { index: i + 1 }));
        }
    }
    if cells.len() > CELL_COVER_BUDGET {
        return Err(format!(
            "named-cell set beyond the enumeration budget ({CELL_COVER_BUDGET}) — refusing"
        ));
    }
    // Per-axis cell counts + total.
    let sizes: Vec<u64> = cuts.iter().map(|c| c.len() as u64 - 1).collect();
    let total: u64 = sizes
        .iter()
        .try_fold(1u64, |acc, n| acc.checked_mul(*n))
        .ok_or_else(|| "cell count overflows u64 — refusing".to_string())?;
    if let Some(&bad) = cells.iter().find(|&&c| c >= total) {
        return Ok(Err(CarillonViolation::CellOutOfRange {
            index: bad,
            count: total,
        }));
    }
    if region.len() != cuts.len() {
        return Err(format!(
            "region arity {} against a {}-axis complex — refusing",
            region.len(),
            cuts.len()
        ));
    }
    // Full-dimensional scope only (the reference's own named seam).
    for (axis, (lo, hi)) in region.iter().enumerate() {
        if !lt(lo, hi) {
            return Err(format!(
                "region is degenerate or inverted at axis {axis} — \
                 full-dimensional scope boxes only (named seam), refusing"
            ));
        }
    }
    // The region must sit inside the ambient box: cells cannot cover
    // an overhang.
    for (axis, (lo, hi)) in region.iter().enumerate() {
        let first = cuts[axis].first().expect("nonempty cut list");
        let last = cuts[axis].last().expect("nonempty cut list");
        if lt(lo, first) || lt(last, hi) {
            return Ok(Err(CarillonViolation::RegionEscapesDom { axis }));
        }
    }
    // Per-axis spanned index sets: cells whose open interior meets the
    // region (nondegenerate intersection — the reference's `clo < chi`
    // filter).
    let mut spanned: Vec<Vec<u64>> = Vec::with_capacity(cuts.len());
    for (axis, list) in cuts.iter().enumerate() {
        let (rlo, rhi) = &region[axis];
        let mut on_axis = Vec::new();
        for i in 0..list.len() - 1 {
            if lt(&list[i], rhi) && lt(rlo, &list[i + 1]) {
                on_axis.push(i as u64);
            }
        }
        spanned.push(on_axis);
    }
    // Budget-safe early exit: more spanned cells than named cells is a
    // hole outright (the named list is a strict set).
    let spanned_total = spanned
        .iter()
        .try_fold(1u64, |acc: u64, s| acc.checked_mul(s.len() as u64));
    match spanned_total {
        None => {
            // Overflow: certainly more spanned cells than any Shape
            // literal names.
            return Ok(Err(CarillonViolation::CoverageHole { cell: 0 }));
        }
        Some(n) if n > cells.len() as u64 => {
            // Find one concrete hole for the message: the first
            // spanned cell not named (cheap scan bounded by the named
            // set + 1).
        }
        _ => {}
    }
    let named: HashSet<u64> = cells.iter().copied().collect();
    // Odometer over the spanned product, axis 0 fastest linearization:
    // idx = c_0 + n_0 · (c_1 + n_1 · (…)).
    let n_axes = spanned.len();
    let mut pos = vec![0usize; n_axes];
    let mut checked: u64 = 0;
    loop {
        let mut idx: u64 = 0;
        for k in (0..n_axes).rev() {
            idx = idx * sizes[k] + spanned[k][pos[k]];
        }
        if !named.contains(&idx) {
            return Ok(Err(CarillonViolation::CoverageHole { cell: idx }));
        }
        checked += 1;
        if checked > cells.len() as u64 {
            // Unreachable given the early-exit arithmetic above, kept
            // as a belt: more distinct spanned cells than named ones.
            return Ok(Err(CarillonViolation::CoverageHole { cell: idx }));
        }
        let mut k = 0;
        loop {
            if k == n_axes {
                return Ok(Ok(()));
            }
            pos[k] += 1;
            if pos[k] < spanned[k].len() {
                break;
            }
            pos[k] = 0;
            k += 1;
        }
    }
}

/// R5, the pure core: `cover` is an exact box cover of `bx ∩ dbar`.
pub fn check_lowbound_boxes(
    cover: &[QBox],
    dbar: &QBox,
    bx: &QBox,
) -> Result<Result<(), CarillonViolation>, String> {
    if bx.len() != dbar.len() {
        return Err(format!(
            "region-atom box arity {} against dbar arity {} — refusing",
            bx.len(),
            dbar.len()
        ));
    }
    let n = dbar.len();
    // The target: T = bx ∩ dbar, per axis.
    let mut target: QBox = Vec::with_capacity(n);
    let mut empty = false;
    for axis in 0..n {
        let lo = qq_max(&bx[axis].0, &dbar[axis].0);
        let hi = qq_min(&bx[axis].1, &dbar[axis].1);
        if lt(&hi, &lo) {
            empty = true;
        }
        target.push((lo, hi));
    }
    if empty {
        return Ok(if cover.is_empty() {
            Ok(())
        } else {
            Err(CarillonViolation::CoverNotEmpty)
        });
    }
    // Containment: every cover box non-inverted and inside T.
    for (pi, part) in cover.iter().enumerate() {
        if part.len() != n {
            return Err(format!(
                "cover box {pi} has arity {}, the intersection has {} — refusing",
                part.len(),
                n
            ));
        }
        for (axis, (lo, hi)) in part.iter().enumerate() {
            if lt(hi, lo) {
                return Ok(Err(CarillonViolation::EmptyCoverBox { part: pi, axis }));
            }
            if lt(lo, &target[axis].0) || lt(&target[axis].1, hi) {
                return Ok(Err(CarillonViolation::CoverBoxEscapes { part: pi, axis }));
            }
        }
    }
    // Coverage: cut T's nondegenerate axes at every cover-box endpoint
    // and demand each sub-cell lie inside some cover box. Degenerate
    // axes of T are already pinned pointwise by containment. Closed
    // boxes: nondegenerate sub-cells decide coverage (a shared face
    // lies in the closure of an adjacent covered cell).
    let nd: Vec<usize> = (0..n).filter(|&k| lt(&target[k].0, &target[k].1)).collect();
    if nd.is_empty() {
        // T is a point; a contained cover box IS that point.
        return Ok(if cover.is_empty() {
            Err(CarillonViolation::FloorCoverageHole)
        } else {
            Ok(())
        });
    }
    if cover.is_empty() {
        return Ok(Err(CarillonViolation::FloorCoverageHole));
    }
    let mut axis_cuts: Vec<Vec<QQ>> = Vec::with_capacity(nd.len());
    let mut cell_total: u64 = 1;
    for &k in &nd {
        let (tlo, thi) = &target[k];
        let mut pts: Vec<QQ> = vec![tlo.clone(), thi.clone()];
        for part in cover {
            for v in [&part[k].0, &part[k].1] {
                if lt(tlo, v) && lt(v, thi) {
                    pts.push(v.clone());
                }
            }
        }
        pts.sort_by(|a, b| a.cmp_qq(b));
        pts.dedup_by(|a, b| qq_eq(a, b));
        cell_total = cell_total
            .checked_mul(pts.len() as u64 - 1)
            .filter(|t| *t <= FLOOR_COVER_BUDGET)
            .ok_or_else(|| {
                format!(
                    "floor-cover sub-cell grid beyond the budget \
                     ({FLOOR_COVER_BUDGET}) — refusing"
                )
            })?;
        axis_cuts.push(pts);
    }
    // Odometer over the sub-cells.
    let mut pos = vec![0usize; nd.len()];
    loop {
        let covered = cover.iter().any(|part| {
            nd.iter().enumerate().all(|(j, &k)| {
                let (clo, chi) = (&axis_cuts[j][pos[j]], &axis_cuts[j][pos[j] + 1]);
                le(&part[k].0, clo) && le(chi, &part[k].1)
            })
        });
        if !covered {
            return Ok(Err(CarillonViolation::FloorCoverageHole));
        }
        let mut j = 0;
        loop {
            if j == nd.len() {
                return Ok(Ok(()));
            }
            pos[j] += 1;
            if pos[j] + 1 < axis_cuts[j].len() {
                break;
            }
            pos[j] = 0;
            j += 1;
        }
    }
}

// ---------------------------------------------------------------------
// Row decoding
// ---------------------------------------------------------------------

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a CarillonVocab,
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
        let roster = self.v.ctors.get(&sort).expect("family sorts rostered");
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

    fn qq(&self, index: usize, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a canonical Q literal — malformed rows"),
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

    fn walk_list<T>(
        &mut self,
        index: usize,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        mut on_cons: impl FnMut(&mut Self, &CtorRow) -> Result<(T, u32), EvalError>,
    ) -> Result<Vec<T>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head_elem;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} recurs along its own list tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            let row = self.sole(index, sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} is constructed by a fun outside the \
                         expected nil/cons pair — malformed rows"
                    ),
                ));
            }
            let (item, tail) = on_cons(self, row)?;
            out.push(item);
            cur = tail;
        }
    }

    /// Decode a Qtsl `Box` element into per-axis `(lo, hi)` exact-ℚ
    /// pairs.
    fn qbox(&mut self, index: usize, box_elem: u32) -> Result<QBox, EvalError> {
        let box_sort = self.sort_of(self.v.box_cons);
        let interval_sort = self.sort_of(self.v.mk_interval);
        let (v_mk, v_nil, v_cons) = (self.v.mk_interval, self.v.box_nil, self.v.box_cons);
        let iv_elems = self.walk_list(index, box_sort, box_elem, v_nil, v_cons, |d, row| {
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, index, "boxCons row arity mismatch".into()));
            };
            let head = d.elem(index, head)?;
            let tail = d.elem(index, tail)?;
            Ok((head, tail))
        })?;
        let mut out = Vec::with_capacity(iv_elems.len());
        for iv_elem in iv_elems {
            let iv = self.sole(index, interval_sort, iv_elem)?;
            if iv.fun != v_mk {
                return Err(ctx_err(
                    self.name,
                    index,
                    "interval element is not constructed by mkInterval — malformed rows".into(),
                ));
            }
            let [hi, lo] = iv.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    index,
                    "mkInterval row arity mismatch".into(),
                ));
            };
            out.push((
                self.qq(index, lo, "mkInterval/lo")?,
                self.qq(index, hi, "mkInterval/hi")?,
            ));
        }
        Ok(out)
    }

    fn sort_of(&self, chid: Chid) -> Chid {
        *self
            .v
            .ctors
            .iter()
            .find(|(_, roster)| roster.contains_key(&chid))
            .map(|(s, _)| s)
            .expect("family constructors rostered under their codomains")
    }

    /// Decode a `QGridCx` element into [`crate::gridcx::GridCx`]
    /// (structure-only refusals; profile and wire adjudication are the
    /// caller's). Iterative post-order, as in the morse decode:
    /// hash-consed subtree sharing decodes per occurrence; a cyclic
    /// "tree" exhausts the shared budget and refuses.
    fn gridcx(&mut self, index: usize, cx_elem: u32) -> Result<crate::gridcx::GridCx, EvalError> {
        use crate::gridcx::{ChartRef, GridCx, GroupGen, PatchLeaf, PatchTree};
        use geolog_envelope::Literal;

        let gridcx_sort = self.sort_of(self.v.qgc_mk);
        let patchtree_sort = self.sort_of(self.v.qpt_leaf);
        let chartref_sort = self.sort_of(self.v.qch_identity);
        let genlist_sort = self.sort_of(self.v.qgl_cons);
        let groupgen_sort = self.sort_of(self.v.qgen_interval);
        let ratlist_sort = self.sort_of(self.v.qrl_cons);

        // A raw Q literal (the gridcx types carry `Literal`, not QQ).
        let q_lit = |d: &Decoder<'_>, val: &Value, what: &str| -> Result<Literal, EvalError> {
            if let Value::Lit(l) = val {
                if QQ::from_q_literal(l).is_some() {
                    return Ok(l.clone());
                }
            }
            Err(ctx_err(
                d.name,
                index,
                format!("`{what}` is not a canonical Q literal — malformed rows"),
            ))
        };
        let nat = |d: &Decoder<'_>, val: &Value, what: &str| -> Result<u64, EvalError> {
            if let Value::Lit(l) = val {
                if let LiteralView::Nat(n) = l.view() {
                    return Ok(n);
                }
            }
            Err(ctx_err(
                d.name,
                index,
                format!("`{what}` is not a Nat literal — malformed rows"),
            ))
        };
        let shape = |d: &Decoder<'_>, val: &Value, what: &str| -> Result<Vec<u64>, EvalError> {
            if let Value::Lit(l) = val {
                if let LiteralView::Shape(s) = l.view() {
                    return Ok(s.iter().collect());
                }
            }
            Err(ctx_err(
                d.name,
                index,
                format!("`{what}` is not a Shape literal — malformed rows"),
            ))
        };

        let mk = self.sole(index, gridcx_sort, cx_elem)?;
        if mk.fun != self.v.qgc_mk {
            return Err(ctx_err(
                self.name,
                index,
                "grid-complex element is not constructed by qgcMk — malformed rows".into(),
            ));
        }
        let [dom_val, tree_val] = mk.args.as_slice() else {
            return Err(ctx_err(self.name, index, "qgcMk row arity mismatch".into()));
        };
        let dom_elem = self.elem(index, dom_val)?;
        let tree_root = self.elem(index, tree_val)?;

        // The ambient box, as raw literals (the gridcx contract).
        let box_sort = self.sort_of(self.v.box_cons);
        let interval_sort = self.sort_of(self.v.mk_interval);
        let (v_mk, v_nil, v_cons) = (self.v.mk_interval, self.v.box_nil, self.v.box_cons);
        let iv_elems = self.walk_list(index, box_sort, dom_elem, v_nil, v_cons, |d, row| {
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, index, "boxCons row arity mismatch".into()));
            };
            Ok((d.elem(index, head)?, d.elem(index, tail)?))
        })?;
        let mut dom = Vec::with_capacity(iv_elems.len());
        for iv_elem in iv_elems {
            let iv = self.sole(index, interval_sort, iv_elem)?;
            if iv.fun != v_mk {
                return Err(ctx_err(
                    self.name,
                    index,
                    "box interval element is not constructed by mkInterval — malformed rows".into(),
                ));
            }
            let [hi, lo] = iv.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    index,
                    "mkInterval row arity mismatch".into(),
                ));
            };
            dom.push((
                q_lit(self, lo, "mkInterval/lo")?,
                q_lit(self, hi, "mkInterval/hi")?,
            ));
        }

        // The patch tree, post-order with an explicit stack.
        enum Frame {
            Visit(u32),
            BuildSplit { axis: u64, cut: Literal },
        }
        let mut work = vec![Frame::Visit(tree_root)];
        let mut built: Vec<PatchTree> = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                Frame::Visit(elem) => {
                    let row = self.sole(index, patchtree_sort, elem)?.clone();
                    if row.fun == self.v.qpt_leaf {
                        let [chart, gens, part] = row.args.as_slice() else {
                            return Err(ctx_err(
                                self.name,
                                index,
                                "qptLeaf row arity mismatch".into(),
                            ));
                        };
                        let part = shape(self, part, "qptLeaf/part")?;
                        let chart_elem = self.elem(index, chart)?;
                        let chart_row = self.sole(index, chartref_sort, chart_elem)?;
                        let chart = if chart_row.fun == self.v.qch_identity {
                            ChartRef::Identity
                        } else if chart_row.fun == self.v.qch_digest {
                            let [sha] = chart_row.args.as_slice() else {
                                return Err(ctx_err(
                                    self.name,
                                    index,
                                    "qchDigest row arity mismatch".into(),
                                ));
                            };
                            ChartRef::Digest {
                                sha256hex: self.str_lit(index, sha, "qchDigest/sha256hex")?,
                            }
                        } else {
                            return Err(ctx_err(
                                self.name,
                                index,
                                "chart element constructed outside the QChartRef roster — \
                                 malformed rows"
                                    .into(),
                            ));
                        };
                        let gens_elem = self.elem(index, gens)?;
                        let (v_gl_nil, v_gl_cons) = (self.v.qgl_nil, self.v.qgl_cons);
                        let gen_elems = self.walk_list(
                            index,
                            genlist_sort,
                            gens_elem,
                            v_gl_nil,
                            v_gl_cons,
                            |d, row| {
                                let [gen, tail] = row.args.as_slice() else {
                                    return Err(ctx_err(
                                        d.name,
                                        index,
                                        "qglCons row arity mismatch".into(),
                                    ));
                                };
                                Ok((d.elem(index, gen)?, d.elem(index, tail)?))
                            },
                        )?;
                        let mut gens = Vec::with_capacity(gen_elems.len());
                        for gen_elem in gen_elems {
                            let gen_row = self.sole(index, groupgen_sort, gen_elem)?;
                            if gen_row.fun == self.v.qgen_interval {
                                let [cuts_val] = gen_row.args.as_slice() else {
                                    return Err(ctx_err(
                                        self.name,
                                        index,
                                        "qgenInterval row arity mismatch".into(),
                                    ));
                                };
                                let cuts_elem = self.elem(index, cuts_val)?;
                                let (v_rl_nil, v_rl_cons) = (self.v.qrl_nil, self.v.qrl_cons);
                                let cuts = self.walk_list(
                                    index,
                                    ratlist_sort,
                                    cuts_elem,
                                    v_rl_nil,
                                    v_rl_cons,
                                    |d, row| {
                                        let [head, tail] = row.args.as_slice() else {
                                            return Err(ctx_err(
                                                d.name,
                                                index,
                                                "qrlCons row arity mismatch".into(),
                                            ));
                                        };
                                        let q = q_lit(d, head, "qrlCons/head")?;
                                        Ok((q, d.elem(index, tail)?))
                                    },
                                )?;
                                gens.push(GroupGen::Interval { cuts });
                            } else if gen_row.fun == self.v.qgen_kuhn {
                                // Opaque at this layer (the v0 profile
                                // refuses before any Kuhn cell is read).
                                gens.push(GroupGen::Kuhn);
                            } else {
                                return Err(ctx_err(
                                    self.name,
                                    index,
                                    "generator element constructed outside the QGroupGen \
                                     roster — malformed rows"
                                        .into(),
                                ));
                            }
                        }
                        built.push(PatchTree::Leaf(PatchLeaf { part, gens, chart }));
                    } else if row.fun == self.v.qpt_split {
                        let [axis, cut, hi, lo] = row.args.as_slice() else {
                            return Err(ctx_err(
                                self.name,
                                index,
                                "qptSplit row arity mismatch".into(),
                            ));
                        };
                        let axis = nat(self, axis, "qptSplit/axis")?;
                        let cut = q_lit(self, cut, "qptSplit/cut")?;
                        let lo = self.elem(index, lo)?;
                        let hi = self.elem(index, hi)?;
                        work.push(Frame::BuildSplit { axis, cut });
                        work.push(Frame::Visit(hi));
                        work.push(Frame::Visit(lo));
                    } else {
                        return Err(ctx_err(
                            self.name,
                            index,
                            "patch-tree element constructed outside the QPatchTree roster — \
                             malformed rows"
                                .into(),
                        ));
                    }
                }
                Frame::BuildSplit { axis, cut } => {
                    let hi = built.pop().expect("post-order: hi built");
                    let lo = built.pop().expect("post-order: lo built");
                    built.push(PatchTree::Split {
                        axis,
                        cut,
                        lo: Box::new(lo),
                        hi: Box::new(hi),
                    });
                }
            }
        }
        let tree = built.pop().expect("post-order: root built");
        Ok(GridCx { dom, tree })
    }
}

// ---------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------

fn shape_arg(name: &str, index: usize, val: &Value) -> Result<Vec<u64>, EvalError> {
    if let Value::Lit(l) = val {
        if let LiteralView::Shape(s) = l.view() {
            return Ok(s.iter().collect());
        }
    }
    Err(ctx_err(name, index, "expected a Shape literal cell".into()))
}

/// Evaluate a carillon-family relation over the row context.
pub(crate) fn eval_carillon(
    name: &str,
    v: &CarillonVocab,
    kind: CarillonKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let verdict = match kind {
        CarillonKind::CellCover => {
            // [cells: Shape, cx: QGridCx, region: Box]
            let cells = shape_arg(name, 0, args[0])?;
            let cx_elem = elem_local(name, 1, args[1], rows)?;
            let region_elem = elem_local(name, 2, args[2], rows)?;
            let cx = d.gridcx(1, cx_elem)?;
            let region = d.qbox(2, region_elem)?;

            // v0 profile first (capability — refusals), then the wire
            // (well-formedness — decided false), the admission order.
            let leaf = crate::gridcx::v0_leaf(&cx.tree).map_err(|p| {
                ctx_err(name, 1, format!("grid complex outside the v0 profile: {p}"))
            })?;
            if let Err(w) = crate::gridcx::validate_leaf(cx.dom.len(), leaf) {
                let _ = CarillonViolation::GridCxWire(w);
                return Ok(false);
            }
            let cut_lits = crate::gridcx::degenerate_cuts(&cx.dom, leaf);
            let mut cuts: Vec<Vec<QQ>> = Vec::with_capacity(cut_lits.len());
            for list in &cut_lits {
                let mut axis = Vec::with_capacity(list.len());
                for l in list {
                    axis.push(QQ::from_q_literal(l).ok_or_else(|| {
                        ctx_err(name, 1, "non-Q cut literal in the grid wire".into())
                    })?);
                }
                // The derived full list must be strictly increasing
                // (interior-only cuts + a proper ambient interval);
                // a violation is decided grid content.
                for w in axis.windows(2) {
                    if !lt(&w[0], &w[1]) {
                        return Ok(false);
                    }
                }
                cuts.push(axis);
            }
            check_cell_cover(&cells, &cuts, &region).map_err(|why| ctx_err(name, 0, why))?
        }
        CarillonKind::DbarClosure => {
            // [dbar: Box, m: Manifest, mode: Mode] — the event-3
            // declaration stands (mode cited as an entity), but the
            // recompute's required content left the row grain: reset
            // images ride kernel cites (`tr_kernel`/`KernelCite`) and
            // certificate-stratum reset roles (`prReset`), opaque in
            // single-body context. REFUSING, never deciding — the
            // R8-style loud deferral (the syswire flatten arm's
            // posture); when the reset-row staging lands in the
            // theory, this arm grows the recompute against the
            // entity-cited mode via the pure core (`check_dbar_closure`).
            return Err(ctx_err(
                name,
                0,
                "the one-jump closed-domain recompute needs the mode's reset \
                 images, which the event-3 theory carries as kernel cites and \
                 certificate-stratum reset roles — not relationally exposed in \
                 single-body context; refusing, not deciding (the R8-style \
                 loud deferral: when reset-row staging lands in the theory, \
                 this arm grows the recompute)"
                    .into(),
            ));
        }
        CarillonKind::GapA => {
            // [m: Manifest] — same retired stratum as the R3 arm,
            // same deferral, same growth point (`check_gap_a`).
            return Err(ctx_err(
                name,
                0,
                "the reset-image containment sweep needs the manifest's reset \
                 images, which the event-3 theory carries as kernel cites and \
                 certificate-stratum reset roles — not relationally exposed in \
                 single-body context; refusing, not deciding (the R8-style \
                 loud deferral: when reset-row staging lands in the theory, \
                 this arm grows the recompute)"
                    .into(),
            ));
        }
        CarillonKind::FloorBoxes => {
            // [cover: QBoxList, dbar: Box, region: QRegionAtom]
            let cover_elem = elem_local(name, 0, args[0], rows)?;
            let dbar_elem = elem_local(name, 1, args[1], rows)?;
            let region_elem = elem_local(name, 2, args[2], rows)?;

            let boxlist_sort = d.sort_of(d.v.qbx_cons);
            let (v_bx_nil, v_bx_cons) = (d.v.qbx_nil, d.v.qbx_cons);
            let box_elems = d.walk_list(
                0,
                boxlist_sort,
                cover_elem,
                v_bx_nil,
                v_bx_cons,
                |d, row| {
                    let [head, tail] = row.args.as_slice() else {
                        return Err(ctx_err(d.name, 0, "qbxCons row arity mismatch".into()));
                    };
                    Ok((d.elem(0, head)?, d.elem(0, tail)?))
                },
            )?;
            let mut cover = Vec::with_capacity(box_elems.len());
            for be in box_elems {
                cover.push(d.qbox(0, be)?);
            }
            let dbar = d.qbox(1, dbar_elem)?;

            // The region atom: qraBox resolves; every other
            // constructor is the non-box seam — refused by name.
            let region_sort = {
                // qraBox's codomain sort (rostered).
                d.sort_of(d.v.qra_box)
            };
            let atom = d.sole(2, region_sort, region_elem)?;
            if atom.fun != d.v.qra_box {
                return Err(ctx_err(
                    name,
                    2,
                    "region atom is not a qraBox — sublevel/affine atoms are the \
                     RCert/eps-rounded/non-linear seam (not box-resolvable), refusing"
                        .into(),
                ));
            }
            let [box_val] = atom.args.as_slice() else {
                return Err(ctx_err(name, 2, "qraBox row arity mismatch".into()));
            };
            let bx_elem = d.elem(2, box_val)?;
            let bx = d.qbox(2, bx_elem)?;

            check_lowbound_boxes(&cover, &dbar, &bx).map_err(|why| ctx_err(name, 0, why))?
        }
    };
    Ok(verdict.is_ok())
}

// ---------------------------------------------------------------------
// Unit tests on the pure core
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }
    fn iv(lo: i64, hi: i64) -> (QQ, QQ) {
        (q(lo, 1), q(hi, 1))
    }

    // --------------------------------------------------- R3: the hull

    #[test]
    fn hull_of_no_images_is_the_domain() {
        let dom = vec![iv(0, 1), iv(-1, 1)];
        assert_eq!(closed_domain_hull(&dom, &[]).unwrap(), dom);
    }

    #[test]
    fn hull_widens_per_axis() {
        let dom = vec![iv(0, 1)];
        let hull = closed_domain_hull(&dom, &[vec![iv(-2, 0)], vec![iv(1, 3)]]).unwrap();
        assert_eq!(hull, vec![iv(-2, 3)]);
    }

    #[test]
    fn hull_refuses_the_zip_trap() {
        // A 2-axis image against a 1-axis domain: the python zip would
        // silently truncate; here it refuses.
        let dom = vec![iv(0, 1)];
        assert!(closed_domain_hull(&dom, &[vec![iv(0, 1), iv(0, 1)]]).is_err());
    }

    fn manifest_1d() -> ManifestData {
        ManifestData {
            modes: vec![
                ModeData {
                    name: "on".into(),
                    domain: vec![iv(0, 2)],
                    jump_images: vec![vec![iv(0, 1)]],
                },
                ModeData {
                    name: "off".into(),
                    domain: vec![iv(1, 3)],
                    jump_images: vec![],
                },
            ],
            transitions: vec![TransitionData {
                src: "on".into(),
                dst: "off".into(),
                reset_image: vec![iv(1, 2)],
            }],
        }
    }

    #[test]
    fn dbar_holds_on_the_exact_hull() {
        let m = manifest_1d();
        // "off" is hulled with the transition image [1,2] ⊆ [1,3]:
        // hull = [1,3].
        assert_eq!(
            check_dbar_closure(&vec![iv(1, 3)], &m, "off").unwrap(),
            Ok(())
        );
        // "on" hulls with its own jump image [0,1] ⊆ [0,2]: [0,2].
        assert_eq!(
            check_dbar_closure(&vec![iv(0, 2)], &m, "on").unwrap(),
            Ok(())
        );
    }

    #[test]
    fn dbar_mismatch_is_decided_false() {
        let m = manifest_1d();
        assert!(matches!(
            check_dbar_closure(&vec![iv(0, 3)], &m, "off").unwrap(),
            Err(CarillonViolation::DbarMismatch { .. })
        ));
        // Wrong arity claims are mismatches too.
        assert!(matches!(
            check_dbar_closure(&vec![iv(1, 3), iv(0, 1)], &m, "off").unwrap(),
            Err(CarillonViolation::DbarMismatch { .. })
        ));
    }

    #[test]
    fn dbar_hull_widens_beyond_the_domain() {
        let mut m = manifest_1d();
        m.transitions[0].reset_image = vec![iv(2, 5)]; // escapes [1,3]
        assert_eq!(
            check_dbar_closure(&vec![iv(1, 5)], &m, "off").unwrap(),
            Ok(())
        );
        assert!(check_dbar_closure(&vec![iv(1, 3)], &m, "off")
            .unwrap()
            .is_err());
    }

    #[test]
    fn dbar_unknown_or_duplicate_mode_refuses() {
        let m = manifest_1d();
        assert!(check_dbar_closure(&vec![iv(0, 1)], &m, "nowhere").is_err());
        let mut dup = manifest_1d();
        dup.modes.push(ModeData {
            name: "on".into(),
            domain: vec![iv(0, 1)],
            jump_images: vec![],
        });
        assert!(check_dbar_closure(&vec![iv(0, 2)], &dup, "on").is_err());
    }

    // --------------------------------------------------- R4: gap-A

    #[test]
    fn gap_a_holds_when_images_land_inside() {
        assert_eq!(check_gap_a(&manifest_1d()).unwrap(), Ok(()));
    }

    #[test]
    fn gap_a_boundary_landing_holds() {
        let mut m = manifest_1d();
        m.transitions[0].reset_image = vec![iv(1, 3)]; // exactly D_off
        assert_eq!(check_gap_a(&m).unwrap(), Ok(()));
    }

    #[test]
    fn gap_a_escaping_transition_fails() {
        let mut m = manifest_1d();
        m.transitions[0].reset_image = vec![iv(2, 4)]; // 4 > 3
        assert!(matches!(
            check_gap_a(&m).unwrap(),
            Err(CarillonViolation::ImageEscapes {
                what: "transition",
                ..
            })
        ));
    }

    #[test]
    fn gap_a_escaping_jump_fails() {
        let mut m = manifest_1d();
        m.modes[0].jump_images[0] = vec![iv(-1, 1)]; // -1 < 0
        assert!(matches!(
            check_gap_a(&m).unwrap(),
            Err(CarillonViolation::ImageEscapes {
                what: "spontaneous jump",
                ..
            })
        ));
    }

    #[test]
    fn gap_a_empty_image_is_vacuous() {
        let mut m = manifest_1d();
        m.modes[0].jump_images[0] = vec![(q(5, 1), q(4, 1))]; // inverted
        assert_eq!(check_gap_a(&m).unwrap(), Ok(()));
    }

    #[test]
    fn gap_a_dangling_reference_refuses() {
        let mut m = manifest_1d();
        m.transitions[0].dst = "nowhere".into();
        assert!(check_gap_a(&m).is_err());
        let mut m2 = manifest_1d();
        m2.transitions[0].src = "nowhere".into();
        assert!(check_gap_a(&m2).is_err());
    }

    #[test]
    fn gap_a_refuses_nd() {
        let m = ManifestData {
            modes: vec![ModeData {
                name: "m".into(),
                domain: vec![iv(0, 1), iv(0, 1)],
                jump_images: vec![vec![iv(0, 1), iv(0, 1)]],
            }],
            transitions: vec![],
        };
        assert!(check_gap_a(&m).is_err());
    }

    // --------------------------------------------------- R2: cell cover

    /// A 2-D grid over [0,4]²: axis 0 cut at {1,2,3} (4 cells), axis 1
    /// cut at {2} (2 cells). Cell idx = c0 + 4·c1 (axis 0 fastest).
    fn grid_2d() -> Vec<Vec<QQ>> {
        vec![
            vec![q(0, 1), q(1, 1), q(2, 1), q(3, 1), q(4, 1)],
            vec![q(0, 1), q(2, 1), q(4, 1)],
        ]
    }

    #[test]
    fn cell_cover_exact_span_holds() {
        // Region [1,3]×[0,2]: axis-0 cells {1,2}, axis-1 cell {0} →
        // indices {1, 2}.
        assert_eq!(
            check_cell_cover(&[1, 2], &grid_2d(), &vec![iv(1, 3), iv(0, 2)]).unwrap(),
            Ok(())
        );
    }

    #[test]
    fn cell_cover_unaligned_region_needs_the_meeting_cells() {
        // Region [1/2, 3/2]×[1,3] meets axis-0 cells {0,1} and axis-1
        // cells {0,1} → {0,1,4,5}.
        let r = vec![(q(1, 2), q(3, 2)), iv(1, 3)];
        assert_eq!(
            check_cell_cover(&[0, 1, 4, 5], &grid_2d(), &r).unwrap(),
            Ok(())
        );
        assert!(matches!(
            check_cell_cover(&[0, 1, 4], &grid_2d(), &r).unwrap(),
            Err(CarillonViolation::CoverageHole { cell: 5 })
        ));
    }

    #[test]
    fn cell_cover_extra_cells_are_harmless() {
        // Naming cells beyond the region is coverage, not equality.
        assert_eq!(
            check_cell_cover(&[0, 1, 2, 3], &grid_2d(), &vec![iv(1, 3), iv(0, 2)]).unwrap(),
            Ok(())
        );
    }

    #[test]
    fn cell_cover_hole_is_decided_false() {
        assert!(matches!(
            check_cell_cover(&[1], &grid_2d(), &vec![iv(1, 3), iv(0, 2)]).unwrap(),
            Err(CarillonViolation::CoverageHole { cell: 2 })
        ));
    }

    #[test]
    fn cell_cover_boundary_touch_is_not_membership() {
        // Region [1,2]×[0,2] touches cells 0 and 2 only at faces —
        // cell 1 alone covers it.
        assert_eq!(
            check_cell_cover(&[1], &grid_2d(), &vec![iv(1, 2), iv(0, 2)]).unwrap(),
            Ok(())
        );
    }

    #[test]
    fn cell_cover_region_escaping_dom_fails() {
        assert!(matches!(
            check_cell_cover(
                &[0, 1, 2, 3, 4, 5, 6, 7],
                &grid_2d(),
                &vec![iv(1, 5), iv(0, 2)]
            )
            .unwrap(),
            Err(CarillonViolation::RegionEscapesDom { axis: 0 })
        ));
    }

    #[test]
    fn cell_cover_out_of_range_and_descent_fail() {
        let r = vec![iv(1, 3), iv(0, 2)];
        assert!(matches!(
            check_cell_cover(&[1, 2, 8], &grid_2d(), &r).unwrap(),
            Err(CarillonViolation::CellOutOfRange { index: 8, count: 8 })
        ));
        assert!(matches!(
            check_cell_cover(&[2, 1], &grid_2d(), &r).unwrap(),
            Err(CarillonViolation::CellsNotAscending { .. })
        ));
        assert!(matches!(
            check_cell_cover(&[1, 1, 2], &grid_2d(), &r).unwrap(),
            Err(CarillonViolation::CellsNotAscending { .. })
        ));
    }

    #[test]
    fn cell_cover_degenerate_region_refuses() {
        assert!(check_cell_cover(&[1], &grid_2d(), &vec![iv(1, 1), iv(0, 2)]).is_err());
        assert!(check_cell_cover(&[1], &grid_2d(), &vec![iv(2, 1), iv(0, 2)]).is_err());
    }

    #[test]
    fn cell_cover_1d_matches_the_v0_sweep() {
        // The 1-D reference path: pieces over [0,1] cut at 1/4.
        let cuts = vec![vec![q(0, 1), q(1, 4), q(1, 1)]];
        assert_eq!(
            check_cell_cover(&[0, 1], &cuts, &vec![iv(0, 1)]).unwrap(),
            Ok(())
        );
        assert!(matches!(
            check_cell_cover(&[1], &cuts, &vec![iv(0, 1)]).unwrap(),
            Err(CarillonViolation::CoverageHole { cell: 0 })
        ));
        // A region inside one cell needs only that cell.
        assert_eq!(
            check_cell_cover(&[1], &cuts, &vec![(q(1, 2), q(3, 4))]).unwrap(),
            Ok(())
        );
    }

    // --------------------------------------------------- R5: floor boxes

    #[test]
    fn floor_exact_single_box_holds() {
        // T = [0,2]∩[1,3] = [1,2]; cover = [T].
        assert_eq!(
            check_lowbound_boxes(&[vec![iv(1, 2)]], &vec![iv(1, 3)], &vec![iv(0, 2)]).unwrap(),
            Ok(())
        );
    }

    #[test]
    fn floor_tiling_holds_and_hole_fails() {
        // T = [0,4]; tiles [0,1],[1,3],[3,4].
        let t = |a: i64, b: i64| vec![iv(a, b)];
        assert_eq!(
            check_lowbound_boxes(
                &[t(0, 1), t(1, 3), t(3, 4)],
                &vec![iv(0, 4)],
                &vec![iv(0, 4)]
            )
            .unwrap(),
            Ok(())
        );
        assert!(matches!(
            check_lowbound_boxes(&[t(0, 1), t(3, 4)], &vec![iv(0, 4)], &vec![iv(0, 4)]).unwrap(),
            Err(CarillonViolation::FloorCoverageHole)
        ));
    }

    #[test]
    fn floor_overlapping_tiles_still_exact() {
        let t = |a: i64, b: i64| vec![iv(a, b)];
        assert_eq!(
            check_lowbound_boxes(&[t(0, 3), t(2, 4)], &vec![iv(0, 4)], &vec![iv(0, 4)]).unwrap(),
            Ok(())
        );
    }

    #[test]
    fn floor_escaping_box_fails() {
        assert!(matches!(
            check_lowbound_boxes(&[vec![iv(0, 2)]], &vec![iv(1, 3)], &vec![iv(0, 2)]).unwrap(),
            Err(CarillonViolation::CoverBoxEscapes { part: 0, axis: 0 })
        ));
    }

    #[test]
    fn floor_empty_intersection_demands_empty_cover() {
        assert_eq!(
            check_lowbound_boxes(&[], &vec![iv(3, 4)], &vec![iv(0, 2)]).unwrap(),
            Ok(())
        );
        assert!(matches!(
            check_lowbound_boxes(&[vec![iv(3, 3)]], &vec![iv(3, 4)], &vec![iv(0, 2)]).unwrap(),
            Err(CarillonViolation::CoverNotEmpty)
        ));
    }

    #[test]
    fn floor_nonempty_target_with_empty_cover_fails() {
        assert!(matches!(
            check_lowbound_boxes(&[], &vec![iv(0, 2)], &vec![iv(1, 3)]).unwrap(),
            Err(CarillonViolation::FloorCoverageHole)
        ));
    }

    #[test]
    fn floor_degenerate_intersection_is_exactly_coverable() {
        // T = [0,2]∩[2,3] = the point slab [2,2].
        assert_eq!(
            check_lowbound_boxes(&[vec![iv(2, 2)]], &vec![iv(2, 3)], &vec![iv(0, 2)]).unwrap(),
            Ok(())
        );
        assert!(check_lowbound_boxes(&[], &vec![iv(2, 3)], &vec![iv(0, 2)])
            .unwrap()
            .is_err());
    }

    #[test]
    fn floor_degenerate_axis_in_2d() {
        // T = [1,2]×[2,2]: covered by one degenerate tile, or by two
        // tiles split at 3/2 on axis 0.
        let dbar = vec![iv(0, 2), iv(2, 4)];
        let bx = vec![iv(1, 3), iv(0, 2)];
        assert_eq!(
            check_lowbound_boxes(&[vec![iv(1, 2), iv(2, 2)]], &dbar, &bx).unwrap(),
            Ok(())
        );
        assert_eq!(
            check_lowbound_boxes(
                &[
                    vec![(q(1, 1), q(3, 2)), iv(2, 2)],
                    vec![(q(3, 2), q(2, 1)), iv(2, 2)],
                ],
                &dbar,
                &bx
            )
            .unwrap(),
            Ok(())
        );
        // A hole in the middle.
        assert!(matches!(
            check_lowbound_boxes(
                &[
                    vec![(q(1, 1), q(5, 4)), iv(2, 2)],
                    vec![(q(3, 2), q(2, 1)), iv(2, 2)],
                ],
                &dbar,
                &bx
            )
            .unwrap(),
            Err(CarillonViolation::FloorCoverageHole)
        ));
    }

    #[test]
    fn floor_2d_l_shape_tiling() {
        // T = [0,2]²; an L of three unit tiles misses [1,2]²; adding
        // it closes the cover.
        let t = |a: (i64, i64), b: (i64, i64)| vec![iv(a.0, a.1), iv(b.0, b.1)];
        let l3 = [t((0, 1), (0, 1)), t((1, 2), (0, 1)), t((0, 1), (1, 2))];
        let dbar = vec![iv(0, 2), iv(0, 2)];
        let bx = dbar.clone();
        assert!(matches!(
            check_lowbound_boxes(&l3, &dbar, &bx).unwrap(),
            Err(CarillonViolation::FloorCoverageHole)
        ));
        let mut full = l3.to_vec();
        full.push(t((1, 2), (1, 2)));
        assert_eq!(check_lowbound_boxes(&full, &dbar, &bx).unwrap(), Ok(()));
    }

    #[test]
    fn floor_inverted_cover_box_fails() {
        assert!(matches!(
            check_lowbound_boxes(
                &[vec![(q(2, 1), q(1, 1))]],
                &vec![iv(0, 4)],
                &vec![iv(0, 4)]
            )
            .unwrap(),
            Err(CarillonViolation::EmptyCoverBox { part: 0, axis: 0 })
        ));
    }
}
