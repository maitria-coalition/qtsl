//! The block-lattice family: `blockLatticeWF` and
//! `productLatticeChecks` — the certificate-family (attracting-block
//! lattice) side-conditions, evaluated over rows.
//!
//! Two relations:
//!
//! - **`blockLatticeWF [bl: BlockLattice]`** — the record
//!   well-formedness obligation: axis/block index families are exactly
//!   `{0..n-1}` (bijective presence); at least two strictly increasing
//!   rational gridlines per axis; each stored block's cell list
//!   sorted, nonempty, PROPER, and in range; each block's `nFacets`
//!   equal to the canonical boundary-facet count of its cell set, with
//!   the facet-proof family present and aligned to the canonical
//!   order. Also carried from the same obligation's wire statement:
//!   at least one stored block, pairwise-distinct blocks, per-axis
//!   wires pairwise distinct, and every drift term drawn from the
//!   scalar polynomial-tree fragment (constants, wire variables,
//!   addition, multiplication, subtraction — nothing else).
//!
//! - **`productLatticeChecks [p: PProductLattice]`** — the product
//!   rule's checker obligations: facet discharge (every facet-proof
//!   slot of all three lattices concludes the required facet-sign
//!   sequent — discharge by citation, since a factor's proof may fill
//!   a composite slot unchanged under the absent-atom licence), drift
//!   confinement (each factor's drift terms mention only that
//!   factor's own axis wires), wire disjointness (the two factors
//!   share no axis wire), and product correctness (the conclusion's
//!   lattice IS the product of left and right: axes concatenated,
//!   drift terms equal structurally, gridlines verbatim, blocks the
//!   extended pairwise products in the pinned enumeration order).
//!   Record well-formedness is re-run on all three lattices first,
//!   mirroring the wire checker, which runs it on all three records
//!   at the point of consumption.
//!
//! Semantic authority: the soundness warrant `sound_productLattice`
//! with `prodBlocks_confined` (`lean/qtsl/Qtsl/ProductLattice.lean` —
//! the `CertifiedBlockLattice` structure, the `prodBlock`/`citeFacet`
//! product construction, and validity transport across wire-disjoint
//! extension), together with the certificate wire format's family
//! section, whose obligations this module recomputes at row grain.
//!
//! # Pinned conventions
//!
//! 1. **Cell linearization: row-major, axis 0 slowest** (C order) —
//!    `idx = (…(c_0 · n_1 + c_1) · n_2 + …) + c_{d−1}` over the
//!    per-axis cell counts `n_k = nGridlines_k − 1`. Deliberately NOT
//!    the Morse-readout kit's convention (axis 0 fastest,
//!    [`crate::morse`]): the two lattices are distinct sorts with
//!    distinct pinned wire forms, and each evaluator follows its own
//!    format's linearization. Do not unify by accident.
//! 2. **Canonical facet order**: boundary cell-facets
//!    `(cell, axis, direction)` — neighbouring cell inside the grid
//!    but outside the block — sorted by (cell row-major index, axis,
//!    direction with lower before upper). Grid-boundary faces owe
//!    nothing (the arena is the full grid box, its forward invariance
//!    declared rather than certified).
//! 3. **Facet-sign sequent** for a facet of pinned axis `i` at plane
//!    value `v` (the lower gridline for a lower facet, the upper for
//!    an upper facet): post is a single comparison atom whose left
//!    side is the axis drift with every occurrence of the axis wire
//!    substituted by `v` (pure tree substitution, no simplification,
//!    compared structurally) and whose right side is a constant
//!    margin — `>=` with a strictly positive margin for a lower facet
//!    (the block sits on the positive side), `<=` with a strictly
//!    negative margin for an upper facet. The pre is an AND-tree of
//!    `FInRegion(TVar(w), simplex, S)` atoms over the record's axis
//!    wires, at most one per wire and at least one in total: an atom
//!    on a free axis must be exactly the facet's cell interval on
//!    that axis (absence is licensed — the transport-and-weaken
//!    warrant, which is what lets one factor node discharge every
//!    composite slot it is cited from), and an atom on the pinned
//!    axis must be that axis's full arena interval.
//! 4. **Interval atoms** denote through the simplicial vocabulary: a
//!    one-dimensional complex (`SimpC/amb_dim = 1`), a simplex whose
//!    sealed membership mask has exactly two vertices, vertex
//!    coordinates equal (as a set) to the interval's endpoints, the
//!    extension set empty and anchored on the atom's own simplex.
//!    Masks are read under the sealed-rows discipline of
//!    [`crate::blmask`], including the refusal on out-of-range
//!    membership rows.
//! 5. **Product enumeration**: composite axes are left's then
//!    right's; composite stored blocks are the extended pairwise
//!    products `{b1 × b2 : b1 ∈ left ∪ {D1}, b2 ∈ right ∪ {D2}}`
//!    minus the implicit top `D1 × D2`, enumerated lexicographically
//!    with each factor's stored blocks first (in index order) and its
//!    arena last. A product block's cell set is
//!    `{i1 · N2 + i2 : i1 ∈ b1, i2 ∈ b2}` with `N2` the right
//!    factor's total cell count — already sorted by construction.
//!
//! # Adjudicated boundaries — deliberately not decided here
//!
//! - **Axis-wire scalarity** (the wire format checks each axis wire
//!   against the scalar rational tensor type via the symbol table) is
//!   typing-stratum territory at row grain — `Wire/type` rows may
//!   legitimately live outside the certificate body, and the theory's
//!   own well-formedness obligations carry typing. The same split
//!   sent the wedge geometry Lean-side for the Morse readout.
//! - **The two-axis reader profile** (wire readers reject more than
//!   two axes until the general-arity facet machinery lands) is a
//!   wire READER gate, not part of this relation's frozen statement;
//!   the row evaluator implements the declaration's own bound
//!   (budget refusals aside, any positive axis count).
//! - **Proof validity**: a facet slot's proof is checked for the
//!   SHAPE of its conclusion only; that the proof tree itself is
//!   valid is the proof calculus's global obligation, not this
//!   relation's.
//!
//! Verdict discipline (the crate's): a decided violation is
//! `Ok(false)`; unresolvable or ambiguous elements, external
//! references where a same-body element is required, malformed rows,
//! out-of-range family indices (the Index-sort semantics: such rows
//! correspond to no model state), and exhausted budgets REFUSE with a
//! reason, never guessing. The bijective-presence charges on the
//! DECLARED axis/block index families are decided content (`false` on
//! gaps, duplicates, or out-of-range indices) — they are what the
//! relation is FOR — while the per-axis gridline family and the
//! per-block cell/facet families refuse on missing or duplicated
//! entries (an incompletely constructed family is undecidable, not
//! decidedly ill-formed).

use crate::atomic::elem_local;
use crate::error::EvalError;
use crate::formrows::{find_field, find_sort, BlVocab, FormCtor, TermCtor, Walk};
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{BTreeMap, BTreeSet, HashSet};

const F_WF: &[(&str, &str)] = &[("bl", "BlockLattice")];
const F_PRODUCT: &[(&str, &str)] = &[("p", "PProductLattice")];

/// The block-lattice family's rows of the claimed roster (concatenated
/// at registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    ("blockLatticeWF", F_WF, RelKind::Lattice { product: false }),
    (
        "productLatticeChecks",
        F_PRODUCT,
        RelKind::Lattice { product: true },
    ),
];

/// Budgets: refusal beyond, never divergence.
pub const LATTICE_MAX_AXES: u64 = 16;
pub const LATTICE_MAX_GRIDLINES: u64 = 4096;
pub const LATTICE_MAX_CELLS: u64 = 1 << 16;
pub const LATTICE_MAX_BLOCKS: u64 = 512;
/// Cap on the total number of cell entries handled across one
/// evaluation's decoded and recomputed block families.
pub const LATTICE_MAX_TOTAL_CELLS: u64 = 1 << 20;

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// The block-lattice family's resolved vocabulary: the lattice, axis,
/// block, judgment, and product-node field identities plus the
/// simplicial interval chain, name-selected once at construction and
/// shape-verified (names select, shapes verify, identities pin).
#[derive(Debug, Clone)]
pub struct LatticeVocab {
    // BlockLattice fields.
    bl_n_axes: Chid,
    bl_n_blocks: Chid,
    // BLAxis fields.
    axis_lattice: Chid,
    axis_index: Chid,
    axis_wire: Chid,
    axis_drift: Chid,
    axis_n_gridlines: Chid,
    axis_gridline: Chid,
    // FamBlock fields.
    block_lattice: Chid,
    block_index: Chid,
    block_n_cells: Chid,
    block_cell: Chid,
    block_n_facets: Chid,
    block_facet_proof: Chid,
    // FamJudgment / PProductLattice fields.
    famj_lattice: Chid,
    prod_concludes: Chid,
    prod_left: Chid,
    prod_right: Chid,
    prod_flows_only: Chid,
    // The simplicial interval chain (the facet-sequent pre atoms).
    simplex_complex: Chid,
    simplex_contains: Chid,
    simpc_n_vertices: Chid,
    simpc_amb_dim: Chid,
    simpc_coord: Chid,
    ext_simplex: Chid,
    ext_contains: Chid,
}

/// Build the block-lattice vocabulary over the declared indices.
/// `Err` → the family is not claimed (declared-but-unbound,
/// safe-fail).
pub fn build_lattice_vocab(indices: &[&TheoryIndex]) -> Result<LatticeVocab, String> {
    let bl_sort = find_sort(indices, "BlockLattice")?;
    let axis_sort = find_sort(indices, "BLAxis")?;
    let block_sort = find_sort(indices, "FamBlock")?;
    let famj_sort = find_sort(indices, "FamJudgment")?;
    let prod_sort = find_sort(indices, "PProductLattice")?;
    let simplex_sort = find_sort(indices, "Simplex")?;
    let ext_sort = find_sort(indices, "ExtensionSet")?;
    let simpc_sort = find_sort(indices, "SimpC")?;

    // A unary field with a verified codomain.
    let field = |name: &str, dom: Chid, cod: SortKey| -> Result<Chid, String> {
        let c = find_field(indices, name, dom)?;
        for index in indices {
            if let Some(d) = index.fun_by_chid(c) {
                if d.relational
                    || d.codomain != Some(cod)
                    || d.domain != DomainSig::Unary(SortKey::Elem(dom))
                {
                    return Err(format!(
                        "`{name}` does not have the expected field shape \
                         (unary fun on the expected sort with the expected codomain)"
                    ));
                }
                return Ok(c);
            }
        }
        Err(format!(
            "`{name}` resolved but is not indexed — malformed sweep"
        ))
    };
    // An indexed family fun: a two-field record over the subject sort
    // and a Nat index, with a verified codomain.
    let ifield = |name: &str, subj: Chid, cod: SortKey| -> Result<Chid, String> {
        let c = find_field(indices, name, subj)?;
        for index in indices {
            if let Some(d) = index.fun_by_chid(c) {
                let ok = !d.relational
                    && d.codomain == Some(cod)
                    && match &d.domain {
                        DomainSig::Record(fs) => {
                            fs.len() == 2
                                && fs
                                    .iter()
                                    .any(|(_, s)| matches!(s, SortKey::Elem(x) if *x == subj))
                                && fs.iter().any(|(_, s)| *s == SortKey::Ground(Ground::Nat))
                        }
                        _ => false,
                    };
                if !ok {
                    return Err(format!(
                        "`{name}` does not have the expected indexed-family shape \
                         ([subject, Nat] with the expected codomain)"
                    ));
                }
                return Ok(c);
            }
        }
        Err(format!(
            "`{name}` resolved but is not indexed — malformed sweep"
        ))
    };
    let membership = |name: &str, subj: Chid| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = d.relational
                && d.codomain.is_none()
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [(_, SortKey::Elem(s0)), (_, SortKey::Ground(Ground::Nat))]
                            if *s0 == subj
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected membership-relation shape"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    // The coordinate table: [complex: SimpC, v: Nat, j: Nat] -> Q
    // (three fields, bytewise argument order complex < j < v).
    let coord = {
        let c = find_field(indices, "SimpC/coord", simpc_sort)?;
        let mut ok = false;
        for index in indices {
            if let Some(d) = index.fun_by_chid(c) {
                ok = !d.relational
                    && d.codomain == Some(SortKey::Ground(Ground::Q))
                    && matches!(&d.domain, DomainSig::Record(fs) if fs.len() == 3);
            }
        }
        if !ok {
            return Err("`SimpC/coord` does not have the expected coordinate-table shape".into());
        }
        c
    };

    let term_sort = find_sort(indices, "Term")?;
    let wire_sort = find_sort(indices, "Wire")?;
    let proof_sort = find_sort(indices, "Proof")?;
    let e = SortKey::Elem;
    let nat = SortKey::Ground(Ground::Nat);
    let q = SortKey::Ground(Ground::Q);

    Ok(LatticeVocab {
        bl_n_axes: field("BlockLattice/nAxes", bl_sort, nat)?,
        bl_n_blocks: field("BlockLattice/nBlocks", bl_sort, nat)?,
        axis_lattice: field("BLAxis/lattice", axis_sort, e(bl_sort))?,
        axis_index: field("BLAxis/index", axis_sort, nat)?,
        axis_wire: field("BLAxis/wire", axis_sort, e(wire_sort))?,
        axis_drift: field("BLAxis/drift", axis_sort, e(term_sort))?,
        axis_n_gridlines: field("BLAxis/nGridlines", axis_sort, nat)?,
        axis_gridline: ifield("BLAxis/gridline", axis_sort, q)?,
        block_lattice: field("FamBlock/lattice", block_sort, e(bl_sort))?,
        block_index: field("FamBlock/index", block_sort, nat)?,
        block_n_cells: field("FamBlock/nCells", block_sort, nat)?,
        block_cell: ifield("FamBlock/cell", block_sort, nat)?,
        block_n_facets: field("FamBlock/nFacets", block_sort, nat)?,
        block_facet_proof: ifield("FamBlock/facetProof", block_sort, e(proof_sort))?,
        famj_lattice: field("FamJudgment/lattice", famj_sort, e(bl_sort))?,
        prod_concludes: field("PProductLattice/concludes", prod_sort, e(famj_sort))?,
        prod_left: field("PProductLattice/left", prod_sort, e(bl_sort))?,
        prod_right: field("PProductLattice/right", prod_sort, e(bl_sort))?,
        prod_flows_only: field("PProductLattice/flowsOnly", prod_sort, nat)?,
        simplex_complex: field("Simplex/complex", simplex_sort, e(simpc_sort))?,
        simplex_contains: membership("Simplex/contains", simplex_sort)?,
        simpc_n_vertices: field("SimpC/n_vertices", simpc_sort, nat)?,
        simpc_amb_dim: field("SimpC/amb_dim", simpc_sort, nat)?,
        simpc_coord: coord,
        ext_simplex: field("ExtensionSet/simplex", ext_sort, e(simplex_sort))?,
        ext_contains: membership("ExtensionSet/contains", ext_sort)?,
    })
}

// ---------------------------------------------------------------------
// Decoded data + named violations
// ---------------------------------------------------------------------

/// One decoded axis: wire and drift as same-body elements, gridlines
/// as exact rationals, and the drift's free wires (collected during
/// the fragment walk).
struct AxisData {
    wire: u32,
    drift: u32,
    gridlines: Vec<QQ>,
    drift_wires: BTreeSet<u32>,
}

/// One decoded stored block: strictly increasing cell indices and the
/// facet-proof family (present, in canonical slot order; values kept
/// as raw cells so well-formedness needs no proof structure).
struct BlockData {
    cells: Vec<u64>,
    facet_proofs: Vec<Value>,
}

/// One decoded, well-formed lattice.
struct LatticeData {
    axes: Vec<AxisData>,
    blocks: Vec<BlockData>,
    grid_counts: Vec<u64>,
    n_cells: u64,
}

/// A decided violation — `Ok(false)` territory, named for the module's
/// own diagnostics (the payloads feed `Debug` rendering only).
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
enum LatticeViolation {
    ZeroAxes,
    ZeroBlocks,
    AxisIndexFamily,
    BlockIndexFamily,
    GridlineCount { axis: usize },
    GridlineOrder { axis: usize },
    DriftFragment { axis: usize },
    DuplicateAxisWire,
    BlockCells { block: usize },
    DuplicateBlock { block: usize },
    FacetCount { block: usize },
    FacetPost { block: usize, facet: usize },
    FacetPre { block: usize, facet: usize },
    DriftConfinement { axis: usize },
    SharedWire,
    ProductAxes,
    ProductBlocks,
}

type Decided<T> = Result<T, LatticeViolation>;

// ---------------------------------------------------------------------
// Cell geometry (row-major, axis 0 slowest)
// ---------------------------------------------------------------------

/// One canonical boundary facet: the block cell, the axis, and the
/// direction (`upper = false` is the lower face — before the upper in
/// the canonical order).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Facet {
    cell: u64,
    axis: usize,
    upper: bool,
}

/// Decompose a row-major cell index (axis 0 slowest) into per-axis
/// coordinates.
fn coords_of(grid_counts: &[u64], cell: u64) -> Vec<u64> {
    let d = grid_counts.len();
    let mut coords = vec![0u64; d];
    let mut rem = cell;
    for i in (0..d).rev() {
        coords[i] = rem % grid_counts[i];
        rem /= grid_counts[i];
    }
    coords
}

/// Re-linearize per-axis coordinates (axis 0 slowest).
fn index_of(grid_counts: &[u64], coords: &[u64]) -> u64 {
    let mut idx = 0u64;
    for (i, &n) in grid_counts.iter().enumerate() {
        idx = idx * n + coords[i];
    }
    idx
}

/// The canonical boundary-facet enumeration of a block: facets whose
/// neighbouring cell lies inside the grid but outside the block,
/// sorted by (cell, axis, lower before upper). `cells` is strictly
/// increasing, so the enumeration is sorted by construction.
fn canonical_facets(grid_counts: &[u64], cells: &[u64]) -> Vec<Facet> {
    let in_block = |idx: u64| cells.binary_search(&idx).is_ok();
    let mut out = Vec::new();
    for &cell in cells {
        let coords = coords_of(grid_counts, cell);
        for (axis, &n) in grid_counts.iter().enumerate() {
            for upper in [false, true] {
                let c = coords[axis];
                let neighbour = if upper {
                    if c + 1 >= n {
                        continue; // grid-boundary face: owes nothing
                    }
                    c + 1
                } else {
                    if c == 0 {
                        continue; // grid-boundary face
                    }
                    c - 1
                };
                let mut ncoords = coords.clone();
                ncoords[axis] = neighbour;
                if !in_block(index_of(grid_counts, &ncoords)) {
                    out.push(Facet { cell, axis, upper });
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------------
// Row decoding
// ---------------------------------------------------------------------

/// Every subject element carrying a `pointer` row whose value is the
/// given lattice element — the discovery direction for the entity
/// idiom (axes and blocks point AT their lattice). Deduplicated,
/// refusing on malformed rows.
fn members_of(
    w: &Walk<'_>,
    rows: &CertRows,
    index: usize,
    lattice: u32,
    pointer: Chid,
    what: &str,
) -> Result<Vec<u32>, EvalError> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for row in rows.producers(lattice).iter().filter(|r| r.fun == pointer) {
        if row.args.len() != 1 {
            return Err(w.refuse(
                index,
                format!(
                    "malformed `{what}` row: expected 1 argument, got {}",
                    row.args.len()
                ),
            ));
        }
        let m = w.local(index, &row.args[0])?;
        if seen.insert(m) {
            out.push(m);
        }
    }
    Ok(out)
}

/// Arrange member elements into declared-index order by their Nat
/// index field. Gaps, duplicates, and out-of-range indices are DECIDED
/// violations (the relation's bijective-presence charge); a member
/// with a missing or ambiguous index row refuses through the walk.
fn indexed_members(
    w: &mut Walk<'_>,
    index: usize,
    members: &[u32],
    index_fun: Chid,
    declared: u64,
    what: &str,
    violation: LatticeViolation,
) -> Result<Decided<Vec<u32>>, EvalError> {
    let n = usize::try_from(declared).expect("budgeted");
    if members.len() != n {
        return Ok(Err(violation));
    }
    let mut slots: Vec<Option<u32>> = vec![None; n];
    for &m in members {
        let i = w.field_nat(index, m, index_fun, what)?;
        let Ok(iu) = usize::try_from(i) else {
            return Ok(Err(violation));
        };
        if iu >= n || slots[iu].is_some() {
            return Ok(Err(violation));
        }
        slots[iu] = Some(m);
    }
    // members.len() == n and no slot was filled twice, so every slot
    // is full.
    Ok(Ok(slots.into_iter().map(|s| s.expect("counted")).collect()))
}

/// Collect the dense indexed family `fun(subject, k) = value` for
/// `k in 0..n`, with the subject in the FIRST argument position and
/// the Nat index in the second (the bytewise field order of
/// `FamBlock/cell` and `FamBlock/facetProof`). Missing, duplicated,
/// or out-of-range indices refuse (the Index-sort semantics: an
/// incomplete family is undecidable, an out-of-range row corresponds
/// to no model state).
fn subject_indexed_family<'a>(
    w: &Walk<'a>,
    rows: &'a CertRows,
    index: usize,
    subject: u32,
    fun: Chid,
    n: u64,
    what: &str,
) -> Result<Vec<&'a Value>, EvalError> {
    let n_usize = usize::try_from(n)
        .ok()
        .filter(|n| (*n as u64) <= LATTICE_MAX_CELLS)
        .ok_or_else(|| w.refuse(index, format!("`{what}` family size {n} out of budget")))?;
    let mut out: Vec<Option<&Value>> = vec![None; n_usize];
    for row in rows.arg_rows(subject) {
        if row.fun != fun {
            continue;
        }
        let [s_cell, k_cell] = row.args.as_slice() else {
            return Err(w.refuse(
                index,
                format!("`{what}` row has {} args (expected 2)", row.args.len()),
            ));
        };
        if w.local(index, s_cell)? != subject {
            continue;
        }
        let Value::Lit(kl) = k_cell else {
            return Err(w.refuse(index, format!("`{what}` index cell is not a literal")));
        };
        let LiteralView::Nat(k) = kl.view() else {
            return Err(w.refuse(index, format!("`{what}` index cell is not a Nat")));
        };
        let Ok(ku) = usize::try_from(k) else {
            return Err(w.refuse(index, format!("`{what}` index {k} out of range")));
        };
        if ku >= n_usize {
            return Err(w.refuse(
                index,
                format!("`{what}` index {k} at or past the declared count {n}"),
            ));
        }
        let slot = &mut out[ku];
        match slot {
            None => *slot = Some(&row.value),
            Some(v) if **v == row.value => {}
            Some(_) => {
                return Err(w.refuse(
                    index,
                    format!("`{what}` index {k} carries conflicting rows — never picking"),
                ))
            }
        }
    }
    out.into_iter()
        .enumerate()
        .map(|(k, v)| v.ok_or_else(|| w.refuse(index, format!("`{what}` index {k} missing"))))
        .collect()
}

/// The gridline family `BLAxis/gridline(x, g) = q` for `g in 0..n`
/// (index FIRST in bytewise order), as exact rationals.
fn gridline_family(
    w: &Walk<'_>,
    rows: &CertRows,
    index: usize,
    axis: u32,
    fun: Chid,
    n: u64,
) -> Result<Vec<QQ>, EvalError> {
    let n_usize = usize::try_from(n)
        .ok()
        .filter(|n| (*n as u64) <= LATTICE_MAX_GRIDLINES)
        .ok_or_else(|| w.refuse(index, format!("gridline family size {n} out of budget")))?;
    let mut out: Vec<Option<QQ>> = vec![None; n_usize];
    for row in rows.arg_rows(axis) {
        if row.fun != fun {
            continue;
        }
        let [g_cell, x_cell] = row.args.as_slice() else {
            return Err(w.refuse(
                index,
                format!("gridline row has {} args (expected 2)", row.args.len()),
            ));
        };
        if w.local(index, x_cell)? != axis {
            continue;
        }
        let Value::Lit(gl) = g_cell else {
            return Err(w.refuse(index, "gridline index cell is not a literal".into()));
        };
        let LiteralView::Nat(g) = gl.view() else {
            return Err(w.refuse(index, "gridline index cell is not a Nat".into()));
        };
        let Ok(gu) = usize::try_from(g) else {
            return Err(w.refuse(index, format!("gridline index {g} out of range")));
        };
        if gu >= n_usize {
            return Err(w.refuse(
                index,
                format!("gridline index {g} at or past the declared count {n}"),
            ));
        }
        let Value::Lit(ql) = &row.value else {
            return Err(w.refuse(index, "gridline value is not a literal".into()));
        };
        let Some(q) = QQ::from_q_literal(ql) else {
            return Err(w.refuse(index, "gridline value is not a Q literal".into()));
        };
        let slot = &mut out[gu];
        match slot {
            None => *slot = Some(q),
            Some(prev) if *prev == q => {}
            Some(_) => {
                return Err(w.refuse(
                    index,
                    format!("gridline index {g} carries conflicting rows — never picking"),
                ))
            }
        }
    }
    out.into_iter()
        .enumerate()
        .map(|(g, v)| v.ok_or_else(|| w.refuse(index, format!("gridline index {g} missing"))))
        .collect()
}

/// Walk a drift term: enforce the scalar polynomial-tree fragment
/// (constants, wire variables, addition, multiplication, subtraction)
/// and collect the free wires. `Ok(Err(_))` = fragment violation.
fn drift_fragment_wires(
    w: &mut Walk<'_>,
    index: usize,
    drift: u32,
    axis: usize,
) -> Result<Decided<BTreeSet<u32>>, EvalError> {
    let mut wires = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut stack = vec![drift];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let (k, row) = w.term_ctor_row(index, t)?;
        let row = row.clone();
        match k {
            TermCtor::Const => {}
            TermCtor::Var => {
                wires.insert(w.local(index, &row.args[0])?);
            }
            TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                stack.push(w.local(index, &row.args[0])?);
                stack.push(w.local(index, &row.args[1])?);
            }
            TermCtor::Neg | TermCtor::Idx | TermCtor::Hole => {
                return Ok(Err(LatticeViolation::DriftFragment { axis }));
            }
        }
    }
    Ok(Ok(wires))
}

/// Decode one lattice element and run the full record well-formedness
/// obligation on it. `Err` = refusal; `Ok(Err(_))` = decided
/// violation; `Ok(Ok(_))` = a well-formed decoded lattice.
fn decode_lattice(
    w: &mut Walk<'_>,
    rows: &CertRows,
    v: &LatticeVocab,
    index: usize,
    bl: u32,
) -> Result<Decided<LatticeData>, EvalError> {
    let n_axes = w.field_nat(index, bl, v.bl_n_axes, "BlockLattice/nAxes")?;
    let n_blocks = w.field_nat(index, bl, v.bl_n_blocks, "BlockLattice/nBlocks")?;
    if n_axes > LATTICE_MAX_AXES {
        return Err(w.refuse(index, format!("{n_axes} axes exceed the axis budget")));
    }
    if n_blocks > LATTICE_MAX_BLOCKS {
        return Err(w.refuse(index, format!("{n_blocks} blocks exceed the block budget")));
    }
    if n_axes == 0 {
        return Ok(Err(LatticeViolation::ZeroAxes));
    }
    if n_blocks == 0 {
        return Ok(Err(LatticeViolation::ZeroBlocks));
    }

    // Axes: discovery, bijective index presence, per-axis data.
    let axis_members = members_of(w, rows, index, bl, v.axis_lattice, "BLAxis/lattice")?;
    let axis_elems = match indexed_members(
        w,
        index,
        &axis_members,
        v.axis_index,
        n_axes,
        "BLAxis/index",
        LatticeViolation::AxisIndexFamily,
    )? {
        Ok(a) => a,
        Err(viol) => return Ok(Err(viol)),
    };
    let mut axes = Vec::with_capacity(axis_elems.len());
    for (i, &axis) in axis_elems.iter().enumerate() {
        let wire = w.field_elem(index, axis, v.axis_wire, "BLAxis/wire")?;
        let drift = w.field_elem(index, axis, v.axis_drift, "BLAxis/drift")?;
        let n_gridlines = w.field_nat(index, axis, v.axis_n_gridlines, "BLAxis/nGridlines")?;
        if n_gridlines > LATTICE_MAX_GRIDLINES {
            return Err(w.refuse(
                index,
                format!("{n_gridlines} gridlines exceed the gridline budget"),
            ));
        }
        if n_gridlines < 2 {
            return Ok(Err(LatticeViolation::GridlineCount { axis: i }));
        }
        let gridlines = gridline_family(w, rows, index, axis, v.axis_gridline, n_gridlines)?;
        if gridlines
            .windows(2)
            .any(|p| p[0].cmp_qq(&p[1]) != std::cmp::Ordering::Less)
        {
            return Ok(Err(LatticeViolation::GridlineOrder { axis: i }));
        }
        let drift_wires = match drift_fragment_wires(w, index, drift, i)? {
            Ok(ws) => ws,
            Err(viol) => return Ok(Err(viol)),
        };
        axes.push(AxisData {
            wire,
            drift,
            gridlines,
            drift_wires,
        });
    }
    let mut wire_set = BTreeSet::new();
    for a in &axes {
        if !wire_set.insert(a.wire) {
            return Ok(Err(LatticeViolation::DuplicateAxisWire));
        }
    }
    let grid_counts: Vec<u64> = axes.iter().map(|a| a.gridlines.len() as u64 - 1).collect();
    let mut n_cells = 1u64;
    for &n in &grid_counts {
        n_cells = n_cells
            .checked_mul(n)
            .filter(|&t| t <= LATTICE_MAX_CELLS)
            .ok_or_else(|| w.refuse(index, "grid exceeds the cell budget".into()))?;
    }

    // Blocks: discovery, bijective index presence, per-block data.
    let block_members = members_of(w, rows, index, bl, v.block_lattice, "FamBlock/lattice")?;
    let block_elems = match indexed_members(
        w,
        index,
        &block_members,
        v.block_index,
        n_blocks,
        "FamBlock/index",
        LatticeViolation::BlockIndexFamily,
    )? {
        Ok(b) => b,
        Err(viol) => return Ok(Err(viol)),
    };
    let mut blocks: Vec<BlockData> = Vec::with_capacity(block_elems.len());
    let mut total_cells = 0u64;
    for (bi, &block) in block_elems.iter().enumerate() {
        let n_cells_b = w.field_nat(index, block, v.block_n_cells, "FamBlock/nCells")?;
        if n_cells_b == 0 {
            return Ok(Err(LatticeViolation::BlockCells { block: bi }));
        }
        total_cells = total_cells.saturating_add(n_cells_b);
        if total_cells > LATTICE_MAX_TOTAL_CELLS {
            return Err(w.refuse(index, "block families exceed the total cell budget".into()));
        }
        let cell_vals = subject_indexed_family(
            w,
            rows,
            index,
            block,
            v.block_cell,
            n_cells_b,
            "FamBlock/cell",
        )?;
        let mut cells = Vec::with_capacity(cell_vals.len());
        for val in cell_vals {
            let Value::Lit(l) = val else {
                return Err(w.refuse(index, "`FamBlock/cell` value is not a literal".into()));
            };
            let LiteralView::Nat(c) = l.view() else {
                return Err(w.refuse(index, "`FamBlock/cell` value is not a Nat".into()));
            };
            cells.push(c);
        }
        // Sorted (strictly), in range, PROPER.
        if cells.windows(2).any(|p| p[0] >= p[1])
            || *cells.last().expect("nonempty") >= n_cells
            || cells.len() as u64 == n_cells
        {
            return Ok(Err(LatticeViolation::BlockCells { block: bi }));
        }
        if blocks.iter().any(|b| b.cells == cells) {
            return Ok(Err(LatticeViolation::DuplicateBlock { block: bi }));
        }
        // Facet slots: the declared count must equal the canonical
        // boundary-facet count, and the proof family must be present
        // (its values are checked for shape by the product relation).
        let n_facets = w.field_nat(index, block, v.block_n_facets, "FamBlock/nFacets")?;
        let canonical = canonical_facets(&grid_counts, &cells);
        if n_facets != canonical.len() as u64 {
            return Ok(Err(LatticeViolation::FacetCount { block: bi }));
        }
        let proof_vals = subject_indexed_family(
            w,
            rows,
            index,
            block,
            v.block_facet_proof,
            n_facets,
            "FamBlock/facetProof",
        )?;
        let mut facet_proofs = Vec::with_capacity(proof_vals.len());
        for val in proof_vals {
            if !matches!(val, Value::Ref(_)) {
                return Err(w.refuse(
                    index,
                    "`FamBlock/facetProof` value is not an element ref".into(),
                ));
            }
            facet_proofs.push(val.clone());
        }
        blocks.push(BlockData {
            cells,
            facet_proofs,
        });
    }

    Ok(Ok(LatticeData {
        axes,
        blocks,
        grid_counts,
        n_cells,
    }))
}

// ---------------------------------------------------------------------
// Facet discharge (the sequent-shape obligation)
// ---------------------------------------------------------------------

/// Structural equality of `got` against `drift` with every occurrence
/// of `pinned_wire` substituted by the constant `pinned_value` — pure
/// tree substitution, no simplification. The drift side has already
/// passed the fragment gate, so only constants, wire variables, and
/// the three binary operations occur on it.
fn subst_eq(
    w: &mut Walk<'_>,
    index: usize,
    got: u32,
    drift: u32,
    pinned_wire: u32,
    pinned_value: &QQ,
) -> Result<bool, EvalError> {
    let mut seen: HashSet<(u32, u32)> = HashSet::new();
    let mut work = vec![(got, drift)];
    while let Some((g, d)) = work.pop() {
        if !seen.insert((g, d)) {
            continue;
        }
        let (kd, rowd) = w.term_ctor_row(index, d)?;
        let rowd = rowd.clone();
        match kd {
            TermCtor::Var => {
                let wire = w.local(index, &rowd.args[0])?;
                let (kg, rowg) = w.term_ctor_row(index, g)?;
                let rowg = rowg.clone();
                if wire == pinned_wire {
                    // The substituted position: the checked side must
                    // be exactly the constant at the facet plane.
                    if kg != TermCtor::Const {
                        return Ok(false);
                    }
                    let Value::Lit(l) = &rowg.args[0] else {
                        return Err(w.refuse(index, "TConst argument is not a literal cell".into()));
                    };
                    let Some(q) = QQ::from_q_literal(l) else {
                        return Err(w.refuse(index, "TConst argument is not a Q literal".into()));
                    };
                    if q != *pinned_value {
                        return Ok(false);
                    }
                } else {
                    if kg != TermCtor::Var {
                        return Ok(false);
                    }
                    if w.local(index, &rowg.args[0])? != wire {
                        return Ok(false);
                    }
                }
            }
            TermCtor::Const => {
                let (kg, rowg) = w.term_ctor_row(index, g)?;
                if kg != TermCtor::Const || rowg.args[0] != rowd.args[0] {
                    return Ok(false);
                }
            }
            TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                let (kg, rowg) = w.term_ctor_row(index, g)?;
                let rowg = rowg.clone();
                if kg != kd {
                    return Ok(false);
                }
                work.push((
                    w.local(index, &rowg.args[0])?,
                    w.local(index, &rowd.args[0])?,
                ));
                work.push((
                    w.local(index, &rowg.args[1])?,
                    w.local(index, &rowd.args[1])?,
                ));
            }
            // Unreachable behind the fragment gate; refuse rather than
            // guess if rows shift underneath us.
            TermCtor::Neg | TermCtor::Idx | TermCtor::Hole => {
                return Err(w.refuse(
                    index,
                    "drift term outside the scalar fragment reached substitution".into(),
                ))
            }
        }
    }
    Ok(true)
}

/// The sealed membership mask of `subject` under `contains_rel`,
/// validated against the vertex bound (an out-of-range membership row
/// corresponds to no model state and refuses — the mask-family
/// posture, mirrored).
fn sealed_mask(
    w: &Walk<'_>,
    rows: &CertRows,
    index: usize,
    subject: u32,
    contains_rel: Chid,
    bound: u64,
    what: &str,
) -> Result<BTreeSet<u64>, EvalError> {
    let mut out = BTreeSet::new();
    for row in rows
        .rel_attrs(subject)
        .iter()
        .filter(|r| r.rel == contains_rel)
    {
        if row.args.len() != 2 {
            return Err(w.refuse(
                index,
                format!(
                    "malformed `{what}` membership row: expected 2 arguments, got {}",
                    row.args.len()
                ),
            ));
        }
        let vertex = match &row.args[1] {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => n,
                _ => {
                    return Err(w.refuse(
                        index,
                        format!("malformed `{what}` membership row: vertex is not a Nat"),
                    ))
                }
            },
            _ => {
                return Err(w.refuse(
                    index,
                    format!("malformed `{what}` membership row: vertex is not a Nat"),
                ))
            }
        };
        if vertex >= bound {
            return Err(w.refuse(
                index,
                format!(
                    "`{what}` membership row cites vertex {vertex}, at or past the \
                     complex's {bound} vertices — outside the representable masks"
                ),
            ));
        }
        out.insert(vertex);
    }
    Ok(out)
}

/// The coordinate `SimpC/coord(complex, v, 0)` as an exact rational
/// (argument order is bytewise: complex, j, v).
fn vertex_coord(
    w: &Walk<'_>,
    rows: &CertRows,
    index: usize,
    v: &LatticeVocab,
    complex: u32,
    vertex: u64,
) -> Result<QQ, EvalError> {
    let mut found: Option<QQ> = None;
    for row in rows.arg_rows(complex) {
        if row.fun != v.simpc_coord {
            continue;
        }
        let [c_cell, j_cell, v_cell] = row.args.as_slice() else {
            return Err(w.refuse(
                index,
                format!(
                    "malformed `SimpC/coord` row: expected 3 arguments, got {}",
                    row.args.len()
                ),
            ));
        };
        if w.local(index, c_cell)? != complex {
            continue;
        }
        let (Value::Lit(jl), Value::Lit(vl)) = (j_cell, v_cell) else {
            return Err(w.refuse(
                index,
                "malformed `SimpC/coord` row: non-literal index".into(),
            ));
        };
        let (LiteralView::Nat(j), LiteralView::Nat(vv)) = (jl.view(), vl.view()) else {
            return Err(w.refuse(index, "malformed `SimpC/coord` row: non-Nat index".into()));
        };
        if j != 0 || vv != vertex {
            continue;
        }
        let Value::Lit(ql) = &row.value else {
            return Err(w.refuse(index, "`SimpC/coord` value is not a literal".into()));
        };
        let Some(q) = QQ::from_q_literal(ql) else {
            return Err(w.refuse(index, "`SimpC/coord` value is not a Q literal".into()));
        };
        match &found {
            None => found = Some(q),
            Some(prev) if *prev == q => {}
            Some(_) => {
                return Err(w.refuse(
                    index,
                    format!("ambiguous `SimpC/coord` for vertex {vertex} — never picking"),
                ))
            }
        }
    }
    found.ok_or_else(|| {
        w.refuse(
            index,
            format!("no `SimpC/coord` row for vertex {vertex} at coordinate 0 — unresolvable"),
        )
    })
}

/// Does the region atom `(extset, simplex)` denote exactly the closed
/// interval `[lo, hi]`? A structural mismatch is a decided `false`;
/// unreadable structure refuses.
#[allow(clippy::too_many_arguments)]
fn interval_atom_matches(
    w: &mut Walk<'_>,
    rows: &CertRows,
    index: usize,
    v: &LatticeVocab,
    extset: u32,
    simplex: u32,
    lo: &QQ,
    hi: &QQ,
) -> Result<bool, EvalError> {
    // The extension set must be anchored on the atom's own simplex and
    // must be empty.
    let ext_simplex = w.field_elem(index, extset, v.ext_simplex, "ExtensionSet/simplex")?;
    if ext_simplex != simplex {
        return Ok(false);
    }
    let complex = w.field_elem(index, simplex, v.simplex_complex, "Simplex/complex")?;
    let amb_dim = w.field_nat(index, complex, v.simpc_amb_dim, "SimpC/amb_dim")?;
    if amb_dim != 1 {
        return Ok(false);
    }
    let n_vertices = w.field_nat(index, complex, v.simpc_n_vertices, "SimpC/n_vertices")?;
    let ext_mask = sealed_mask(
        w,
        rows,
        index,
        extset,
        v.ext_contains,
        n_vertices,
        "ExtensionSet/contains",
    )?;
    if !ext_mask.is_empty() {
        return Ok(false);
    }
    let mask = sealed_mask(
        w,
        rows,
        index,
        simplex,
        v.simplex_contains,
        n_vertices,
        "Simplex/contains",
    )?;
    if mask.len() != 2 {
        return Ok(false);
    }
    let mut coords: Vec<QQ> = Vec::with_capacity(2);
    for &vertex in &mask {
        coords.push(vertex_coord(w, rows, index, v, complex, vertex)?);
    }
    let (a, b) = (&coords[0], &coords[1]);
    let (min, max) = if a.cmp_qq(b) == std::cmp::Ordering::Greater {
        (b, a)
    } else {
        (a, b)
    };
    Ok(min == lo && max == hi)
}

/// The facet-discharge obligation on one well-formed lattice: every
/// facet-proof slot concludes the required facet-sign sequent for its
/// canonical facet.
fn check_facet_discharge(
    w: &mut Walk<'_>,
    rows: &CertRows,
    v: &LatticeVocab,
    index: usize,
    lat: &LatticeData,
) -> Result<Decided<()>, EvalError> {
    let wire_to_axis: BTreeMap<u32, usize> = lat
        .axes
        .iter()
        .enumerate()
        .map(|(i, a)| (a.wire, i))
        .collect();
    for (bi, block) in lat.blocks.iter().enumerate() {
        let facets = canonical_facets(&lat.grid_counts, &block.cells);
        debug_assert_eq!(facets.len(), block.facet_proofs.len());
        for (fi, (facet, proof_val)) in facets.iter().zip(&block.facet_proofs).enumerate() {
            let proof = w.local(index, proof_val)?;
            let (pre, post) = w.concludes(index, proof)?;
            let axis = &lat.axes[facet.axis];
            let coords = coords_of(&lat.grid_counts, facet.cell);
            let c_i = usize::try_from(coords[facet.axis]).expect("budgeted");
            let pinned_value = if facet.upper {
                &axis.gridlines[c_i + 1]
            } else {
                &axis.gridlines[c_i]
            };

            // Post: one comparison atom, operator and margin sign by
            // inward direction, left side the substituted drift.
            let post_bad = || {
                Ok(Err(LatticeViolation::FacetPost {
                    block: bi,
                    facet: fi,
                }))
            };
            let Some((bowtie, l, r)) = w.as_atom(index, post)? else {
                return post_bad();
            };
            // Bowtie codes: 1 = LE, 3 = GE (the closed constructor
            // roster's order).
            let expected_bowtie: u8 = if facet.upper { 1 } else { 3 };
            if bowtie != expected_bowtie {
                return post_bad();
            }
            let (kr, rowr) = w.term_ctor_row(index, r)?;
            if kr != TermCtor::Const {
                return post_bad();
            }
            let Value::Lit(ml) = &rowr.args[0] else {
                return Err(w.refuse(index, "margin constant is not a literal cell".into()));
            };
            let Some(margin) = QQ::from_q_literal(ml) else {
                return Err(w.refuse(index, "margin constant is not a Q literal".into()));
            };
            let sign_ok = if facet.upper {
                // Block below the plane: inward is downward.
                !margin.is_nonneg()
            } else {
                margin.is_nonneg() && !margin.is_zero()
            };
            if !sign_ok {
                return post_bad();
            }
            if !subst_eq(w, index, l, axis.drift, axis.wire, pinned_value)? {
                return post_bad();
            }

            // Pre: an AND-tree of region atoms over the record's axis
            // wires, at most one per wire, at least one in total;
            // free-axis atoms carry the facet's cell interval, a
            // pinned-axis atom carries the full arena interval.
            let pre_bad = || {
                Ok(Err(LatticeViolation::FacetPre {
                    block: bi,
                    facet: fi,
                }))
            };
            let leaves = w.conjunct_list(index, pre)?;
            let mut seen_wires: BTreeSet<u32> = BTreeSet::new();
            for leaf in leaves {
                let (k, row) = w.form_ctor_row(index, leaf)?;
                if k != FormCtor::InRegion {
                    return pre_bad();
                }
                let row = row.clone();
                // Bytewise field order: S, simplex, t.
                let extset = w.local(index, &row.args[0])?;
                let simplex = w.local(index, &row.args[1])?;
                let t = w.local(index, &row.args[2])?;
                let (kt, rowt) = w.term_ctor_row(index, t)?;
                if kt != TermCtor::Var {
                    return pre_bad();
                }
                let rowt = rowt.clone();
                let atom_wire = w.local(index, &rowt.args[0])?;
                let Some(&j) = wire_to_axis.get(&atom_wire) else {
                    return pre_bad();
                };
                if !seen_wires.insert(atom_wire) {
                    return pre_bad();
                }
                let (lo, hi) = if j == facet.axis {
                    let g = &lat.axes[j].gridlines;
                    (&g[0], &g[g.len() - 1])
                } else {
                    let c_j = usize::try_from(coords[j]).expect("budgeted");
                    let g = &lat.axes[j].gridlines;
                    (&g[c_j], &g[c_j + 1])
                };
                if !interval_atom_matches(w, rows, index, v, extset, simplex, lo, hi)? {
                    return pre_bad();
                }
            }
            if seen_wires.is_empty() {
                return pre_bad();
            }
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// The product obligations
// ---------------------------------------------------------------------

/// Drift confinement on one factor: every drift's free wires are among
/// the factor's own axis wires.
fn check_confinement(lat: &LatticeData) -> Decided<()> {
    let wires: BTreeSet<u32> = lat.axes.iter().map(|a| a.wire).collect();
    for (i, a) in lat.axes.iter().enumerate() {
        if !a.drift_wires.is_subset(&wires) {
            return Err(LatticeViolation::DriftConfinement { axis: i });
        }
    }
    Ok(())
}

/// The composite-equals-product obligation over the geometric fields:
/// axes concatenated (same wires, structurally equal drifts, verbatim
/// gridlines) and blocks the extended pairwise products in the pinned
/// enumeration order. Facet slots are deliberately excluded — they
/// are governed by the facet-discharge obligation alone, which is
/// what makes citation sharing legal.
fn check_product(
    w: &mut Walk<'_>,
    index: usize,
    left: &LatticeData,
    right: &LatticeData,
    comp: &LatticeData,
) -> Result<Decided<()>, EvalError> {
    let n_l = left.axes.len();
    let n_r = right.axes.len();
    if comp.axes.len() != n_l + n_r {
        return Ok(Err(LatticeViolation::ProductAxes));
    }
    for (k, factor_axis) in left.axes.iter().chain(right.axes.iter()).enumerate() {
        let comp_axis = &comp.axes[k];
        if comp_axis.wire != factor_axis.wire
            || comp_axis.gridlines.len() != factor_axis.gridlines.len()
            || comp_axis
                .gridlines
                .iter()
                .zip(&factor_axis.gridlines)
                .any(|(a, b)| a != b)
        {
            return Ok(Err(LatticeViolation::ProductAxes));
        }
        if !w.struct_eq(index, comp_axis.drift, factor_axis.drift, true)? {
            return Ok(Err(LatticeViolation::ProductAxes));
        }
    }

    // Extended block families: stored blocks in index order, then the
    // factor arena.
    let arena = |lat: &LatticeData| -> Vec<u64> { (0..lat.n_cells).collect() };
    let n_bl = left.blocks.len() as u64;
    let n_br = right.blocks.len() as u64;
    let expected_count = (n_bl + 1) * (n_br + 1) - 1;
    if comp.blocks.len() as u64 != expected_count {
        return Ok(Err(LatticeViolation::ProductBlocks));
    }
    let left_ext: Vec<Vec<u64>> = left
        .blocks
        .iter()
        .map(|b| b.cells.clone())
        .chain(std::iter::once(arena(left)))
        .collect();
    let right_ext: Vec<Vec<u64>> = right
        .blocks
        .iter()
        .map(|b| b.cells.clone())
        .chain(std::iter::once(arena(right)))
        .collect();
    let n2 = right.n_cells;
    let mut slot = 0usize;
    let mut budget = 0u64;
    for (i1, c1) in left_ext.iter().enumerate() {
        for (i2, c2) in right_ext.iter().enumerate() {
            if i1 as u64 == n_bl && i2 as u64 == n_br {
                continue; // the implicit top: never stored
            }
            budget += (c1.len() as u64) * (c2.len() as u64);
            if budget > LATTICE_MAX_TOTAL_CELLS {
                return Err(w.refuse(
                    index,
                    "product enumeration exceeds the total cell budget".into(),
                ));
            }
            // {i1 · N2 + i2}: sorted by construction (both factors
            // strictly increasing, the map lexicographic).
            let expected: Vec<u64> = c1
                .iter()
                .flat_map(|&a| c2.iter().map(move |&b| a * n2 + b))
                .collect();
            if comp.blocks[slot].cells != expected {
                return Ok(Err(LatticeViolation::ProductBlocks));
            }
            slot += 1;
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------

/// Evaluate `blockLatticeWF [bl]`: decode + the record
/// well-formedness obligation.
pub(crate) fn eval_block_lattice_wf(
    name: &str,
    bl_vocab: &BlVocab,
    v: &LatticeVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let bl = elem_local(name, 0, args[0], rows)?;
    let mut w = Walk::new(name, bl_vocab, rows);
    Ok(decode_lattice(&mut w, rows, v, 0, bl)?.is_ok())
}

/// Evaluate `productLatticeChecks [p]`: record well-formedness on all
/// three lattices, then facet discharge, drift confinement, wire
/// disjointness, and product correctness.
pub(crate) fn eval_product_lattice_checks(
    name: &str,
    bl_vocab: &BlVocab,
    v: &LatticeVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let p = elem_local(name, 0, args[0], rows)?;
    let mut w = Walk::new(name, bl_vocab, rows);

    // flowsOnly is published metadata with zero proof weight; a value
    // outside its two-element index domain corresponds to no model
    // state (refusal, the mask-family posture).
    let flows_only = w.field_nat(0, p, v.prod_flows_only, "PProductLattice/flowsOnly")?;
    if flows_only > 1 {
        return Err(w.refuse(
            0,
            format!("`PProductLattice/flowsOnly` value {flows_only} is outside its index domain"),
        ));
    }

    let famj = w.field_elem(0, p, v.prod_concludes, "PProductLattice/concludes")?;
    let comp_elem = w.field_elem(0, famj, v.famj_lattice, "FamJudgment/lattice")?;
    let left_elem = w.field_elem(0, p, v.prod_left, "PProductLattice/left")?;
    let right_elem = w.field_elem(0, p, v.prod_right, "PProductLattice/right")?;

    // Record well-formedness on all three (the wire checker runs it on
    // all three records at consumption).
    let left = match decode_lattice(&mut w, rows, v, 0, left_elem)? {
        Ok(l) => l,
        Err(_) => return Ok(false),
    };
    let right = match decode_lattice(&mut w, rows, v, 0, right_elem)? {
        Ok(l) => l,
        Err(_) => return Ok(false),
    };
    let comp = match decode_lattice(&mut w, rows, v, 0, comp_elem)? {
        Ok(l) => l,
        Err(_) => return Ok(false),
    };

    // Wire disjointness.
    let left_wires: BTreeSet<u32> = left.axes.iter().map(|a| a.wire).collect();
    if right.axes.iter().any(|a| left_wires.contains(&a.wire)) {
        return Ok(false);
    }
    // Drift confinement, per factor.
    if check_confinement(&left).is_err() || check_confinement(&right).is_err() {
        return Ok(false);
    }
    // Composite = the product construction.
    if check_product(&mut w, 0, &left, &right, &comp)?.is_err() {
        return Ok(false);
    }
    // Facet discharge, all three records.
    for lat in [&left, &right, &comp] {
        if check_facet_discharge(&mut w, rows, v, 0, lat)?.is_err() {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn facet_enumeration_matches_hand_counts() {
        // 1-D, 2 cells, block {1}: one lower facet at cell 1.
        assert_eq!(
            canonical_facets(&[2], &[1]),
            vec![Facet {
                cell: 1,
                axis: 0,
                upper: false
            }]
        );
        // 2-D 2×2 grid, block {3} (cell (1,1)): lower faces on both
        // axes, canonical order axis 0 first.
        assert_eq!(
            canonical_facets(&[2, 2], &[3]),
            vec![
                Facet {
                    cell: 3,
                    axis: 0,
                    upper: false
                },
                Facet {
                    cell: 3,
                    axis: 1,
                    upper: false
                },
            ]
        );
        // 2-D 3×3 grid, L-shaped block {0, 3, 4}: hand-enumerated.
        // Coordinates (axis 0 slowest): 0 = (0,0), 3 = (1,0), 4 = (1,1).
        let facets = canonical_facets(&[3, 3], &[0, 3, 4]);
        assert_eq!(
            facets,
            vec![
                // cell 0 = (0,0): upper axis-1 neighbour 1 outside.
                Facet {
                    cell: 0,
                    axis: 1,
                    upper: true
                },
                // cell 3 = (1,0): upper axis-0 neighbour 6 outside.
                Facet {
                    cell: 3,
                    axis: 0,
                    upper: true
                },
                // cell 4 = (1,1): lower axis-0 neighbour 1, upper
                // axis-0 neighbour 7, upper axis-1 neighbour 5 — all
                // outside; lower axis-1 neighbour 3 is in the block.
                Facet {
                    cell: 4,
                    axis: 0,
                    upper: false
                },
                Facet {
                    cell: 4,
                    axis: 0,
                    upper: true
                },
                Facet {
                    cell: 4,
                    axis: 1,
                    upper: true
                },
            ]
        );
    }

    #[test]
    fn linearization_is_axis_zero_slowest() {
        // 2×3 grid: cell (1, 2) = 1·3 + 2 = 5.
        assert_eq!(index_of(&[2, 3], &[1, 2]), 5);
        assert_eq!(coords_of(&[2, 3], 5), vec![1, 2]);
    }
}
