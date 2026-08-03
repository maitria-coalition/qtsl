//! the arena-unification design — the unified-arena grid complex, wire side.
//!
//! Decoded value types for the re-staged `QGridCx` vocabulary
//! (the declaring theory, at the unified-arena design's second
//! revision — "rev 2" below), the review-repaired RGS partition-wire
//! validation, the
//! v0 checker-profile classification, and the canonical cell
//! enumeration whose degenerate case is pinned equal to the R1
//! oracle's convention 1 (axis 0 fastest) by an executable
//! differential (`tests/gridcx_wire.rs`).
//!
//! Pure combinatorics — no row-context machinery. The R1 oracle's
//! decode ([`crate::morse`]) and the wire tests consume these
//! functions; the certificate admission gate ([`crate::admission`])
//! carries its OWN decoded-type family and validator over the same
//! staged wire (agreeing on the hard-v0 slice, stricter about Kuhn
//! payloads) — TWO implementations today, not one authority; their
//! unification is a named unification seam (review finding,
//! adjudication: record-and-proceed).
//!
//! **The partition wire (rev 2, frozen)**: a partition of axes
//! `0..n` is staged as a per-axis group-index list in canonical
//! restricted-growth form (RGS):
//!
//! > part\[0\] = 0,  part\[k\] <= 1 + max(part\[..k\]).
//!
//! Valid RGS lists are in bijection with partitions whose groups are
//! labelled in first-occurrence order — and first occurrence IS the
//! the by-least-member canonical group order, so the label order is
//! the group order with no separate derivation. After the one O(n)
//! check, empty fibres, sparse labels, and noncanonical relabelings
//! are all excluded. Derived, never stored: `g = 1 + max(part)`.
//! Carrier (pinned jointly with the admission gate, [`crate::admission`]): the Shape
//! GROUND on `qptLeaf/part` — an order-preserving finite Nat-sequence
//! literal; no cons-list sort, no walk.
//!
//! **Interior-only cuts** (same joint pinning): `qgenInterval`'s list
//! carries strictly-interior cuts only; the axis extents live in
//! `qgcMk/dom` (single leaf) / the split-derived `R_P`, so endpoint
//! duplication — a skew class under the endpoint-inclusive reading —
//! is unrepresentable instead of checked. [`degenerate_cuts`] derives
//! the retired `QGrid`'s full lists back for the unchanged R1 core.
//!
//! **Generator kinds**: `qgenInterval`, fully decoded; `qgenKuhn`,
//! staged (a differential-gated completion, verdict PASS) but
//! OPAQUE at this layer — the
//! v0 profile never reaches a Kuhn cell, so the decoder classifies
//! without reading `res`/`splits`. The kind-vs-fibre gate:
//! `qgenInterval` iff |G_j| = 1, `qgenKuhn` iff |G_j| ∈ {2, 3} — all
//! five review-enumerated skew classes now carry fixtures,
//! Kuhn-on-singleton included.
//!
//! **The canonical cell enumeration (rev 2, frozen contract)**:
//! depth-first over the split tree, `lo` before `hi`; within a patch,
//! mixed-radix over groups in canonical group order (= RGS label
//! order), FIRST group fastest; within an interval group, ascending
//! interval index. Degenerate check (single leaf, all singletons):
//! groups are the axes ascending, first-fastest = axis 0 fastest, and
//! convention 1's `idx = c_0 + n_0·(c_1 + n_1·(…))` is recovered
//! verbatim — the mandatory bit-compat differential of this leg.

use geolog_envelope::Literal;

// ---------------------------------------------------------------------
// Decoded value types (what the wire sorts mean, checker-side)
// ---------------------------------------------------------------------

/// A per-group complex generator (`QGroupGen`). Interval only at the
/// original re-stage; the Kuhn constructor now plugs in beside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GroupGen {
    /// `qgenInterval(cuts)` — the INTERIOR-ONLY cut list (convention
    /// pinned jointly with the admission gate): strictly
    /// increasing, strictly inside the patch box's axis extent, which
    /// lives in `qgcMk/dom` / the split-derived `R_P` — endpoint skew
    /// is thereby unrepresentable rather than checked (the
    /// derive-don't-store posture; rev 2's own "empty interior cut
    /// lists" reading of the
    /// trivial patch). Cells on the group = `cuts.len() + 1`; the
    /// empty list is the trivial subdivision (one cell, the box).
    /// The retired `QGrid`'s full lists re-derive as
    /// `[dom.lo] + cuts + [dom.hi]` ([`degenerate_cuts`]).
    Interval { cuts: Vec<Literal> },
    /// `qgenKuhn(res, splits)` — staged (a differential-gated
    /// completion, verdict PASS) but OPAQUE at THIS layer: the v0
    /// checker profile never reaches a Kuhn cell (kind-vs-fibre
    /// refuses Kuhn-on-singleton; the profile refuses non-singleton
    /// groups), so this decoder classifies without reading `res`/
    /// `splits`. The admission gate is STRICTER since R2 (review finding): it decodes both fields and enforces the Kuhn-payload length
    /// obligations (`len(res) = |G_j|`, entries ≥ 1,
    /// `len(splits) = Π res`) with dedicated refusal arms — the
    /// divergence is one-directional (admission refuses more) and is
    /// part of DEBT-5's two-family seam. Kuhn cell counts and
    /// enumeration ride the producer reference (`mtk/src/qenum.rs`)
    /// until the mixed checker profile lands.
    Kuhn,
}

/// `QChartRef` — the sigma-variant's chart slot (theta_ref pattern:
/// slot now, semantics with its consumer).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChartRef {
    /// `qchIdentity` — the v0 profile's only admissible chart.
    Identity,
    /// `qchDigest(sha256hex)` — reserved; outside the v0 profile.
    Digest { sha256hex: String },
}

/// A `qptLeaf`'s payload: RGS partition, aligned generators, chart.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatchLeaf {
    /// The RGS partition wire: axis `k` belongs to group `part[k]`.
    /// Rides the Shape GROUND on `qptLeaf/part` (an order-preserving
    /// finite Nat-sequence literal — no cons-list sort; carrier
    /// pinned jointly with the admission gate, and the Shape
    /// index-domain registry carries the row).
    pub part: Vec<u64>,
    /// Per-group generators, aligned with the partition's label range.
    pub gens: Vec<GroupGen>,
    pub chart: ChartRef,
}

/// `QPatchTree` — the split forest. `R_P` is derived from the split
/// path, never stored (derived on the decode path by design).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatchTree {
    Leaf(PatchLeaf),
    Split {
        axis: u64,
        cut: Literal,
        lo: Box<PatchTree>,
        hi: Box<PatchTree>,
    },
}

/// `QGridCx` — ambient box + patch tree. `dom` is decoded as per-axis
/// `(lo, hi)` closed-interval bounds (the Qtsl `Box` cons-list).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GridCx {
    pub dom: Vec<(Literal, Literal)>,
    pub tree: PatchTree,
}

impl PatchTree {
    /// The tree's leaves in canonical (depth-first, lo-before-hi)
    /// patch order — wire validation runs per leaf, on every leaf,
    /// BEFORE any profile classification (matching the admission
    /// gate's generator-validity-then-profile order, so a skew leaf
    /// is a decided violation even inside an out-of-profile forest).
    pub fn leaves(&self) -> Vec<&PatchLeaf> {
        let mut out = Vec::new();
        let mut stack = vec![self];
        while let Some(node) = stack.pop() {
            match node {
                PatchTree::Leaf(leaf) => out.push(leaf),
                PatchTree::Split { lo, hi, .. } => {
                    stack.push(hi);
                    stack.push(lo);
                }
            }
        }
        out
    }
}

// ---------------------------------------------------------------------
// T-B: the partition-wire validation (the loader-path functions)
// ---------------------------------------------------------------------

/// A decided wire violation — ill-formed certificate CONTENT (the
/// admission gate refuses on these; the oracle maps them to a decided
/// `false` via `KitViolation::GridCxWire`, the grid-wf precedent).
/// Each variant is one of the review-enumerated skew classes,
/// stated at the wire level where RGS canonicalization leaves it:
/// empty fibres / sparse labels / noncanonical relabelings all
/// surface as one of the two RGS-clause violations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireViolation {
    /// `part[0] != 0` — a noncanonical relabeling's first symptom.
    PartitionFirstLabel { found: u64 },
    /// `part[k] > 1 + max(part[..k])` — sparse labels / skipped
    /// groups (the empty-fibre class, unrepresentable below this
    /// label-jump form once `g` is derived rather than stored).
    PartitionLabelJump {
        index: usize,
        label: u64,
        bound: u64,
    },
    /// `part.len() != ` the ambient dimension (the `qgcMk/dom` axis
    /// count) — the partition wire is length-`n` by definition.
    PartitionLength { part: usize, axes: usize },
    /// `gens.len() != 1 + max(part)` — the misaligned-`QGenList` skew.
    GenListMisaligned { groups: u64, gens: usize },
    /// An interval generator on a group with fibre size != 1 — the
    /// kind-vs-fibre gate (`qgenInterval` iff |G_j| = 1).
    IntervalOnMultiAxisGroup { group: u64, fiber: usize },
    /// A Kuhn generator on a group with fibre size outside {2, 3} —
    /// the gate's mirror arm (Kuhn-on-singleton, the fifth
    /// review-enumerated skew class, representable since `qgenKuhn`
    /// entered the staged vocabulary).
    KuhnOnFiber { group: u64, fiber: usize },
}

impl std::fmt::Display for WireViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WireViolation::PartitionFirstLabel { found } => {
                write!(f, "partition wire: part[0] = {found}, expected 0 (RGS)")
            }
            WireViolation::PartitionLabelJump {
                index,
                label,
                bound,
            } => write!(
                f,
                "partition wire: part[{index}] = {label} exceeds the RGS bound {bound}"
            ),
            WireViolation::PartitionLength { part, axes } => write!(
                f,
                "partition wire: length {part} against an ambient dimension of {axes}"
            ),
            WireViolation::GenListMisaligned { groups, gens } => write!(
                f,
                "generator list: {gens} generator(s) for {groups} partition group(s)"
            ),
            WireViolation::IntervalOnMultiAxisGroup { group, fiber } => write!(
                f,
                "group {group}: interval generator on a fiber of size {fiber} \
                 (qgenInterval iff |G_j| = 1)"
            ),
            WireViolation::KuhnOnFiber { group, fiber } => write!(
                f,
                "group {group}: Kuhn generator on a fiber of size {fiber} \
                 (qgenKuhn iff |G_j| in {{2, 3}})"
            ),
        }
    }
}

/// The RGS predicate — one total, local, O(n) scan. Returns the
/// derived group count `g = 1 + max(part)` (`0` for the empty list;
/// zero-dimensionality is a PROFILE refusal, not a wire violation —
/// see [`ProfileRefusal::ZeroDimensional`]).
pub fn validate_rgs(part: &[u64]) -> Result<u64, WireViolation> {
    let Some(&first) = part.first() else {
        return Ok(0);
    };
    if first != 0 {
        return Err(WireViolation::PartitionFirstLabel { found: first });
    }
    let mut max = 0u64;
    for (index, &label) in part.iter().enumerate().skip(1) {
        if label > max + 1 {
            return Err(WireViolation::PartitionLabelJump {
                index,
                label,
                bound: max + 1,
            });
        }
        max = max.max(label);
    }
    Ok(max + 1)
}

/// The full leaf wire check: partition length = the ambient dimension
/// (`axes` — for a single-leaf tree, `dom.len()`; under splits, the
/// same, since splits never change dimension), RGS canonical form,
/// `QGenList` length = derived `g`, generator kind gated by fibre
/// size. After `Ok(())`, every group of a staged (interval-only) leaf
/// is a singleton, so `part = [0, 1, …, n-1]` and group `j` IS axis
/// `j`.
pub fn validate_leaf(axes: usize, leaf: &PatchLeaf) -> Result<(), WireViolation> {
    if leaf.part.len() != axes {
        return Err(WireViolation::PartitionLength {
            part: leaf.part.len(),
            axes,
        });
    }
    let g = validate_rgs(&leaf.part)?;
    if leaf.gens.len() as u64 != g {
        return Err(WireViolation::GenListMisaligned {
            groups: g,
            gens: leaf.gens.len(),
        });
    }
    let mut fiber = vec![0usize; g as usize];
    for &label in &leaf.part {
        fiber[label as usize] += 1;
    }
    for (j, gen) in leaf.gens.iter().enumerate() {
        match gen {
            GroupGen::Interval { .. } => {
                if fiber[j] != 1 {
                    return Err(WireViolation::IntervalOnMultiAxisGroup {
                        group: j as u64,
                        fiber: fiber[j],
                    });
                }
            }
            GroupGen::Kuhn => {
                if !(fiber[j] == 2 || fiber[j] == 3) {
                    return Err(WireViolation::KuhnOnFiber {
                        group: j as u64,
                        fiber: fiber[j],
                    });
                }
            }
        }
    }
    Ok(())
}

/// RGS decode: the partition's groups (sorted member lists) in label
/// order — which the RGS bijection makes the by-least-member order.
/// Callers validate first; an un-validated list still decodes into
/// whatever its labels say (skew in, skew out), never panics.
pub fn rgs_decode(part: &[u64]) -> Vec<Vec<u64>> {
    let g = part.iter().copied().max().map_or(0, |m| m + 1);
    let mut groups = vec![Vec::new(); g as usize];
    for (axis, &label) in part.iter().enumerate() {
        if let Some(grp) = groups.get_mut(label as usize) {
            grp.push(axis as u64);
        }
    }
    groups
}

/// RGS encode: a set partition of `0..n` (disjoint covering blocks,
/// any order, any internal order) → its canonical RGS list. The
/// canonicalization IS the encoding: labels are assigned in
/// by-least-member block order. Returns `None` if the blocks are not
/// a partition of `0..n`.
pub fn rgs_encode(n: usize, groups: &[Vec<u64>]) -> Option<Vec<u64>> {
    let mut blocks: Vec<&Vec<u64>> = groups.iter().filter(|b| !b.is_empty()).collect();
    blocks.sort_by_key(|b| b.iter().copied().min());
    let mut part = vec![u64::MAX; n];
    for (label, block) in blocks.iter().enumerate() {
        for &axis in block.iter() {
            let slot = part.get_mut(usize::try_from(axis).ok()?)?;
            if *slot != u64::MAX {
                return None; // duplicate axis
            }
            *slot = label as u64;
        }
    }
    if part.contains(&u64::MAX) {
        return None; // uncovered axis
    }
    Some(part)
}

// ---------------------------------------------------------------------
// The v0 checker profile (capability classification — refusals)
// ---------------------------------------------------------------------

/// Outside the v0 checker profile — schema-valid content the v0
/// checker CANNOT DECIDE (refuse-not-guess), as distinct from a
/// [`WireViolation`] (ill-formed content, decided false). Widening any
/// of these is a profile-version event, never a silent behaviour
/// change (rev 2, a review fold).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProfileRefusal {
    /// The tree is a split — multi-patch complexes await the mixed
    /// checker profile (facet adjacency across patch boundaries is
    /// real geometry — a named successor obligation of the Lean
    /// generator-validity development).
    MultiPatch,
    /// A digest chart reference — chart semantics arrive with the
    /// sigma-variant's consumer legs.
    NonIdentityChart,
    /// `n = 0` — refused at admission in v0: no consumer exists
    /// (rev 2's pinned edge case).
    ZeroDimensional,
    /// A non-singleton partition group — mixed complexes await the
    /// mixed checker profile (the mixed-complex recompute machinery as its
    /// own profile-version event). Reachable since `qgenKuhn` entered
    /// the staged vocabulary (a valid leaf may carry fiber-2/3 groups);
    /// before that, all-singleton was implied by validation.
    NonSingletonGroup { group: u64 },
}

impl std::fmt::Display for ProfileRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProfileRefusal::MultiPatch => {
                write!(f, "multi-patch complex (v0 admits single-leaf only)")
            }
            ProfileRefusal::NonIdentityChart => {
                write!(
                    f,
                    "non-identity chart reference (v0 admits qchIdentity only)"
                )
            }
            ProfileRefusal::ZeroDimensional => {
                write!(f, "zero-dimensional domain (n = 0 is refused in v0)")
            }
            ProfileRefusal::NonSingletonGroup { group } => {
                write!(
                    f,
                    "partition group {group} is not a singleton (mixed complexes \
                     await the mixed checker profile)"
                )
            }
        }
    }
}

/// The v0 profile classification: single leaf, identity chart,
/// `n >= 1`, all-singleton partition (`part = [0, 1, …, n-1]` — the
/// unique all-singleton RGS list). RGS-canonical form and generator
/// alignment are [`validate_leaf`]'s half of the predicate —
/// capability first, then well-formedness.
pub fn v0_leaf(tree: &PatchTree) -> Result<&PatchLeaf, ProfileRefusal> {
    let leaf = match tree {
        PatchTree::Leaf(leaf) => leaf,
        PatchTree::Split { .. } => return Err(ProfileRefusal::MultiPatch),
    };
    if !matches!(leaf.chart, ChartRef::Identity) {
        return Err(ProfileRefusal::NonIdentityChart);
    }
    if leaf.part.is_empty() {
        return Err(ProfileRefusal::ZeroDimensional);
    }
    for (axis, &label) in leaf.part.iter().enumerate() {
        if label != axis as u64 {
            return Err(ProfileRefusal::NonSingletonGroup { group: label });
        }
    }
    Ok(leaf)
}

/// The degenerate extraction — THE interior-only flip point (its
/// admission-side twin is `admission.rs`'s `derive_degenerate_grid`):
/// a validated v0 leaf's per-axis FULL cut lists, derived as
/// `[dom.lo] + interior + [dom.hi]` per axis — group `j` is singleton
/// axis `j`, so the interval generators ARE the axes, in order. The
/// derived lists are the exact payload the retired `QGrid` carried,
/// and the R1 core runs on them unchanged: its strictly-increasing
/// grid-wf check on the derived list decides interiority for free
/// (`lo < c_0 ∧ sorted ∧ c_last < hi ∧ lo < hi` is exactly
/// "derived list strictly increasing").
pub fn degenerate_cuts(dom: &[(Literal, Literal)], leaf: &PatchLeaf) -> Vec<Vec<Literal>> {
    debug_assert!(
        validate_leaf(dom.len(), leaf).is_ok(),
        "callers validate first"
    );
    dom.iter()
        .zip(&leaf.gens)
        .map(|((lo, hi), g)| match g {
            GroupGen::Interval { cuts } => {
                let mut full = Vec::with_capacity(cuts.len() + 2);
                full.push(lo.clone());
                full.extend(cuts.iter().cloned());
                full.push(hi.clone());
                full
            }
            GroupGen::Kuhn => {
                unreachable!("v0 (all-singleton) validated leaves are interval-only")
            }
        })
        .collect()
}

// ---------------------------------------------------------------------
// The canonical cell enumeration (rev 2's frozen contract)
// ---------------------------------------------------------------------

/// One enumerated top cell: the owning leaf's ordinal in the
/// depth-first (lo-before-hi) patch order, plus its per-group
/// coordinate vector (group order = canonical label order; interval
/// coordinates are ascending interval indices).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellAddr {
    pub leaf: usize,
    pub coords: Vec<u64>,
}

/// Per-group top-cell counts of a leaf (interval group, interior-only
/// cuts: `cuts + 1` — never zero; the empty list is the trivial
/// one-cell subdivision). `None` when the leaf carries a Kuhn group:
/// Kuhn counts ride the producer reference (`mtk/src/qenum.rs`) until
/// the mixed checker profile lands.
pub fn leaf_group_sizes(leaf: &PatchLeaf) -> Option<Vec<u64>> {
    leaf.gens
        .iter()
        .map(|g| match g {
            GroupGen::Interval { cuts } => Some(cuts.len() as u64 + 1),
            GroupGen::Kuhn => None,
        })
        .collect()
}

/// Total top-cell count of a tree (`None` on u64 overflow or on a
/// Kuhn group — callers budget before materializing).
pub fn cell_count(tree: &PatchTree) -> Option<u64> {
    match tree {
        PatchTree::Leaf(leaf) => leaf_group_sizes(leaf)?
            .into_iter()
            .try_fold(1u64, |acc, n| acc.checked_mul(n)),
        PatchTree::Split { lo, hi, .. } => cell_count(lo)?.checked_add(cell_count(hi)?),
    }
}

/// The canonical cell enumeration, materialized: depth-first over the
/// split tree (`lo` before `hi`); within a leaf, mixed-radix over
/// groups with the FIRST group fastest, implemented as an odometer
/// (increment group 0, carry rightward) so the degenerate bit-compat
/// differential checks it against convention 1's closed formula
/// through a genuinely different code path. `None` when any leaf
/// carries a Kuhn group (its within-group order rides the producer
/// reference until the mixed checker profile lands).
pub fn enumerate_cells(tree: &PatchTree) -> Option<Vec<CellAddr>> {
    let mut out = Vec::new();
    let mut leaf_ordinal = 0usize;
    // Explicit DFS stack; nodes pushed hi-then-lo so lo pops first.
    let mut stack: Vec<&PatchTree> = vec![tree];
    while let Some(node) = stack.pop() {
        match node {
            PatchTree::Split { lo, hi, .. } => {
                stack.push(hi);
                stack.push(lo);
            }
            PatchTree::Leaf(leaf) => {
                // Interval sizes are cuts+1 ≥ 1, so every leaf emits
                // at least one cell; the n = 0 leaf emits exactly one
                // (the empty product — the whole patch box), refused
                // at the v0 profile but enumerated faithfully.
                let sizes = leaf_group_sizes(leaf)?;
                let mut coords = vec![0u64; sizes.len()];
                'odometer: loop {
                    out.push(CellAddr {
                        leaf: leaf_ordinal,
                        coords: coords.clone(),
                    });
                    for j in 0..sizes.len() {
                        coords[j] += 1;
                        if coords[j] < sizes[j] {
                            continue 'odometer;
                        }
                        coords[j] = 0;
                    }
                    break;
                }
                leaf_ordinal += 1;
            }
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(num: i64, den: u64) -> Literal {
        Literal::q(num, den).expect("canonical q")
    }

    fn interval_gen(interior: &[(i64, u64)]) -> GroupGen {
        GroupGen::Interval {
            cuts: interior.iter().map(|&(n, d)| q(n, d)).collect(),
        }
    }

    /// The degenerate leaf over given per-axis INTERIOR cut lists.
    fn degenerate_leaf(interior: &[&[(i64, u64)]]) -> PatchLeaf {
        PatchLeaf {
            part: (0..interior.len() as u64).collect(),
            gens: interior.iter().map(|c| interval_gen(c)).collect(),
            chart: ChartRef::Identity,
        }
    }

    #[test]
    fn rgs_accepts_canonical_and_derives_g() {
        assert_eq!(validate_rgs(&[0]), Ok(1));
        assert_eq!(validate_rgs(&[0, 1, 2]), Ok(3));
        assert_eq!(validate_rgs(&[0, 0, 1, 0, 2, 1]), Ok(3));
        assert_eq!(validate_rgs(&[]), Ok(0));
    }

    #[test]
    fn rgs_decode_is_by_least_member() {
        assert_eq!(
            rgs_decode(&[0, 1, 0, 2, 1]),
            vec![vec![0, 2], vec![1, 4], vec![3]]
        );
    }

    #[test]
    fn degenerate_enumeration_is_axis0_fastest_e1() {
        // The E1 worked-example grid as interior cuts over [0,1]²: 2 x 2 cells.
        let leaf = degenerate_leaf(&[&[(1, 4)], &[(1, 3)]]);
        let dom = vec![(q(0, 1), q(1, 1)), (q(0, 1), q(1, 1))];
        assert_eq!(
            degenerate_cuts(&dom, &leaf),
            vec![
                vec![q(0, 1), q(1, 4), q(1, 1)],
                vec![q(0, 1), q(1, 3), q(1, 1)],
            ],
            "derived full lists = the retired QGrid payload"
        );
        let tree = PatchTree::Leaf(leaf);
        let cells = enumerate_cells(&tree).expect("interval-only tree");
        let coords: Vec<Vec<u64>> = cells.into_iter().map(|c| c.coords).collect();
        assert_eq!(
            coords,
            vec![vec![0, 0], vec![1, 0], vec![0, 1], vec![1, 1]],
            "axis 0 fastest"
        );
        assert_eq!(cell_count(&tree), Some(4));
    }
}
