//! The R1 Morse-readout oracle — `qtsl_morse_readout` as a real
//! checker-side recompute (ends the relation's
//! schema-declaration-only status).
//!
//! Semantic authority: the Morse judgement's block-lattice readout
//! lemma ("Lemma M" below) with the R1 registry row of
//! the Morse rule roster as the recompute contract:
//! lattice ∪/∩ closure over cell bitmaps; facet-row presence +
//! canonical facet-list alignment (`blockLatticeWF`'s class, per an
//! adjudicated split — the wedge GEOMETRY moved Lean-side, so R1's
//! obligation here is syntactic well-formedness + the combinatorial
//! recompute); the readout (join-irreducibles, unique lower covers,
//! cells, cell order — recompute-don't-trust: the recomputed
//! enumeration is the SOLE authority the certificate's `h` indices are
//! read against); `h` fibre convexity + vertex-cell monotonicity; dag
//! check; box-aligned ρ disjointness/containment.
//!
//! **Pinned conventions** (the frozen sources under-determine these;
//! each named as a finding in the design record; the "revisable before
//! any production byte" clause was exercised by the the arena unification
//! unified-arena re-stage — conventions 1 and 2 now read against the
//! new wire, same semantics on the degenerate profile):
//!
//! 1. **cell linearization**: axis 0 fastest —
//!    `idx = c_0 + n_0·(c_1 + n_1·(…))` over the per-axis cell counts
//!    `n_k = cuts_k.len() − 1` of the DERIVED grid (dom endpoints +
//!    interior cuts, [`crate::gridcx::degenerate_cuts`]) — the
//!    degenerate case of the canonical cell enumeration, pinned
//!    equal by the gridcx bit-compat differential.
//! 2. **canonical facet order**: sorted by `(cell, group, facet)` —
//!    the generalized descriptor with the degenerate reading
//!    (singleton group = the axis; facet 0/1 = lower/upper, so
//!    convention 2's lower-before-upper survives verbatim). A facet
//!    row's `cells` Shape may cover several cells (the worked
//!    example's A.a.x does); alignment is checked on the FLATTENED
//!    sequence (rows in list order × row cells ascending) against the
//!    canonical enumeration. Facets are faces between a block cell
//!    and an arena cell outside the block; grid-boundary faces and
//!    faces into non-arena cells are ∂D-faces and owe nothing
//!    (`QtslGridGeometry.lean` header).
//! 3. **join-irreducible enumeration**: ascending lexicographic order
//!    of the members' sorted cell-index sequences (prefix-shorter
//!    first). `QCellMap`'s `cell` field indexes THIS enumeration.
//! 4. **dag order**: `v ≥_G w` ⟺ a directed path `v →* w` exists.
//!    Lemma M(v)(b)'s monotonicity is checked as: for vertex-mapped
//!    `b' ⊆ b`, `h(b)` reaches `h(b')` (the worked example's
//!    top-cell-to-source reading).
//! 5. **box-aligned ρ**: a region qualifies iff it is a finite
//!    conjunction (`SAnd` tree / atoms / `STrue`) of coordinate-
//!    monomial atoms (`SAtomLE`/`SAtomGE` over `c·x_k`, `c ≠ 0`) whose
//!    folded per-axis bounds are ALL finite and each equal to a grid
//!    cut. Disjointness is grid-level (bitmap — the regularized
//!    reading, matching Lemma M's "bitmap-and realizes KMV's
//!    regularized meet"); containment is cellset ⊆ arena. Anything
//!    else is OPAQUE: its well-formedness rides the rule's `rho_wf`
//!    Proof rows, not R1 (the roster's box-aligned scope).
//! 6. **constructor rosters exclude attribute funs** — the staged
//!    corpus's `Entity/attr` naming convention read as schema data:
//!    slash-named funs (`QMorse/graph`, `QRegionSat/formula`) produce
//!    values by REFERENCE, not construction, and must not render a
//!    referenced element's structure ambiguous. Mis-classification in
//!    either direction degrades to refusal, never a flipped verdict.
//!
//! Verdict discipline (the CtxArg pattern, unchanged): a decided
//! violation is `Ok(false)` — with the violation NAMED via
//! [`KitViolation`] for callers that want the reason — and anything
//! the row context cannot decide (unconstructed/ambiguous elements,
//! exhausted budgets, oversize kits) REFUSES, never guesses.

use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{AttrRow, CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{Literal, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// The Morse-readout family's row of the claimed roster (concatenated
/// at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_morse_readout",
    &[
        ("dag", "QDag"),
        ("h", "QCellMap"),
        ("lat", "QBlockLattice"),
        ("rho", "QVertexRegionList"),
    ],
    RelKind::Morse,
)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const MORSE_MAX_CELLS: u64 = 1 << 16;
pub const MORSE_MAX_BLOCKS: usize = 512;
pub const MORSE_MAX_VERTICES: u64 = 1 << 16;
pub const MORSE_MAX_EDGES: usize = 1 << 20;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// The pinned constructor vocabulary (C-ORACLE: names select once at
// registry construction; all dispatch is by these identities)
// ---------------------------------------------------------------------

/// The Morse-kit constructor vocabulary, pinned at registry
/// construction from the sorts the `qtsl_morse_readout` declaration
/// names. `ctors` rosters EVERY non-relational fun into each kit sort
/// across the swept revisions, so "constructed by something else" is a
/// definite verdict distinct from "not constructed in view" (refusal).
#[derive(Debug, Clone)]
pub struct MorseVocab {
    // R1 kit constructors.
    qdag_mk: Chid,
    qde_nil: Chid,
    qde_cons: Chid,
    qcm_nil: Chid,
    qcm_vertex: Chid,
    qcm_transit: Chid,
    qvr_nil: Chid,
    qvr_cons: Chid,
    // QBlockLattice attribute funs (entity-like: read via the subject
    // view, not the producer view).
    lat_cx: Chid,
    lat_arena: Chid,
    lat_blocks: Chid,
    // The unified-arena generator vocabulary (the arena unification): QGridCx =
    // ambient box + patch tree; leaves carry RGS partition + aligned
    // generators + chart slot. Decoded into `gridcx::GridCx`.
    qgc_mk: Chid,
    qpt_leaf: Chid,
    qpt_split: Chid,
    qgl_nil: Chid,
    qgl_cons: Chid,
    qgen_interval: Chid,
    qgen_kuhn: Chid,
    qch_identity: Chid,
    qch_digest: Chid,
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    qrl_nil: Chid,
    qrl_cons: Chid,
    qb_nil: Chid,
    qb_cons: Chid,
    qf_nil: Chid,
    qf_cons: Chid,
    // The Qtsl spec-surface slice the box-aligned ρ recognizer
    // dispatches on (shared with the admission gate — the shared-recognizer contract).
    region: RegionVocab,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// The spec-surface vocabulary slice the box-aligned ρ recognizer
/// ([`classify_region`]) dispatches on: the eight constructor
/// identities plus the full producer rosters of their three sorts
/// (StateF, SFList, Poly). Roster membership is what separates
/// "constructed by some OTHER spec-surface constructor" (SOr, SNot, …
/// — a definite OPAQUE, the Proof-row lane) from "no constructor row
/// in view" (undecidable — refusal). The staged R1 decoder and the
/// admission gate both build this ONE type and call the ONE recognizer,
/// so the two gates cannot diverge on that boundary (review finding's
/// parity bar; fields public for the admission vocabulary's test
/// injection, the [`crate::admission::ArenaVocab`] pattern).
#[derive(Debug, Clone)]
pub struct RegionVocab {
    pub s_true: Chid,
    pub s_and: Chid,
    pub s_atom_le: Chid,
    pub s_atom_ge: Chid,
    pub sl_nil: Chid,
    pub sl_cons: Chid,
    pub p_zero: Chid,
    pub p_term: Chid,
    /// Producer roster of the StateF sort (membership only).
    pub statef_roster: HashSet<Chid>,
    /// Producer roster of the SFList sort.
    pub sflist_roster: HashSet<Chid>,
    /// Producer roster of the Poly sort.
    pub poly_roster: HashSet<Chid>,
    /// Post-grid (event-4) closures only: the `oPoly` injection — the
    /// SAtom re-founding moved the polynomial behind a
    /// StateObservable argument, so the atom decode takes one more
    /// hop. `None` on legacy closures, where atoms carry the
    /// polynomial directly (the dual-pin discipline: per-closure
    /// resolution keeps both vintages checking).
    pub o_poly: Option<Chid>,
    /// Producer roster of the StateObservable sort (empty on legacy
    /// closures).
    pub stateobs_roster: HashSet<Chid>,
}

/// The `qtsl_morse_readout` relation's expected shape — record
/// `{dag: D, h: H, lat: L, rho: R}` (bytewise field order) with
/// four distinct declared sorts. Returns (D, H, L, R) on match.
pub fn matches_morse_signature(sig: &DomainSig) -> Option<(Chid, Chid, Chid, Chid)> {
    let DomainSig::Record(fields) = sig else {
        return None;
    };
    let [(f0, s0), (f1, s1), (f2, s2), (f3, s3)] = fields.as_slice() else {
        return None;
    };
    if f0 != "dag" || f1 != "h" || f2 != "lat" || f3 != "rho" {
        return None;
    }
    let (SortKey::Elem(d), SortKey::Elem(h), SortKey::Elem(l), SortKey::Elem(r)) = (s0, s1, s2, s3)
    else {
        return None;
    };
    let four = [*d, *h, *l, *r];
    for i in 0..4 {
        for j in i + 1..4 {
            if four[i] == four[j] {
                return None;
            }
        }
    }
    Some((*d, *h, *l, *r))
}

/// Build the Morse-kit vocabulary for the four sorts a gated
/// declaration names. Names select the constructors, shapes verify,
/// identities pin (the `build_syntax_vocab` pattern). `Err` → the
/// candidate relation Refuses (C-ORACLE safe-fail).
pub fn build_morse_vocab(
    indices: &[&TheoryIndex],
    dag_sort: Chid,
    cellmap_sort: Chid,
    lat_sort: Chid,
    vrl_sort: Chid,
) -> Result<MorseVocab, String> {
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
    // Record-shape check by (field name, expectation) — Elem
    // expectations either pin a known sort or CAPTURE one.
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

    // --- the dag ------------------------------------------------------
    let (qdag_mk, mk_sig) = find("qdagMk", dag_sort, &|s| {
        record(
            s,
            &[("edges", F::Capture), ("vertices", F::Ground(Ground::Nat))],
        )
        .map(|_| ())
    })?;
    let edges_sort = record(
        &mk_sig,
        &[("edges", F::Capture), ("vertices", F::Ground(Ground::Nat))],
    )
    .expect("checked above")[0];
    let (qde_nil, _) = find("qdeNil", edges_sort, &nullary)?;
    let (qde_cons, _) = find("qdeCons", edges_sort, &|s| {
        record(
            s,
            &[
                ("dst", F::Ground(Ground::Nat)),
                ("src", F::Ground(Ground::Nat)),
                ("tail", F::Elem(edges_sort)),
            ],
        )
        .map(|_| ())
    })?;

    // --- the cell map -------------------------------------------------
    let (qcm_nil, _) = find("qcmNil", cellmap_sort, &nullary)?;
    let (qcm_vertex, _) = find("qcmVertex", cellmap_sort, &|s| {
        record(
            s,
            &[
                ("cell", F::Ground(Ground::Nat)),
                ("tail", F::Elem(cellmap_sort)),
                ("vertex", F::Ground(Ground::Nat)),
            ],
        )
        .map(|_| ())
    })?;
    let (qcm_transit, _) = find("qcmTransit", cellmap_sort, &|s| {
        record(
            s,
            &[
                ("cell", F::Ground(Ground::Nat)),
                ("tail", F::Elem(cellmap_sort)),
            ],
        )
        .map(|_| ())
    })?;

    // --- rho ----------------------------------------------------------
    let (qvr_nil, _) = find("qvrNil", vrl_sort, &nullary)?;
    let (qvr_cons, cons_sig) = find("qvrCons", vrl_sort, &|s| {
        record(
            s,
            &[
                ("region", F::Capture),
                ("tail", F::Elem(vrl_sort)),
                ("vertex", F::Ground(Ground::Nat)),
            ],
        )
        .map(|_| ())
    })?;
    let statef_sort = record(
        &cons_sig,
        &[
            ("region", F::Capture),
            ("tail", F::Elem(vrl_sort)),
            ("vertex", F::Ground(Ground::Nat)),
        ],
    )
    .expect("checked above")[0];

    // --- the lattice's attribute funs (entity-like) -------------------
    let attr =
        |name: &str, cod_check: &dyn Fn(&SortKey) -> bool| -> Result<(Chid, SortKey), String> {
            for index in indices {
                let Some(d) = index.fun(name) else { continue };
                if d.relational
                    || d.domain != DomainSig::Unary(SortKey::Elem(lat_sort))
                    || !d.codomain.as_ref().is_some_and(cod_check)
                {
                    return Err(format!(
                        "`{name}` is not the expected QBlockLattice attribute \
                     (wrong kind, domain, or codomain)"
                    ));
                }
                return Ok((d.chid, d.codomain.expect("checked")));
            }
            Err(format!("no `{name}` attribute among the swept revisions"))
        };
    let (lat_cx, cx_cod) = attr("QBlockLattice/cx", &|c| matches!(c, SortKey::Elem(_)))?;
    let (lat_arena, _) = attr("QBlockLattice/arena", &|c| {
        *c == SortKey::Ground(Ground::Shape)
    })?;
    let (lat_blocks, blocks_cod) =
        attr("QBlockLattice/blocks", &|c| matches!(c, SortKey::Elem(_)))?;
    let SortKey::Elem(gridcx_sort) = cx_cod else {
        unreachable!("checked elem above")
    };
    let SortKey::Elem(blocklist_sort) = blocks_cod else {
        unreachable!("checked elem above")
    };

    // --- the unified-arena generator vocabulary (the arena unification) ------------
    let (qgc_mk, mk_sig) = find("qgcMk", gridcx_sort, &|s| {
        record(s, &[("dom", F::Capture), ("tree", F::Capture)]).map(|_| ())
    })?;
    let captured =
        record(&mk_sig, &[("dom", F::Capture), ("tree", F::Capture)]).expect("checked above");
    let (box_sort, patchtree_sort) = (captured[0], captured[1]);
    // part rides the Shape GROUND (the RGS partition wire's carrier).
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
    // Staged vocabulary; opaque to this oracle (never read
    // past the constructor identity — the v0 profile refuses first).
    let (qgen_kuhn, _) = find("qgenKuhn", groupgen_sort, &|s| {
        record(s, &[("res", F::AnyElem), ("splits", F::AnyElem)]).map(|_| ())
    })?;
    let (qch_identity, _) = find("qchIdentity", chartref_sort, &nullary)?;
    let (qch_digest, _) = find("qchDigest", chartref_sort, &|s| {
        record(s, &[("sha256hex", F::Ground(Ground::Str))]).map(|_| ())
    })?;
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
    let (qb_nil, _) = find("qbNil", blocklist_sort, &nullary)?;
    let (qb_cons, bc_sig) = find("qbCons", blocklist_sort, &|s| {
        record(
            s,
            &[
                ("cells", F::Ground(Ground::Shape)),
                ("facets", F::Capture),
                ("tail", F::Elem(blocklist_sort)),
            ],
        )
        .map(|_| ())
    })?;
    let facetlist_sort = record(
        &bc_sig,
        &[
            ("cells", F::Ground(Ground::Shape)),
            ("facets", F::Capture),
            ("tail", F::Elem(blocklist_sort)),
        ],
    )
    .expect("checked above")[0];
    let (qf_nil, _) = find("qfNil", facetlist_sort, &nullary)?;
    // the generalized descriptor (group, facet) — degenerate
    // reading: singleton group IS the axis, facet 0/1 = lower/upper.
    let (qf_cons, _) = find("qfCons", facetlist_sort, &|s| {
        record(
            s,
            &[
                ("cells", F::Ground(Ground::Shape)),
                ("facet", F::Ground(Ground::Nat)),
                ("group", F::Ground(Ground::Nat)),
                ("proof", F::AnyElem),
                ("tail", F::Elem(facetlist_sort)),
            ],
        )
        .map(|_| ())
    })?;

    // --- the spec-surface vocabulary the ρ recognizer dispatches on ---
    let (s_true, _) = find("STrue", statef_sort, &nullary)?;
    let (s_and, sand_sig) = find("SAnd", statef_sort, &|s| match s {
        DomainSig::Unary(SortKey::Elem(_)) => Ok(()),
        _ => Err("expected a unary elem-sorted constructor".into()),
    })?;
    let DomainSig::Unary(SortKey::Elem(sflist_sort)) = sand_sig else {
        unreachable!("checked above")
    };
    // Dual-shape atoms (the versioned-vocabulary discipline): legacy
    // closures spell `SAtomLE {c, poly: Poly}`; the event-4 grid
    // re-founded the argument as `{c, o: StateObservable}` with the
    // polynomial view riding the `oPoly` injection. Per-closure
    // resolution keeps both vintages checking — the classifier
    // dispatches on which shape bound.
    let direct = find("SAtomLE", statef_sort, &|s| {
        record(s, &[("c", F::Ground(Ground::Q)), ("poly", F::Capture)]).map(|_| ())
    });
    let (s_atom_le, s_atom_ge, poly_sort, o_poly, stateobs_sort) = match direct {
        Ok((s_atom_le, le_sig)) => {
            let poly_sort = record(
                &le_sig,
                &[("c", F::Ground(Ground::Q)), ("poly", F::Capture)],
            )
            .expect("checked above")[0];
            let (s_atom_ge, _) = find("SAtomGE", statef_sort, &|s| {
                record(
                    s,
                    &[("c", F::Ground(Ground::Q)), ("poly", F::Elem(poly_sort))],
                )
                .map(|_| ())
            })?;
            (s_atom_le, s_atom_ge, poly_sort, None, None)
        }
        Err(e_direct) => {
            let (s_atom_le, le_sig) = find("SAtomLE", statef_sort, &|s| {
                record(s, &[("c", F::Ground(Ground::Q)), ("o", F::Capture)]).map(|_| ())
            })
            .map_err(|e_obs| {
                format!(
                    "`SAtomLE`: neither atom shape resolved (direct-poly: \
                     {e_direct}; oPoly-observable: {e_obs})"
                )
            })?;
            let stateobs_sort = record(&le_sig, &[("c", F::Ground(Ground::Q)), ("o", F::Capture)])
                .expect("checked above")[0];
            let (s_atom_ge, _) = find("SAtomGE", statef_sort, &|s| {
                record(
                    s,
                    &[("c", F::Ground(Ground::Q)), ("o", F::Elem(stateobs_sort))],
                )
                .map(|_| ())
            })?;
            let (o_poly, op_sig) = find("oPoly", stateobs_sort, &|s| {
                record(s, &[("poly", F::Capture)]).map(|_| ())
            })?;
            let poly_sort = record(&op_sig, &[("poly", F::Capture)]).expect("checked above")[0];
            (
                s_atom_le,
                s_atom_ge,
                poly_sort,
                Some(o_poly),
                Some(stateobs_sort),
            )
        }
    };
    let (sl_nil, _) = find("slNil", sflist_sort, &nullary)?;
    let (sl_cons, _) = find("slCons", sflist_sort, &|s| {
        record(
            s,
            &[
                ("head", F::Elem(statef_sort)),
                ("tail", F::Elem(sflist_sort)),
            ],
        )
        .map(|_| ())
    })?;
    let (p_zero, _) = find("pZero", poly_sort, &nullary)?;
    let (p_term, _) = find("pTerm", poly_sort, &|s| {
        record(
            s,
            &[
                ("coeff", F::Ground(Ground::Q)),
                ("expts", F::Ground(Ground::Shape)),
                ("tail", F::Elem(poly_sort)),
            ],
        )
        .map(|_| ())
    })?;

    // --- per-sort constructor rosters ---------------------------------
    let kit_sorts = [
        dag_sort,
        edges_sort,
        cellmap_sort,
        vrl_sort,
        gridcx_sort,
        patchtree_sort,
        genlist_sort,
        groupgen_sort,
        chartref_sort,
        box_sort,
        interval_sort,
        ratlist_sort,
        blocklist_sort,
        facetlist_sort,
        statef_sort,
        sflist_sort,
        poly_sort,
    ];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in kit_sorts {
        ctors.entry(s).or_default();
    }
    // Post-grid closures roster the observable sort too (the atom
    // decode's oPoly hop dispatches over it).
    if let Some(so) = stateobs_sort {
        ctors.entry(so).or_default();
    }
    for index in indices {
        for decl in &index.funs {
            if decl.relational {
                continue;
            }
            // ATTRIBUTE funs are excluded from the constructor rosters
            // (pinned convention 6): the reference corpus names attributes
            // `Entity/attr` and constructors slash-free, and an
            // attribute row `QMorse/graph(j) = d` must not read as a
            // second producer of `d` (P-FUN is per-fun, not
            // per-element). Both mis-classification directions degrade
            // to refusal/Opaque, never a flipped verdict: a slash-named
            // constructor's values become structure-undecidable
            // (refuse), a slash-free attribute's values become
            // ambiguous (refuse).
            if decl.name.contains('/') {
                continue;
            }
            if let Some(SortKey::Elem(c)) = decl.codomain {
                if let Some(roster) = ctors.get_mut(&c) {
                    roster.insert(decl.chid, decl.domain.clone());
                }
            }
        }
    }

    // The recognizer's shared slice (the shared-recognizer contract): chids + the three
    // spec-surface rosters, projected membership-only.
    let roster_of = |sort: Chid| -> HashSet<Chid> {
        ctors
            .get(&sort)
            .expect("spec-surface sorts rostered")
            .keys()
            .copied()
            .collect()
    };
    let region = RegionVocab {
        s_true,
        s_and,
        s_atom_le,
        s_atom_ge,
        sl_nil,
        sl_cons,
        p_zero,
        p_term,
        statef_roster: roster_of(statef_sort),
        sflist_roster: roster_of(sflist_sort),
        poly_roster: roster_of(poly_sort),
        o_poly,
        stateobs_roster: stateobs_sort.map(&roster_of).unwrap_or_default(),
    };

    Ok(MorseVocab {
        qdag_mk,
        qde_nil,
        qde_cons,
        qcm_nil,
        qcm_vertex,
        qcm_transit,
        qvr_nil,
        qvr_cons,
        lat_cx,
        lat_arena,
        lat_blocks,
        qgc_mk,
        qpt_leaf,
        qpt_split,
        qgl_nil,
        qgl_cons,
        qgen_interval,
        qgen_kuhn,
        qch_identity,
        qch_digest,
        box_nil,
        box_cons,
        mk_interval,
        qrl_nil,
        qrl_cons,
        qb_nil,
        qb_cons,
        qf_nil,
        qf_cons,
        region,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The decoded kit (pure data — the core checks run on this, so tests
// and the differential reference hit the combinatorics directly)
// ---------------------------------------------------------------------

/// One block's declared data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockData {
    /// Sorted-strict cell indices (the Shape payload, verbatim).
    pub cells: Vec<u64>,
    /// Facet rows in list order: (group, facet, cells Shape verbatim).
    pub facets: Vec<FacetRow>,
}

/// A facet row's descriptor — the arena-unification generalized form
/// `(group, facet)`, degenerate reading pinned: on the v0 profile a
/// singleton group IS the axis, and facet 0/1 = lower/upper. On
/// simplex cells `facet` indexes the group generator's derived
/// facet enumeration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FacetRow {
    pub group: u64,
    pub facet: u64,
    pub cells: Vec<u64>,
}

/// One `h` entry, in list order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HEntry {
    Vertex { cell: u64, vertex: u64 },
    Transit { cell: u64 },
}

/// One ρ entry's decoded classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionClass {
    /// Fully-bounded, cut-aligned coordinate box → its grid cellset
    /// (sorted linear indices; possibly empty for degenerate boxes,
    /// the regularized reading).
    BoxAligned(Vec<u64>),
    /// Everything else: well-formedness rides the rule's `rho_wf`
    /// Proof rows, outside R1's box-aligned scope.
    Opaque,
}

/// The decoded Morse kit. Grid cuts are canonical Q literals.
#[derive(Debug, Clone)]
pub struct MorseKit {
    /// Per-axis strictly-increasing rational cuts, endpoints included
    /// (wf-checked by the core, not the decoder). Under the generalized-descriptor
    /// unified-arena wire these are DERIVED — `[dom.lo] + interior +
    /// [dom.hi]` per axis from the v0 leaf's interval generators
    /// ([`crate::gridcx::degenerate_cuts`]); the core runs on the
    /// derived presentation unchanged, and its strictly-increasing
    /// check decides cut interiority for free.
    pub grid: Vec<Vec<Literal>>,
    /// The arena cell-set (Shape payload, verbatim).
    pub arena: Vec<u64>,
    pub blocks: Vec<BlockData>,
    pub dag_vertices: u64,
    /// (src, dst) pairs in list order.
    pub dag_edges: Vec<(u64, u64)>,
    pub h: Vec<HEntry>,
    /// (vertex, region) pairs in list order.
    pub rho: Vec<(u64, RegionClass)>,
}

// ---------------------------------------------------------------------
// The named violations (decided-false reasons)
// ---------------------------------------------------------------------

/// A decided kit violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is a check the frozen R1 contract names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KitViolation {
    /// An axis with < 2 cuts, or cuts not strictly increasing.
    GridWf { axis: usize },
    /// Arena empty, unsorted, duplicated, or out of range.
    ArenaWf,
    /// A declared block's cells empty/unsorted/out-of-range, not a
    /// proper nonempty subset of the arena, or a duplicate of another
    /// declared block.
    BlockWf { block: usize },
    /// A block's facet rows do not flatten to the canonical boundary
    /// facet enumeration (sorted by (cell, axis, − before +),
    /// ∂D-faces excluded).
    FacetAlignment { block: usize, why: String },
    /// The declared family ∪ {∅, arena} is not ∪/∩-closed: some
    /// join/meet lands outside it (a closure member without facet
    /// rows).
    ClosureHole { why: String },
    /// Dag edge endpoint out of range, or the graph has a cycle.
    DagWf { why: String },
    /// `h` is not a total function on the recomputed join-irreducible
    /// enumeration (missing/duplicate/out-of-range cell index), or a
    /// vertex image is out of range.
    HTotality { why: String },
    /// An `h`-fibre over a vertex is not convex in the recomputed
    /// cell order (Lemma M(v)(a)).
    FiberConvexity { vertex: u64 },
    /// Vertex-mapped cells violate Lemma M(v)(b): `b' ⊆ b` with no
    /// path `h(b) →* h(b')`.
    HMonotonicity { why: String },
    /// ρ is not a total function on the dag's vertices
    /// (missing/duplicate/out-of-range vertex).
    RhoWf { why: String },
    /// A box-aligned ρ region's cellset is not contained in the arena.
    RhoContainment { vertex: u64 },
    /// Two box-aligned ρ regions overlap at grid level.
    RhoOverlap { v1: u64, v2: u64 },
    /// The lattice's `QGridCx` violates the unified-arena wire
    /// contract (the arena-unification design): RGS partition skew, misaligned
    /// generator list, generator-kind-vs-fibre mismatch — decided at
    /// decode, the grid-wf precedent (the admission gate refuses on
    /// the same [`crate::gridcx::WireViolation`]).
    GridCxWire(crate::gridcx::WireViolation),
}

impl std::fmt::Display for KitViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KitViolation::GridWf { axis } => {
                write!(f, "grid axis {axis}: needs >= 2 strictly increasing cuts")
            }
            KitViolation::ArenaWf => write!(f, "arena cell-set malformed"),
            KitViolation::BlockWf { block } => write!(f, "block {block} cell-set malformed"),
            KitViolation::FacetAlignment { block, why } => {
                write!(f, "block {block} facet rows misaligned: {why}")
            }
            KitViolation::ClosureHole { why } => write!(f, "lattice closure hole: {why}"),
            KitViolation::DagWf { why } => write!(f, "dag check failed: {why}"),
            KitViolation::HTotality { why } => write!(f, "h not total/functional: {why}"),
            KitViolation::FiberConvexity { vertex } => {
                write!(
                    f,
                    "h-fiber over vertex {vertex} not convex in the cell order"
                )
            }
            KitViolation::HMonotonicity { why } => write!(f, "h not monotone: {why}"),
            KitViolation::RhoWf { why } => write!(f, "rho not total/functional: {why}"),
            KitViolation::RhoContainment { vertex } => {
                write!(f, "rho({vertex}) not contained in the arena")
            }
            KitViolation::RhoOverlap { v1, v2 } => {
                write!(f, "rho({v1}) and rho({v2}) overlap at grid level")
            }
            KitViolation::GridCxWire(w) => {
                write!(f, "grid-complex wire violation: {w}")
            }
        }
    }
}

/// The recomputed readout, exposed for tests and downstream legs
/// (`QLatticeInv`'s downset check consumes the closure family).
#[derive(Debug, Clone)]
pub struct Readout {
    /// The closure family as bitsets (∅ and arena included).
    pub family: Vec<CellSet>,
    /// Indices into `family` of the join-irreducibles, in the pinned
    /// canonical enumeration (convention 3).
    pub join_irreducibles: Vec<usize>,
    /// Per join-irreducible: its unique lower cover (index into
    /// `family`).
    pub lower_cover: Vec<usize>,
    /// Per join-irreducible: its Morse cell `T(b) = b ∖ b⁻`.
    pub cells: Vec<CellSet>,
}

// ---------------------------------------------------------------------
// Cell bitsets — cheap bitwise combinatorics over linear cell indices
// ---------------------------------------------------------------------

/// A fixed-width bitset over the grid's linear cell indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CellSet {
    words: Vec<u64>,
}

impl CellSet {
    pub fn empty(n_cells: u64) -> CellSet {
        CellSet {
            words: vec![0; usize::try_from(n_cells.div_ceil(64)).expect("budgeted")],
        }
    }

    pub fn from_sorted(n_cells: u64, cells: &[u64]) -> CellSet {
        let mut s = CellSet::empty(n_cells);
        for &c in cells {
            s.words[(c / 64) as usize] |= 1u64 << (c % 64);
        }
        s
    }

    pub fn contains(&self, c: u64) -> bool {
        self.words
            .get((c / 64) as usize)
            .is_some_and(|w| w & (1u64 << (c % 64)) != 0)
    }

    pub fn or(&self, other: &CellSet) -> CellSet {
        CellSet {
            words: self
                .words
                .iter()
                .zip(&other.words)
                .map(|(a, b)| a | b)
                .collect(),
        }
    }

    pub fn and(&self, other: &CellSet) -> CellSet {
        CellSet {
            words: self
                .words
                .iter()
                .zip(&other.words)
                .map(|(a, b)| a & b)
                .collect(),
        }
    }

    pub fn minus(&self, other: &CellSet) -> CellSet {
        CellSet {
            words: self
                .words
                .iter()
                .zip(&other.words)
                .map(|(a, b)| a & !b)
                .collect(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    pub fn is_subset(&self, other: &CellSet) -> bool {
        self.words
            .iter()
            .zip(&other.words)
            .all(|(a, b)| a & !b == 0)
    }

    pub fn intersects(&self, other: &CellSet) -> bool {
        self.words.iter().zip(&other.words).any(|(a, b)| a & b != 0)
    }

    /// Set bits, ascending.
    pub fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        self.words.iter().enumerate().flat_map(|(i, w)| {
            (0..64)
                .filter(move |b| w & (1u64 << b) != 0)
                .map(move |b| i as u64 * 64 + b)
        })
    }
}

/// Lexicographic order on sorted cell-index sequences (prefix-shorter
/// first) — the pinned join-irreducible enumeration order.
fn lex_cmp(a: &CellSet, b: &CellSet) -> Ordering {
    let mut ia = a.iter();
    let mut ib = b.iter();
    loop {
        match (ia.next(), ib.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(x), Some(y)) => match x.cmp(&y) {
                Ordering::Equal => continue,
                o => return o,
            },
        }
    }
}

// ---------------------------------------------------------------------
// The core recompute (pure; refusal = Err(String) for budget/oversize)
// ---------------------------------------------------------------------

fn strictly_increasing(xs: &[u64]) -> bool {
    xs.windows(2).all(|w| w[0] < w[1])
}

/// The canonical boundary-facet enumeration of a block: triples
/// (cell, axis, upper) sorted by (cell, axis, − before +), faces into
/// existing arena cells outside the block only (∂D-faces owe nothing).
fn canonical_facets(grid_counts: &[u64], arena: &CellSet, block: &CellSet) -> Vec<(u64, u64, u64)> {
    let mut out = Vec::new();
    for cell in block.iter() {
        // Decompose per convention 1 (axis 0 fastest).
        let mut rest = cell;
        let mut coords = Vec::with_capacity(grid_counts.len());
        for &n in grid_counts {
            coords.push(rest % n);
            rest /= n;
        }
        for (k, &n) in grid_counts.iter().enumerate() {
            for upper in [false, true] {
                let c_k = coords[k];
                let neighbor_coord = if upper {
                    if c_k + 1 >= n {
                        continue; // grid-boundary face
                    }
                    c_k + 1
                } else {
                    if c_k == 0 {
                        continue; // grid-boundary face
                    }
                    c_k - 1
                };
                // Linearize the neighbour.
                let mut idx = 0u64;
                let mut stride = 1u64;
                for (j, &nj) in grid_counts.iter().enumerate() {
                    let cj = if j == k { neighbor_coord } else { coords[j] };
                    idx += cj * stride;
                    stride *= nj;
                }
                if arena.contains(idx) && !block.contains(idx) {
                    // Degenerate descriptor: group = the axis,
                    // facet 0/1 = lower/upper (the generalized-descriptor reading).
                    out.push((cell, k as u64, u64::from(upper)));
                }
            }
        }
    }
    // Already sorted: cells ascending (block.iter()), groups (=axes)
    // ascending, facet 0 (lower) before 1 (upper).
    out
}

/// The full R1 recompute on a decoded kit. `Err` = refusal (budget /
/// oversize — undecidable at the checker's resources, never a
/// verdict); `Ok(Err(v))` = decided false with the named violation;
/// `Ok(Ok(readout))` = accept, with the recomputed readout.
pub fn check_kit(kit: &MorseKit) -> Result<Result<Readout, KitViolation>, String> {
    // 1. Grid wf.
    if kit.grid.is_empty() {
        return Ok(Err(KitViolation::GridWf { axis: 0 }));
    }
    let mut grid_counts = Vec::with_capacity(kit.grid.len());
    for (axis, cuts) in kit.grid.iter().enumerate() {
        if cuts.len() < 2 {
            return Ok(Err(KitViolation::GridWf { axis }));
        }
        for w in cuts.windows(2) {
            if crate::qq::cmp_q(&w[0], &w[1]) != Ordering::Less {
                return Ok(Err(KitViolation::GridWf { axis }));
            }
        }
        grid_counts.push((cuts.len() - 1) as u64);
    }
    let mut n_cells: u64 = 1;
    for &n in &grid_counts {
        n_cells = n_cells
            .checked_mul(n)
            .filter(|&t| t <= MORSE_MAX_CELLS)
            .ok_or_else(|| format!("grid exceeds the {MORSE_MAX_CELLS}-cell budget"))?;
    }

    // 2. Arena wf.
    if kit.arena.is_empty()
        || !strictly_increasing(&kit.arena)
        || *kit.arena.last().expect("nonempty") >= n_cells
    {
        return Ok(Err(KitViolation::ArenaWf));
    }
    let arena = CellSet::from_sorted(n_cells, &kit.arena);

    // 3. Blocks wf.
    if kit.blocks.len() > MORSE_MAX_BLOCKS {
        return Err(format!(
            "{} declared blocks exceed the {MORSE_MAX_BLOCKS}-block budget",
            kit.blocks.len()
        ));
    }
    let mut block_sets = Vec::with_capacity(kit.blocks.len());
    for (i, b) in kit.blocks.iter().enumerate() {
        if b.cells.is_empty()
            || !strictly_increasing(&b.cells)
            || *b.cells.last().expect("nonempty") >= n_cells
        {
            return Ok(Err(KitViolation::BlockWf { block: i }));
        }
        let set = CellSet::from_sorted(n_cells, &b.cells);
        if !set.is_subset(&arena) || set == arena {
            return Ok(Err(KitViolation::BlockWf { block: i }));
        }
        if block_sets.contains(&set) {
            return Ok(Err(KitViolation::BlockWf { block: i }));
        }
        block_sets.push(set);
    }

    // 4. Facet alignment (blockLatticeWF's class — the adjudicated
    //    split's syntactic residue).
    for (i, b) in kit.blocks.iter().enumerate() {
        let canonical = canonical_facets(&grid_counts, &arena, &block_sets[i]);
        let mut flattened = Vec::new();
        for row in &b.facets {
            if row.cells.is_empty() || !strictly_increasing(&row.cells) {
                return Ok(Err(KitViolation::FacetAlignment {
                    block: i,
                    why: "a facet row's cell-set is empty or unsorted".into(),
                }));
            }
            for &c in &row.cells {
                flattened.push((c, row.group, row.facet));
            }
        }
        // (cell, group, facet) order — the degenerate reading's facet
        // 0/1 keeps convention 2's lower-before-upper for free; a
        // facet index >= 2 on an interval group can never match the
        // canonical enumeration and lands here as misalignment.
        if flattened != canonical {
            return Ok(Err(KitViolation::FacetAlignment {
                block: i,
                why: format!(
                    "flattened rows list {} facet(s), canonical enumeration \
                     has {} — sequences differ",
                    flattened.len(),
                    canonical.len()
                ),
            }));
        }
    }

    // 5. Lattice closure: family = {∅, arena} ∪ blocks, pairwise
    //    ∪/∩-closed ⟹ every closure member carries facet rows.
    let mut family = vec![CellSet::empty(n_cells), arena.clone()];
    family.extend(block_sets.iter().cloned());
    for i in 0..family.len() {
        for j in i + 1..family.len() {
            for (opname, result) in [
                ("union", family[i].or(&family[j])),
                ("meet", family[i].and(&family[j])),
            ] {
                if !family.contains(&result) {
                    return Ok(Err(KitViolation::ClosureHole {
                        why: format!(
                            "the {opname} of members {i} and {j} is not in the \
                             declared family (its facet rows are absent)"
                        ),
                    }));
                }
            }
        }
    }

    // 6. The readout: join-irreducibles (unique lower cover), Morse
    //    cells, cell order — the recomputed enumeration is the sole
    //    authority h is read against.
    let mut irr: Vec<(usize, usize)> = Vec::new(); // (member, cover)
    for (m, x) in family.iter().enumerate() {
        if x.is_empty() {
            continue;
        }
        // Maximal proper predecessors within the family.
        let covers: Vec<usize> = (0..family.len())
            .filter(|&y| family[y] != *x && family[y].is_subset(x))
            .filter(|&y| {
                !(0..family.len()).any(|z| {
                    z != y
                        && family[z] != *x
                        && family[z].is_subset(x)
                        && family[y] != family[z]
                        && family[y].is_subset(&family[z])
                })
            })
            .collect();
        if covers.len() == 1 {
            irr.push((m, covers[0]));
        }
    }
    irr.sort_by(|a, b| lex_cmp(&family[a.0], &family[b.0]));
    let join_irreducibles: Vec<usize> = irr.iter().map(|(m, _)| *m).collect();
    let lower_cover: Vec<usize> = irr.iter().map(|(_, c)| *c).collect();
    let cells: Vec<CellSet> = irr
        .iter()
        .map(|(m, c)| family[*m].minus(&family[*c]))
        .collect();
    let n_j = join_irreducibles.len() as u64;

    // 7. Dag check.
    if kit.dag_vertices > MORSE_MAX_VERTICES {
        return Err(format!(
            "{} dag vertices exceed the {MORSE_MAX_VERTICES}-vertex budget",
            kit.dag_vertices
        ));
    }
    if kit.dag_edges.len() > MORSE_MAX_EDGES {
        return Err(format!(
            "{} dag edges exceed the {MORSE_MAX_EDGES}-edge budget",
            kit.dag_edges.len()
        ));
    }
    let nv = kit.dag_vertices as usize;
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); nv];
    let mut indeg: Vec<u32> = vec![0; nv];
    for &(src, dst) in &kit.dag_edges {
        if src >= kit.dag_vertices || dst >= kit.dag_vertices {
            return Ok(Err(KitViolation::DagWf {
                why: format!("edge ({src}, {dst}) references a vertex out of range"),
            }));
        }
        adj[src as usize].push(dst as u32);
        indeg[dst as usize] += 1;
    }
    // Kahn: acyclicity.
    let mut queue: Vec<usize> = (0..nv).filter(|&v| indeg[v] == 0).collect();
    let mut seen = 0usize;
    while let Some(v) = queue.pop() {
        seen += 1;
        for &w in &adj[v] {
            indeg[w as usize] -= 1;
            if indeg[w as usize] == 0 {
                queue.push(w as usize);
            }
        }
    }
    if seen != nv {
        return Ok(Err(KitViolation::DagWf {
            why: "the edge relation has a cycle".into(),
        }));
    }

    // 8. h totality + functionality on the recomputed enumeration.
    let mut h_of: Vec<Option<Option<u64>>> = vec![None; join_irreducibles.len()];
    for e in &kit.h {
        let (cell, image) = match *e {
            HEntry::Vertex { cell, vertex } => (cell, Some(vertex)),
            HEntry::Transit { cell } => (cell, None),
        };
        if cell >= n_j {
            return Ok(Err(KitViolation::HTotality {
                why: format!(
                    "entry cell index {cell} out of range (the recomputed \
                     readout has {n_j} join-irreducibles)"
                ),
            }));
        }
        if let Some(v) = image {
            if v >= kit.dag_vertices {
                return Ok(Err(KitViolation::HTotality {
                    why: format!("vertex image {v} out of range"),
                }));
            }
        }
        if h_of[cell as usize].replace(image).is_some() {
            return Ok(Err(KitViolation::HTotality {
                why: format!("duplicate entry for cell index {cell}"),
            }));
        }
    }
    let h_of: Vec<Option<u64>> = match h_of
        .iter()
        .enumerate()
        .map(|(i, e)| {
            e.ok_or_else(|| KitViolation::HTotality {
                why: format!("no entry for cell index {i}"),
            })
        })
        .collect::<Result<_, _>>()
    {
        Ok(v) => v,
        Err(v) => return Ok(Err(v)),
    };

    // 9. Fibre convexity in the recomputed cell order (M(v)(a)):
    //    b1 ⊆ b2 ⊆ b3 with h(b1) = h(b3) = v forces h(b2) = v.
    for i1 in 0..join_irreducibles.len() {
        let Some(v) = h_of[i1] else { continue };
        for i3 in 0..join_irreducibles.len() {
            if h_of[i3] != Some(v) {
                continue;
            }
            let (b1, b3) = (
                &family[join_irreducibles[i1]],
                &family[join_irreducibles[i3]],
            );
            if !b1.is_subset(b3) {
                continue;
            }
            for i2 in 0..join_irreducibles.len() {
                let b2 = &family[join_irreducibles[i2]];
                if b1.is_subset(b2) && b2.is_subset(b3) && h_of[i2] != Some(v) {
                    return Ok(Err(KitViolation::FiberConvexity { vertex: v }));
                }
            }
        }
    }

    // 10. Monotonicity on vertex-mapped cells (M(v)(b), convention 4):
    //     b' ⊆ b ⟹ h(b) →* h(b').
    let mut reach_from: HashMap<u64, Vec<bool>> = HashMap::new();
    let mut reaches = |from: u64, to: u64, adj: &[Vec<u32>]| -> bool {
        let r = reach_from.entry(from).or_insert_with(|| {
            let mut seen = vec![false; nv];
            let mut stack = vec![from as usize];
            seen[from as usize] = true;
            while let Some(v) = stack.pop() {
                for &w in &adj[v] {
                    if !seen[w as usize] {
                        seen[w as usize] = true;
                        stack.push(w as usize);
                    }
                }
            }
            seen
        });
        r[to as usize]
    };
    for i in 0..join_irreducibles.len() {
        let Some(vi) = h_of[i] else { continue };
        for j in 0..join_irreducibles.len() {
            let Some(vj) = h_of[j] else { continue };
            let (bj, bi) = (&family[join_irreducibles[j]], &family[join_irreducibles[i]]);
            if bj.is_subset(bi) && !reaches(vi, vj, &adj) {
                return Ok(Err(KitViolation::HMonotonicity {
                    why: format!(
                        "cell {j} <= cell {i} in the recomputed order, but \
                         vertex {vi} does not reach vertex {vj} in the dag"
                    ),
                }));
            }
        }
    }

    // 11. ρ totality + functionality on the dag's vertices.
    let mut rho_of: Vec<Option<&RegionClass>> = vec![None; nv];
    for (v, r) in &kit.rho {
        if *v >= kit.dag_vertices {
            return Ok(Err(KitViolation::RhoWf {
                why: format!("entry vertex {v} out of range"),
            }));
        }
        if rho_of[*v as usize].replace(r).is_some() {
            return Ok(Err(KitViolation::RhoWf {
                why: format!("duplicate entry for vertex {v}"),
            }));
        }
    }
    if let Some(v) = rho_of.iter().position(Option::is_none) {
        return Ok(Err(KitViolation::RhoWf {
            why: format!("no entry for vertex {v}"),
        }));
    }

    // 12. Box-aligned ρ checks: containment + pairwise grid-level
    //     disjointness among the recognized entries (opaque entries
    //     ride the rho_wf Proof rows).
    let aligned: Vec<(u64, CellSet)> = kit
        .rho
        .iter()
        .filter_map(|(v, r)| match r {
            RegionClass::BoxAligned(cells) => Some((*v, CellSet::from_sorted(n_cells, cells))),
            RegionClass::Opaque => None,
        })
        .collect();
    for (v, set) in &aligned {
        if !set.is_subset(&arena) {
            return Ok(Err(KitViolation::RhoContainment { vertex: *v }));
        }
    }
    for i in 0..aligned.len() {
        for j in i + 1..aligned.len() {
            if aligned[i].1.intersects(&aligned[j].1) {
                return Ok(Err(KitViolation::RhoOverlap {
                    v1: aligned[i].0,
                    v2: aligned[j].0,
                }));
            }
        }
    }

    Ok(Ok(Readout {
        family,
        join_irreducibles,
        lower_cover,
        cells,
    }))
}

/// Down-closedness of a cell-index set against a recomputed closure
/// family — the `QLatticeInv` leg of the R1 contract, exported for the
/// sixth-relation fork (the staged R1 kit atom has
/// no `downset` argument, so this cannot ride `qtsl_morse_readout`'s
/// dispatch; it awaits either `qtsl_downset_wf` or a kit-atom delta —
/// a revisable implementation call).
///
/// `downset` is down-closed iff it is a member of the family and every
/// family member below it is... no — the `QLatticeInv` reading:
/// `downset` is a SET OF JOIN-IRREDUCIBLE indices, and
/// down-closedness is in the recomputed cell order: `j' ≤ j ∈ downset
/// ⟹ j' ∈ downset`.
pub fn downset_is_downclosed(readout: &Readout, downset: &[u64]) -> bool {
    let n = readout.join_irreducibles.len() as u64;
    let member: HashSet<u64> = downset.iter().copied().collect();
    if downset.iter().any(|&d| d >= n) {
        return false;
    }
    for &d in downset {
        let bd = &readout.family[readout.join_irreducibles[d as usize]];
        for (j, &mj) in readout.join_irreducibles.iter().enumerate() {
            if readout.family[mj].is_subset(bd) && !member.contains(&(j as u64)) {
                return false;
            }
        }
    }
    true
}

// ---------------------------------------------------------------------
// Row-context decoding (refusals, never guesses)
// ---------------------------------------------------------------------

use crate::error::EvalError;

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

/// Decode budget shared across one eval's walks.
struct Budget(usize);

impl Budget {
    fn step(&mut self, name: &str, index: usize) -> Result<(), EvalError> {
        self.0 += 1;
        if self.0 > MAX_DECODE_STEPS {
            Err(ctx_err(
                name,
                index,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a MorseVocab,
    rows: &'a CertRows,
    budget: Budget,
}

impl<'a> Decoder<'a> {
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

    /// The unique roster-constructor row producing `elem`, against the
    /// roster of the given sort (the `sole_roster_row` discipline).
    fn sole(&mut self, index: usize, sort: Chid, elem: u32) -> Result<&'a CtorRow, EvalError> {
        self.budget.step(self.name, index)?;
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

    /// The unique attribute row `fun(subject) = value`.
    fn sole_attr(
        &mut self,
        index: usize,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<&'a AttrRow, EvalError> {
        self.budget.step(self.name, index)?;
        let mut found: Option<&AttrRow> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {subject} carries multiple `{what}` attribute rows — \
                         ambiguous (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            ctx_err(
                self.name,
                index,
                format!("element {subject} has no `{what}` attribute row — undecidable"),
            )
        })
    }

    fn nat(&self, index: usize, val: &Value, what: &str) -> Result<u64, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Nat literal — malformed rows"),
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

    fn q_lit(&self, index: usize, val: &Value, what: &str) -> Result<Literal, EvalError> {
        if let Value::Lit(l) = val {
            if matches!(l.view(), LiteralView::Q { .. }) {
                return Ok(l.clone());
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Q literal — malformed rows"),
        ))
    }

    /// Walk a cons-list: per node, `on_cons` receives the row's args
    /// and returns the tail's value slot position. Cycle-checked.
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
}

/// Decode + check: the `qtsl_morse_readout` evaluation. Args in wire
/// field order: `dag, h, lat, rho` — all same-body element refs.
pub fn eval_morse(
    name: &str,
    v: &MorseVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let kit = match decode_kit(name, v, args, rows)? {
        Ok(kit) => kit,
        // Wire violations (RGS skew, misaligned generators) are
        // decided content — false, the grid-wf precedent.
        Err(_wire) => return Ok(false),
    };
    match check_kit(&kit) {
        Ok(Ok(_)) => Ok(true),
        Ok(Err(_violation)) => Ok(false),
        Err(budget) => Err(EvalError::CtxArg {
            name: name.into(),
            index: 2,
            why: budget,
        }),
    }
}

/// Decode the four kit arguments into a [`MorseKit`] (exposed so tests
/// can differential the decoder against direct-core runs).
///
/// Verdict strata, `Err(EvalError)` = refusal — row-
/// context undecidability AND out-of-v0-profile complexes (multi-
/// patch, digest chart, n = 0: schema-valid content this checker
/// cannot decide; refuse-not-guess, the profile-refusal contract's
/// oracle-side backstop — the admission gate refuses the same class before
/// storage); `Ok(Err(KitViolation))` = decided wire violation
/// (ill-formed content — RGS skew, generator misalignment, the
/// grid-wf class); `Ok(Ok(kit))` = the decoded kit, its grid the
/// DERIVED per-axis full cut lists (dom endpoints + interior cuts).
#[allow(clippy::type_complexity)]
pub fn decode_kit(
    name: &str,
    v: &MorseVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<Result<MorseKit, KitViolation>, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        budget: Budget(0),
    };

    // --- arg 0: the dag ----------------------------------------------
    let dag_elem = d.elem(0, args[0])?;
    let dag_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qdag_mk))
        .map(|(s, _)| s)
        .expect("qdagMk rostered under its codomain");
    let mk = d.sole(0, dag_sort, dag_elem)?;
    if mk.fun != v.qdag_mk {
        return Err(ctx_err(
            name,
            0,
            "dag element is constructed by a fun other than qdagMk — malformed rows".into(),
        ));
    }
    let [edges_val, vertices_val] = mk.args.as_slice() else {
        return Err(ctx_err(name, 0, "qdagMk row arity mismatch".into()));
    };
    let dag_vertices = d.nat(0, vertices_val, "qdagMk/vertices")?;
    let edges_elem = d.elem(0, edges_val)?;
    let edges_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qde_cons))
        .map(|(s, _)| s)
        .expect("qdeCons rostered");
    let dag_edges = d.walk_list(
        0,
        edges_sort,
        edges_elem,
        v.qde_nil,
        v.qde_cons,
        |d, row| {
            let [dst, src, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 0, "qdeCons row arity mismatch".into()));
            };
            let pair = (d.nat(0, src, "qdeCons/src")?, d.nat(0, dst, "qdeCons/dst")?);
            let tail = d.elem(0, tail)?;
            Ok((pair, tail))
        },
    )?;

    // --- arg 1: h (two cons constructors — its own walk) --------------
    let h_elem = d.elem(1, args[1])?;
    let cm_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qcm_vertex))
        .map(|(s, _)| s)
        .expect("qcmVertex rostered");
    let h = walk_cellmap(&mut d, h_elem, cm_sort)?;

    // --- arg 2: the lattice ------------------------------------------
    let lat_elem = d.elem(2, args[2])?;
    let cx_attr = d.sole_attr(2, lat_elem, v.lat_cx, "QBlockLattice/cx")?;
    let arena_attr = d.sole_attr(2, lat_elem, v.lat_arena, "QBlockLattice/arena")?;
    let blocks_attr = d.sole_attr(2, lat_elem, v.lat_blocks, "QBlockLattice/blocks")?;
    let arena = d.shape(2, &arena_attr.value, "QBlockLattice/arena")?;

    // The unified-arena decode : QGridCx → gridcx::GridCx; then
    // the wire validation on EVERY leaf (decided content — the
    // admission gate's generator-validity-then-profile order, so a
    // skew leaf is a violation even inside an out-of-profile forest);
    // then the v0-profile gate (refusal); then the degenerate
    // derivation ([dom.lo] + interior + [dom.hi] per axis — the
    // retired QGrid payload, which the core's grid-wf check then
    // adjudicates unchanged, cut interiority included).
    let cx_elem = d.elem(2, &cx_attr.value)?;
    let cx = decode_gridcx(&mut d, cx_elem)?;
    for tree_leaf in cx.tree.leaves() {
        if let Err(wire) = crate::gridcx::validate_leaf(cx.dom.len(), tree_leaf) {
            return Ok(Err(KitViolation::GridCxWire(wire)));
        }
    }
    let leaf = match crate::gridcx::v0_leaf(&cx.tree) {
        Ok(leaf) => leaf,
        Err(refusal) => {
            return Err(ctx_err(
                name,
                2,
                format!("outside the v0 checker profile: {refusal}"),
            ))
        }
    };
    let grid = crate::gridcx::degenerate_cuts(&cx.dom, leaf);

    let blocks_elem = d.elem(2, &blocks_attr.value)?;
    let blocklist_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qb_cons))
        .map(|(s, _)| s)
        .expect("qbCons rostered");
    let facetlist_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qf_cons))
        .map(|(s, _)| s)
        .expect("qfCons rostered");
    let block_rows = d.walk_list(
        2,
        blocklist_sort,
        blocks_elem,
        v.qb_nil,
        v.qb_cons,
        |d, row| {
            let [cells, facets, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 2, "qbCons row arity mismatch".into()));
            };
            let cells = d.shape(2, cells, "qbCons/cells")?;
            let facets = d.elem(2, facets)?;
            let tail = d.elem(2, tail)?;
            Ok(((cells, facets), tail))
        },
    )?;
    let mut blocks = Vec::with_capacity(block_rows.len());
    for (cells, facets_elem) in block_rows {
        let facets = d.walk_list(
            2,
            facetlist_sort,
            facets_elem,
            v.qf_nil,
            v.qf_cons,
            |d, row| {
                // Pinned field order: [cells, facet, group, proof, tail].
                let [fcells, facet, group, proof, tail] = row.args.as_slice() else {
                    return Err(ctx_err(d.name, 2, "qfCons row arity mismatch".into()));
                };
                // The proof field is NOMINAL here: presence-shaped. It
                // must be an element ref (its sequent's validity is the
                // premise kit's E1/E3 job, not R1's).
                if !matches!(proof, Value::Ref(_)) {
                    return Err(ctx_err(
                        d.name,
                        2,
                        "qfCons/proof is not an element ref — malformed rows".into(),
                    ));
                }
                let f = FacetRow {
                    group: d.nat(2, group, "qfCons/group")?,
                    facet: d.nat(2, facet, "qfCons/facet")?,
                    cells: d.shape(2, fcells, "qfCons/cells")?,
                };
                let tail = d.elem(2, tail)?;
                Ok((f, tail))
            },
        )?;
        blocks.push(BlockData { cells, facets });
    }

    // --- arg 3: rho ---------------------------------------------------
    let rho_elem = d.elem(3, args[3])?;
    let vrl_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qvr_cons))
        .map(|(s, _)| s)
        .expect("qvrCons rostered");
    let rho_rows = d.walk_list(3, vrl_sort, rho_elem, v.qvr_nil, v.qvr_cons, |d, row| {
        let [region, tail, vertex] = row.args.as_slice() else {
            return Err(ctx_err(d.name, 3, "qvrCons row arity mismatch".into()));
        };
        let vertex = d.nat(3, vertex, "qvrCons/vertex")?;
        let region = d.elem(3, region)?;
        let tail = d.elem(3, tail)?;
        Ok(((vertex, region), tail))
    })?;
    let d_axes = grid.len();
    let grid_counts: Vec<u64> = grid.iter().map(|c| (c.len().max(1) - 1) as u64).collect();
    let mut rho = Vec::with_capacity(rho_rows.len());
    for (vertex, region_elem) in rho_rows {
        let class = classify_region(
            &d.v.region,
            d.rows,
            &mut d.budget.0,
            MAX_DECODE_STEPS,
            region_elem,
            d_axes,
            &grid_counts,
            &grid,
        )
        .map_err(|why| ctx_err(d.name, 3, why))?;
        rho.push((vertex, class));
    }

    Ok(Ok(MorseKit {
        grid,
        arena,
        blocks,
        dag_vertices,
        dag_edges,
        h,
        rho,
    }))
}

/// The cell map's two-cons walk (nil / vertex / transit).
fn walk_cellmap(
    d: &mut Decoder<'_>,
    head_elem: u32,
    cm_sort: Chid,
) -> Result<Vec<HEntry>, EvalError> {
    let mut out = Vec::new();
    let mut visited: HashSet<u32> = HashSet::new();
    let mut cur = head_elem;
    loop {
        if !visited.insert(cur) {
            return Err(ctx_err(
                d.name,
                1,
                format!(
                    "element {cur} recurs along its own list tail (P-ACYCLIC \
                     territory) — refusing"
                ),
            ));
        }
        let row = d.sole(1, cm_sort, cur)?;
        if row.fun == d.v.qcm_nil {
            return Ok(out);
        }
        if row.fun == d.v.qcm_vertex {
            let [cell, tail, vertex] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 1, "qcmVertex row arity mismatch".into()));
            };
            out.push(HEntry::Vertex {
                cell: d.nat(1, cell, "qcmVertex/cell")?,
                vertex: d.nat(1, vertex, "qcmVertex/vertex")?,
            });
            cur = d.elem(1, tail)?;
        } else if row.fun == d.v.qcm_transit {
            let [cell, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 1, "qcmTransit row arity mismatch".into()));
            };
            out.push(HEntry::Transit {
                cell: d.nat(1, cell, "qcmTransit/cell")?,
            });
            cur = d.elem(1, tail)?;
        } else {
            return Err(ctx_err(
                d.name,
                1,
                format!(
                    "element {cur} is constructed by a fun outside the cell map's \
                     nil/vertex/transit constructors — malformed rows"
                ),
            ));
        }
    }
}

// ---------------------------------------------------------------------
// The unified-arena grid-complex decode (the arena unification)
// ---------------------------------------------------------------------

/// Decode a `QGridCx` element into [`crate::gridcx::GridCx`].
/// Structure-only refusals here (the CtxArg pattern); profile and
/// wire adjudication are the caller's (`decode_kit`). The patch tree
/// walks iteratively (post-order, explicit stack): hash-consed
/// subtree SHARING between a split's halves is value-legal and
/// decodes per occurrence, while a cyclic "tree" exhausts the shared
/// node budget and refuses — never diverges.
fn decode_gridcx(d: &mut Decoder<'_>, cx_elem: u32) -> Result<crate::gridcx::GridCx, EvalError> {
    use crate::gridcx::{ChartRef, GridCx, GroupGen, PatchLeaf, PatchTree};

    let sort_of = |chid: Chid, what: &str| -> Chid {
        *d.v.ctors
            .iter()
            .find(|(_, roster)| roster.contains_key(&chid))
            .map(|(s, _)| s)
            .unwrap_or_else(|| panic!("{what} rostered under its codomain"))
    };
    let gridcx_sort = sort_of(d.v.qgc_mk, "qgcMk");
    let patchtree_sort = sort_of(d.v.qpt_leaf, "qptLeaf");
    let chartref_sort = sort_of(d.v.qch_identity, "qchIdentity");
    let genlist_sort = sort_of(d.v.qgl_cons, "qglCons");
    let groupgen_sort = sort_of(d.v.qgen_interval, "qgenInterval");
    let box_sort = sort_of(d.v.box_cons, "boxCons");
    let interval_sort = sort_of(d.v.mk_interval, "mkInterval");
    let ratlist_sort = sort_of(d.v.qrl_cons, "qrlCons");

    // qgcMk [dom, tree].
    let mk = d.sole(2, gridcx_sort, cx_elem)?;
    if mk.fun != d.v.qgc_mk {
        return Err(ctx_err(
            d.name,
            2,
            "grid-complex element is not constructed by qgcMk — malformed rows".into(),
        ));
    }
    let [dom_val, tree_val] = mk.args.as_slice() else {
        return Err(ctx_err(d.name, 2, "qgcMk row arity mismatch".into()));
    };
    let dom_elem = d.elem(2, dom_val)?;
    let tree_root = d.elem(2, tree_val)?;

    // The ambient box: a cons-list of mkInterval [hi, lo] elements.
    let interval_elems = d.walk_list(
        2,
        box_sort,
        dom_elem,
        d.v.box_nil,
        d.v.box_cons,
        |d, row| {
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 2, "boxCons row arity mismatch".into()));
            };
            let head = d.elem(2, head)?;
            let tail = d.elem(2, tail)?;
            Ok((head, tail))
        },
    )?;
    let mut dom = Vec::with_capacity(interval_elems.len());
    for iv_elem in interval_elems {
        let iv = d.sole(2, interval_sort, iv_elem)?;
        if iv.fun != d.v.mk_interval {
            return Err(ctx_err(
                d.name,
                2,
                "box interval element is not constructed by mkInterval — malformed rows".into(),
            ));
        }
        let [hi, lo] = iv.args.as_slice() else {
            return Err(ctx_err(d.name, 2, "mkInterval row arity mismatch".into()));
        };
        let (hi, lo) = (hi.clone(), lo.clone());
        dom.push((
            d.q_lit(2, &lo, "mkInterval/lo")?,
            d.q_lit(2, &hi, "mkInterval/hi")?,
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
                let row = d.sole(2, patchtree_sort, elem)?.clone();
                if row.fun == d.v.qpt_leaf {
                    // qptLeaf [chart, gens, part] — part on the Shape
                    // ground (the RGS partition wire's carrier).
                    let [chart, gens, part] = row.args.as_slice() else {
                        return Err(ctx_err(d.name, 2, "qptLeaf row arity mismatch".into()));
                    };
                    let part = d.shape(2, part, "qptLeaf/part")?;
                    let chart_elem = d.elem(2, chart)?;
                    let chart_row = d.sole(2, chartref_sort, chart_elem)?;
                    let chart = if chart_row.fun == d.v.qch_identity {
                        ChartRef::Identity
                    } else if chart_row.fun == d.v.qch_digest {
                        let [sha] = chart_row.args.as_slice() else {
                            return Err(ctx_err(d.name, 2, "qchDigest row arity mismatch".into()));
                        };
                        ChartRef::Digest {
                            sha256hex: d.str_lit(2, sha, "qchDigest/sha256hex")?,
                        }
                    } else {
                        return Err(ctx_err(
                            d.name,
                            2,
                            "chart element constructed outside the QChartRef roster — \
                             malformed rows"
                                .into(),
                        ));
                    };
                    let gens_elem = d.elem(2, gens)?;
                    let gen_elems = d.walk_list(
                        2,
                        genlist_sort,
                        gens_elem,
                        d.v.qgl_nil,
                        d.v.qgl_cons,
                        |d, row| {
                            let [gen, tail] = row.args.as_slice() else {
                                return Err(ctx_err(
                                    d.name,
                                    2,
                                    "qglCons row arity mismatch".into(),
                                ));
                            };
                            let gen = d.elem(2, gen)?;
                            let tail = d.elem(2, tail)?;
                            Ok((gen, tail))
                        },
                    )?;
                    let mut gens = Vec::with_capacity(gen_elems.len());
                    for gen_elem in gen_elems {
                        let gen_row = d.sole(2, groupgen_sort, gen_elem)?;
                        if gen_row.fun == d.v.qgen_interval {
                            let [cuts_val] = gen_row.args.as_slice() else {
                                return Err(ctx_err(
                                    d.name,
                                    2,
                                    "qgenInterval row arity mismatch".into(),
                                ));
                            };
                            let cuts_elem = d.elem(2, cuts_val)?;
                            let cuts = d.walk_list(
                                2,
                                ratlist_sort,
                                cuts_elem,
                                d.v.qrl_nil,
                                d.v.qrl_cons,
                                |d, row| {
                                    let [head, tail] = row.args.as_slice() else {
                                        return Err(ctx_err(
                                            d.name,
                                            2,
                                            "qrlCons row arity mismatch".into(),
                                        ));
                                    };
                                    let q = d.q_lit(2, head, "qrlCons/head")?;
                                    let tail = d.elem(2, tail)?;
                                    Ok((q, tail))
                                },
                            )?;
                            gens.push(GroupGen::Interval { cuts });
                        } else if gen_row.fun == d.v.qgen_kuhn {
                            // Opaque at this layer (the v0 profile
                            // never reaches a Kuhn cell); args stay
                            // unread, matching the admission gate.
                            gens.push(GroupGen::Kuhn);
                        } else {
                            return Err(ctx_err(
                                d.name,
                                2,
                                "generator element constructed outside the QGroupGen \
                                 roster — malformed rows"
                                    .into(),
                            ));
                        }
                    }
                    built.push(PatchTree::Leaf(PatchLeaf { part, gens, chart }));
                } else if row.fun == d.v.qpt_split {
                    // qptSplit [axis, cut, hi, lo].
                    let [axis, cut, hi, lo] = row.args.as_slice() else {
                        return Err(ctx_err(d.name, 2, "qptSplit row arity mismatch".into()));
                    };
                    let axis = d.nat(2, axis, "qptSplit/axis")?;
                    let cut = d.q_lit(2, cut, "qptSplit/cut")?;
                    let lo = d.elem(2, lo)?;
                    let hi = d.elem(2, hi)?;
                    work.push(Frame::BuildSplit { axis, cut });
                    work.push(Frame::Visit(hi));
                    work.push(Frame::Visit(lo));
                } else {
                    return Err(ctx_err(
                        d.name,
                        2,
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

// ---------------------------------------------------------------------
// The box-aligned ρ recognizer (pinned convention 5)
// ---------------------------------------------------------------------

/// An exact rational with positive denominator (comparisons by
/// cross-multiplication; not necessarily canonical).
#[derive(Debug, Clone)]
struct Qnum {
    num: BigInt,
    den: BigInt,
}

impl Qnum {
    fn from_lit(l: &Literal) -> Qnum {
        let LiteralView::Q { num, den } = l.view() else {
            unreachable!("callers check the Q dtype")
        };
        Qnum {
            num: BigInt::from_signed_bytes_le(num),
            den: BigInt::from(BigUint::from_bytes_le(den)),
        }
    }

    fn cmp(&self, other: &Qnum) -> Ordering {
        // dens > 0, so cross-multiplication preserves order.
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }

    /// self / other (other != 0); den sign normalized positive.
    fn div(&self, other: &Qnum) -> Qnum {
        let mut num = &self.num * &other.den;
        let mut den = &self.den * &other.num;
        if den.sign() == num_bigint::Sign::Minus {
            num = -num;
            den = -den;
        }
        Qnum { num, den }
    }

    fn is_zero(&self) -> bool {
        self.num.sign() == num_bigint::Sign::NoSign
    }

    fn is_negative(&self) -> bool {
        self.num.sign() == num_bigint::Sign::Minus
    }
}

/// One folded coordinate constraint set: per axis, optional lo/hi.
#[derive(Debug, Clone, Default)]
struct AxisBounds {
    lo: Option<Qnum>,
    hi: Option<Qnum>,
}

/// String-refusal twin of [`Decoder::elem`] for the shared recognizer
/// (both gates wrap `Err` in their own refusal type).
fn region_elem_of(rows: &CertRows, val: &Value, what: &str) -> Result<u32, String> {
    match val {
        Value::Ref(r) => rows.local(r).ok_or_else(|| {
            format!("`{what}` is an external element ref — the row context is single-body")
        }),
        _ => Err(format!("`{what}` is not an element ref — malformed rows")),
    }
}

fn region_q_lit(val: &Value, what: &str) -> Result<Literal, String> {
    if let Value::Lit(l) = val {
        if matches!(l.view(), LiteralView::Q { .. }) {
            return Ok(l.clone());
        }
    }
    Err(format!("`{what}` is not a Q literal — malformed rows"))
}

fn region_shape_of(val: &Value, what: &str) -> Result<Vec<u64>, String> {
    if let Value::Lit(l) = val {
        if let LiteralView::Shape(s) = l.view() {
            return Ok(s.iter().collect());
        }
    }
    Err(format!("`{what}` is not a Shape literal — malformed rows"))
}

/// The `sole_roster_row` discipline against an explicit roster:
/// ambiguity and absence both REFUSE (`Err`), never guess.
fn sole_rostered<'a>(
    rows: &'a CertRows,
    roster: &HashSet<Chid>,
    elem: u32,
    steps: &mut usize,
    max_steps: usize,
) -> Result<&'a CtorRow, String> {
    *steps += 1;
    if *steps > max_steps {
        return Err("structural walk exhausted its node budget — pathological rows".into());
    }
    let mut found: Option<&CtorRow> = None;
    for row in rows.producers(elem) {
        if !roster.contains(&row.fun) {
            continue;
        }
        if found.is_some() {
            return Err(format!(
                "element {elem} is produced by multiple constructor rows — \
                 ambiguous structure (P-FUN territory), refusing"
            ));
        }
        found = Some(row);
    }
    found.ok_or_else(|| {
        format!(
            "element {elem} has no constructor row in the context — \
             structure undecidable"
        )
    })
}

/// Classify a ρ region element (convention 5) against a derived grid —
/// THE box-aligned recognizer, one implementation for both gates: the
/// staged R1 decoder ([`decode_kit`]) and the admission gate's
/// mandatory-R1 assembly (the shared-recognizer contract) call exactly this function, so the
/// two gates cannot diverge on which regions face containment/overlap
/// checks (review finding's parity bar). Refusals (`Err`) only where the
/// row context cannot decide structure or the budget exhausts; every
/// recognized-or-not verdict is definite. `steps` accumulates into the
/// caller's decode budget (refusal past `max_steps`).
#[allow(clippy::too_many_arguments)]
pub fn classify_region(
    rv: &RegionVocab,
    rows: &CertRows,
    steps: &mut usize,
    max_steps: usize,
    region_elem: u32,
    d_axes: usize,
    grid_counts: &[u64],
    grid: &[Vec<Literal>],
) -> Result<RegionClass, String> {
    // Collect atoms by iterative conjunction-tree walk.
    let mut bounds: Vec<AxisBounds> = (0..d_axes).map(|_| AxisBounds::default()).collect();
    let mut stack = vec![region_elem];
    let mut visited: HashSet<u32> = HashSet::new();
    while let Some(e) = stack.pop() {
        *steps += 1;
        if *steps > max_steps {
            return Err("structural walk exhausted its node budget — pathological rows".into());
        }
        if !visited.insert(e) {
            // Shared subtrees are legal (interning); a CYCLE would
            // revisit along the walk of its own ancestors — the
            // visited set breaks both, and sharing cannot change the
            // fold (bounds are idempotent under max/min).
            continue;
        }
        let row = sole_rostered(rows, &rv.statef_roster, e, steps, max_steps)?;
        if row.fun == rv.s_true {
            continue;
        } else if row.fun == rv.s_and {
            let [list] = row.args.as_slice() else {
                return Err("SAnd row arity mismatch".into());
            };
            // The SFList walk (cycle-checked within this walk; a shared
            // tail across walks is hash-consing-legal and fine).
            let mut list_visited: HashSet<u32> = HashSet::new();
            let mut cur = region_elem_of(rows, list, "SAnd/list")?;
            loop {
                if !list_visited.insert(cur) {
                    return Err(format!(
                        "element {cur} recurs along its own SFList tail \
                         (P-ACYCLIC territory) — refusing"
                    ));
                }
                let lrow = sole_rostered(rows, &rv.sflist_roster, cur, steps, max_steps)?;
                if lrow.fun == rv.sl_nil {
                    break;
                }
                if lrow.fun != rv.sl_cons {
                    return Err(format!(
                        "element {cur} is constructed outside the expected SFList \
                         nil/cons pair"
                    ));
                }
                let [head, tail] = lrow.args.as_slice() else {
                    return Err("slCons row arity mismatch".into());
                };
                stack.push(region_elem_of(rows, head, "slCons/head")?);
                cur = region_elem_of(rows, tail, "slCons/tail")?;
            }
        } else if row.fun == rv.s_atom_le || row.fun == rv.s_atom_ge {
            let is_le = row.fun == rv.s_atom_le;
            let [c, arg] = row.args.as_slice() else {
                return Err("SAtom row arity mismatch".into());
            };
            let c = Qnum::from_lit(&region_q_lit(c, "SAtom/c")?);
            let mut poly_elem = region_elem_of(rows, arg, "SAtom/arg")?;
            // Post-grid closures interpose the StateObservable hop:
            // only the `oPoly` injection has a polynomial reading —
            // any other observable classifies Opaque (the recognizer's
            // contract is TOTAL classification, never a refusal on a
            // definite non-box shape).
            if rv.o_poly.is_some() {
                let orow = sole_rostered(rows, &rv.stateobs_roster, poly_elem, steps, max_steps)?;
                if Some(orow.fun) != rv.o_poly {
                    return Ok(RegionClass::Opaque);
                }
                let [p] = orow.args.as_slice() else {
                    return Err("oPoly row arity mismatch".into());
                };
                poly_elem = region_elem_of(rows, p, "oPoly/poly")?;
            }
            // The poly must be a single coordinate monomial c'·x_k.
            let term = sole_rostered(rows, &rv.poly_roster, poly_elem, steps, max_steps)?;
            if term.fun != rv.p_term {
                return Ok(RegionClass::Opaque);
            }
            let [coeff, expts, tail] = term.args.as_slice() else {
                return Err("pTerm row arity mismatch".into());
            };
            let coeff = Qnum::from_lit(&region_q_lit(coeff, "pTerm/coeff")?);
            if coeff.is_zero() {
                return Ok(RegionClass::Opaque);
            }
            let expts = region_shape_of(expts, "pTerm/expts")?;
            let tail_elem = region_elem_of(rows, tail, "pTerm/tail")?;
            let tail_row = sole_rostered(rows, &rv.poly_roster, tail_elem, steps, max_steps)?;
            if tail_row.fun != rv.p_zero {
                return Ok(RegionClass::Opaque);
            }
            let mut axis: Option<usize> = None;
            for (k, &e) in expts.iter().enumerate() {
                match e {
                    0 => {}
                    1 if axis.is_none() => axis = Some(k),
                    _ => return Ok(RegionClass::Opaque),
                }
            }
            let Some(k) = axis.filter(|k| *k < d_axes) else {
                return Ok(RegionClass::Opaque);
            };
            // c'·x_k ≤ c  ⟺  x_k ≤ c/c' (c' > 0) / x_k ≥ c/c' (c' < 0);
            // GE mirrors.
            let bound = c.div(&coeff);
            let upper_bound = is_le != coeff.is_negative();
            let slot = &mut bounds[k];
            if upper_bound {
                slot.hi = Some(match slot.hi.take() {
                    Some(old) if old.cmp(&bound) == Ordering::Less => old,
                    _ => bound,
                });
            } else {
                slot.lo = Some(match slot.lo.take() {
                    Some(old) if old.cmp(&bound) == Ordering::Greater => old,
                    _ => bound,
                });
            }
        } else {
            // Any other StateF constructor (SOr, SNot, SProb, SFalse,
            // …): outside the box-aligned class — the Proof-row lane.
            return Ok(RegionClass::Opaque);
        }
    }

    // Every axis fully bounded, every bound a grid cut — else opaque.
    if d_axes == 0 {
        return Ok(RegionClass::Opaque);
    }
    let mut per_axis_ranges: Vec<(u64, u64)> = Vec::with_capacity(d_axes);
    for (k, b) in bounds.iter().enumerate() {
        let (Some(lo), Some(hi)) = (&b.lo, &b.hi) else {
            return Ok(RegionClass::Opaque);
        };
        let cut_index = |q: &Qnum| -> Option<u64> {
            grid[k]
                .iter()
                .position(|cut| Qnum::from_lit(cut).cmp(q) == Ordering::Equal)
                .map(|i| i as u64)
        };
        let (Some(i_lo), Some(i_hi)) = (cut_index(lo), cut_index(hi)) else {
            return Ok(RegionClass::Opaque);
        };
        // Cells on axis k: the half-open cut-index range [i_lo, i_hi)
        // (empty when i_lo ≥ i_hi — degenerate/empty boxes, the
        // regularized reading).
        per_axis_ranges.push((i_lo, i_hi));
    }
    if per_axis_ranges.iter().any(|(lo, hi)| lo >= hi) {
        return Ok(RegionClass::BoxAligned(Vec::new()));
    }
    // Enumerate the cellset by odometer (axis 0 fastest).
    let mut cells = Vec::new();
    let mut idx: Vec<u64> = per_axis_ranges.iter().map(|(lo, _)| *lo).collect();
    'outer: loop {
        let mut linear = 0u64;
        let mut stride = 1u64;
        for k in 0..d_axes {
            linear += idx[k] * stride;
            stride *= grid_counts[k];
        }
        cells.push(linear);
        for k in 0..d_axes {
            idx[k] += 1;
            if idx[k] < per_axis_ranges[k].1 {
                continue 'outer;
            }
            idx[k] = per_axis_ranges[k].0;
        }
        break;
    }
    cells.sort_unstable();
    Ok(RegionClass::BoxAligned(cells))
}

// ---------------------------------------------------------------------
// Core unit tests (the E1 worked example is the anchor; the rows-path
// differential + mutants live in tests/morse_readout.rs)
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn q(num: i64, den: u64) -> Literal {
        Literal::q(num, den).expect("canonical q")
    }

    /// The E1 worked-example lattice: grid x {0, 1/4, 1}, y
    /// {0, 1/3, 1}; blocks m={3}, a={1,3}, b={2,3}, j={1,2,3};
    /// arena = all four cells. (Axis-0-fastest: cell (cx,cy) =
    /// cx + 2·cy.)
    fn e1_kit() -> MorseKit {
        MorseKit {
            grid: vec![
                vec![q(0, 1), q(1, 4), q(1, 1)],
                vec![q(0, 1), q(1, 3), q(1, 1)],
            ],
            arena: vec![0, 1, 2, 3],
            blocks: vec![
                BlockData {
                    cells: vec![3],
                    facets: vec![
                        FacetRow {
                            group: 0,
                            facet: 0,
                            cells: vec![3],
                        },
                        FacetRow {
                            group: 1,
                            facet: 0,
                            cells: vec![3],
                        },
                    ],
                },
                BlockData {
                    cells: vec![1, 3],
                    facets: vec![FacetRow {
                        group: 0,
                        facet: 0,
                        cells: vec![1, 3],
                    }],
                },
                BlockData {
                    cells: vec![2, 3],
                    facets: vec![FacetRow {
                        group: 1,
                        facet: 0,
                        cells: vec![2, 3],
                    }],
                },
                BlockData {
                    cells: vec![1, 2, 3],
                    facets: vec![
                        FacetRow {
                            group: 0,
                            facet: 0,
                            cells: vec![1],
                        },
                        FacetRow {
                            group: 1,
                            facet: 0,
                            cells: vec![2],
                        },
                    ],
                },
            ],
            // Diamond: v00=0 source, v10=1, v01=2, v11=3 sink.
            dag_vertices: 4,
            dag_edges: vec![(0, 1), (0, 2), (1, 3), (2, 3)],
            // Canonical J enumeration (lex): 0=D=[0,1,2,3], 1=a=[1,3],
            // 2=b=[2,3], 3=m=[3].
            h: vec![
                HEntry::Vertex { cell: 0, vertex: 0 },
                HEntry::Vertex { cell: 1, vertex: 1 },
                HEntry::Vertex { cell: 2, vertex: 2 },
                HEntry::Vertex { cell: 3, vertex: 3 },
            ],
            rho: vec![
                (0, RegionClass::BoxAligned(vec![0])),
                (1, RegionClass::BoxAligned(vec![1])),
                (2, RegionClass::BoxAligned(vec![2])),
                (3, RegionClass::BoxAligned(vec![3])),
            ],
        }
    }

    #[test]
    fn e1_accepts_with_the_worked_example_readout() {
        let r = check_kit(&e1_kit())
            .expect("within budget")
            .expect("accepts");
        // J = {D, a, b, m} in the pinned enumeration; T-cells match
        // the worked example: T(D)={0}, T(a)={1}, T(b)={2}, T(m)={3}.
        assert_eq!(r.join_irreducibles.len(), 4);
        let t: Vec<Vec<u64>> = r.cells.iter().map(|c| c.iter().collect()).collect();
        assert_eq!(t, vec![vec![0], vec![1], vec![2], vec![3]]);
        // Lower covers: D⁻ = j, a⁻ = m, b⁻ = m, m⁻ = ∅.
        let covers: Vec<Vec<u64>> = r
            .lower_cover
            .iter()
            .map(|&c| r.family[c].iter().collect())
            .collect();
        assert_eq!(
            covers,
            vec![vec![1, 2, 3], vec![3], vec![3], Vec::<u64>::new()]
        );
    }

    #[test]
    fn e1_named_mutants_reject_with_their_reasons() {
        // Misordered readout: h stated against a wrong enumeration
        // (D and m swapped) — monotonicity is the recompute's witness.
        let mut k = e1_kit();
        k.h = vec![
            HEntry::Vertex { cell: 0, vertex: 3 },
            HEntry::Vertex { cell: 1, vertex: 1 },
            HEntry::Vertex { cell: 2, vertex: 2 },
            HEntry::Vertex { cell: 3, vertex: 0 },
        ];
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::HMonotonicity { .. }
        ));

        // Non-convex fibre: m and D share a vertex, a between them
        // does not.
        let mut k = e1_kit();
        k.h = vec![
            HEntry::Vertex { cell: 0, vertex: 0 },
            HEntry::Vertex { cell: 1, vertex: 1 },
            HEntry::Vertex { cell: 2, vertex: 2 },
            HEntry::Vertex { cell: 3, vertex: 0 },
        ];
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::FiberConvexity { vertex: 0 }
        ));

        // Cyclic dag.
        let mut k = e1_kit();
        k.dag_edges.push((3, 0));
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::DagWf { .. }
        ));

        // Closure hole: drop the declared join j = a ∪ b.
        let mut k = e1_kit();
        k.blocks.remove(3);
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::ClosureHole { .. }
        ));

        // Facet misalignment: swap block j's two facet rows.
        let mut k = e1_kit();
        k.blocks[3].facets.swap(0, 1);
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::FacetAlignment { block: 3, .. }
        ));

        // Facet omission: drop one of m's facet rows.
        let mut k = e1_kit();
        k.blocks[0].facets.pop();
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::FacetAlignment { block: 0, .. }
        ));

        // ρ overlap (box-aligned).
        let mut k = e1_kit();
        k.rho[0] = (0, RegionClass::BoxAligned(vec![0, 1]));
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::RhoOverlap { .. }
        ));

        // ρ missing a vertex.
        let mut k = e1_kit();
        k.rho.pop();
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::RhoWf { .. }
        ));

        // h missing an entry.
        let mut k = e1_kit();
        k.h.pop();
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::HTotality { .. }
        ));

        // Grid: non-increasing cuts.
        let mut k = e1_kit();
        k.grid[0] = vec![q(0, 1), q(1, 1), q(1, 4)];
        assert!(matches!(
            check_kit(&k).unwrap().unwrap_err(),
            KitViolation::GridWf { axis: 0 }
        ));
    }

    #[test]
    fn opaque_rho_rides_the_proof_lane() {
        // An opaque region participates in totality but is exempt from
        // the box-aligned disjointness/containment recompute.
        let mut k = e1_kit();
        k.rho[1] = (1, RegionClass::Opaque);
        assert!(check_kit(&k).unwrap().is_ok());
    }

    #[test]
    fn downset_check_matches_the_order() {
        let r = check_kit(&e1_kit()).unwrap().unwrap();
        // Enumeration: 0=D, 1=a, 2=b, 3=m; order m < a,b < D.
        assert!(downset_is_downclosed(&r, &[3])); // {m}
        assert!(downset_is_downclosed(&r, &[1, 3])); // {a, m}
        assert!(!downset_is_downclosed(&r, &[1])); // {a} misses m
        assert!(!downset_is_downclosed(&r, &[0, 1, 2])); // misses m
        assert!(downset_is_downclosed(&r, &[0, 1, 2, 3]));
        assert!(!downset_is_downclosed(&r, &[7])); // out of range
    }

    #[test]
    fn degenerate_lattice_still_reads_out() {
        // No blocks: family = {∅, D}; J = {D} with cover ∅; T(D) = D.
        let k = MorseKit {
            grid: vec![vec![q(0, 1), q(1, 1)]],
            arena: vec![0],
            blocks: vec![],
            dag_vertices: 1,
            dag_edges: vec![],
            h: vec![HEntry::Vertex { cell: 0, vertex: 0 }],
            rho: vec![(0, RegionClass::BoxAligned(vec![0]))],
        };
        let r = check_kit(&k).unwrap().unwrap();
        assert_eq!(r.join_irreducibles.len(), 1);
        assert_eq!(r.cells[0].iter().collect::<Vec<_>>(), vec![0]);
    }
}
