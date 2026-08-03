//! Atomic certificate admission.
//!
//! Design basis: the second revision of the unified-arena design
//! ("rev 2" throughout these docs), whose v0 capability profile
//! fixes exactly what this gate admits — the certificate-object
//! loading leg that earlier revisions named as future work.
//!
//! **The frozen pipeline** (rev 2's admission-gate ordering, extended
//! by the review repairs — the interface the chase and the
//! vocabulary staging build against; a change that needs to break it
//! is a named event, never a drift):
//!
//! 1. **decode** — the certificate object's rows into pure data
//!    (refuse-not-guess: ambiguity, cycles, exhausted budgets refuse),
//!    INCLUDING the v0 object-graph linkage chain
//!    `QMorseDischarge/proof → QProof/concludes → QMorse/judgment`
//!    binding the selected records (review finding);
//! 2. **closure + schema** — 2a (review finding): the certificate-OBJECT
//!    boundary is the row boundary: every op in the body must be a row
//!    the decode consumed (a constructor row of a walked element, or
//!    an attribute row of a selected record). Unowned rows — an
//!    unattached second complex, stray constructor rows, rows with
//!    external subjects, non-row ops — refuse the WHOLE bundle;
//!    nothing piggybacks into visibility on a green primary object.
//!    Then 2b (review finding): every owned row conforms to its fun's
//!    STAGED signature — arity, cell kinds, codomain ([`check_schema`])
//!    — and constructor production is globally unique per element
//!    across roster families (P-FUN established at the gate, not
//!    assumed from a projection that does not exist pre-byte);
//! 3. **profile** — generator validity (version-independent), then the
//!    *versioned* capability profile ([`ProfileVersion`] — an explicit
//!    version on the admission path; widening is an enum-variant event,
//!    never a drift);
//! 4. **mandatory R1** — the Morse-readout recompute ([`check_kit`])
//!    runs at admission, not at some optional later evaluation;
//! 5. **chase** — [`ArenaEquationChase`] checks the
//!    staged `ax/qmorsedischarge/arena` equation, and additionally
//!    requires at least one MATCHED premise instance (vacuous
//!    satisfaction is not admissible at v0 — belt to step 1's
//!    suspenders). The [`AdmissionChase`] trait seam survives for the
//!    non-visibility diagnostic surface ([`probe_admission`]) only;
//! 6. **visibility** — only a fully-green bundle constructs an
//!    [`AdmittedCert`]; refusal at ANY step admits nothing (no row of
//!    the bundle reaches any reader surface — [`CertStore`] is the
//!    reference reader).
//!
//! **The production door is policy-fixed** (review finding): the
//! visibility-minting surfaces — [`admit_certificate`] and
//! [`CertStore::admit`] — take NO profile version and NO chase
//! argument; they pin [`ProfileVersion::V0`] and construct the
//! [`ArenaEquationChase`] themselves from the vocabulary (sealed: no
//! caller-implemented hook can observe a decoded bundle on any path
//! that mints visibility — the review ruling). Arbitrary
//! profile/chase combinations remain exercisable through
//! [`probe_admission`], which runs the full pipeline but returns only
//! a verdict — it cannot construct an [`AdmittedCert`].
//!
//! **The v0 profile predicate, exact strictness** (this statement is
//! the checker twin of the Lean generator-validity
//! statement — the two artefacts are written independently so they can
//! disagree if either is wrong):
//!
//! Version-independent generator validity, over the decoded
//! `QGridCx { dom, tree }` with `n = dom.len()`:
//!
//! - **GV1 (domain)**: `n >= 1`, and for every axis `k`:
//!   `dom[k].lo < dom[k].hi` — STRICT (exact-ℚ; degenerate and
//!   zero-dimensional domains refuse; rev 2 pins `n = 0` as refused).
//! - **GV2 (split cuts — the endpoint-cut interiority fix, a
//!   review-caught surprise)**: for every `qptSplit(axis, cut, hi, lo)` node
//!   (the staged field order — alphabetical-fields idiom),
//!   with `R` the node's sub-box derived by folding `dom` through the
//!   split path from the root: `R.lo[axis] < cut < R.hi[axis]`, BOTH
//!   comparisons STRICT in exact ℚ. Equality with either endpoint
//!   refuses. (The wire type alone admits `lo <= cut <= hi`; strict
//!   interiority is generator VALIDITY, checked here at admission.)
//! - **GV3 (partition wire)**: each leaf's partition is a Nat-list of
//!   length `n` in canonical restricted-growth form:
//!   `part[0] = 0` and `part[k] <= 1 + max(part[0..k])`.
//! - **GV4 (generator alignment)**: each leaf's `QGenList` has length
//!   exactly `g = 1 + max(part)`.
//! - **GV5 (kind-vs-fibre gate + Kuhn payload)**: group `j`'s fibre
//!   size `f_j = |{k : part[k] = j}|` gates the generator kind:
//!   `qgenInterval` iff `f_j = 1`; `qgenKuhn` iff `f_j ∈ {2, 3}`.
//!   A `qgenKuhn [res, splits]` payload additionally satisfies the
//!   Kuhn-payload admission obligations (review finding): `len(res) = f_j`, every
//!   `res` entry ≥ 1, `len(splits) = Π res`.
//! - **GV6 (interval cuts)**: for a singleton group `{k}` with
//!   `qgenInterval(cuts)` on a leaf whose derived sub-box is `R`:
//!   `R.lo[k] < c_1 < c_2 < … < c_m < R.hi[k]` — strictly increasing
//!   AND strictly interior, ALL comparisons strict (the empty list is
//!   vacuously valid: a one-cell axis).
//!
//! Then the versioned gate. **v0**: the tree is a single `qptLeaf`;
//! every group is a singleton (equivalently `part = [0, 1, …, n−1]`);
//! the chart is `qchIdentity`; every `Shape` payload over the derived
//! cell enumeration (arena, block cells, facet cells) is within the
//! derived cell count — i.e. exactly today's grids in the new clothes.
//!
//! **Cut-list convention (INTERIOR-ONLY)**: `qgenInterval`'s cuts are
//! the strictly-interior cuts; the axis interval's endpoints come from
//! the derived sub-box, so per-axis cell count is `cuts.len() + 1`.
//! Chosen on the derive-don't-store posture (rev 2's vocabulary-delta preamble:
//! serialize the generator, derive the presentation, skew
//! unrepresentable — stored endpoints that must equal derived values
//! would be checkable-redundant skew). The vocabulary staging landed
//! this interior-only reading.
//!
//! **Integration seams (named; the vocabulary staging has LANDED)**:
//! - [`ArenaVocab::from_indices`] pins the rev 2 constructor names from
//!   staged theories; since the staged vocabulary landed it resolves
//!   against the reference corpus, and the staged-binding test requires
//!   BOTH the vocabulary and the chase to construct (review finding).
//!   Synthetic-chid injection remains a test seam where
//!   identity-independence is itself the point.
//! - ρ regions classify at admission through the SAME box-aligned
//!   recognizer the staged R1 decoder runs
//!   ([`crate::morse::classify_region`], the shared-recognizer contract — one classification
//!   semantics, two gates; review finding): box-aligned regions face their
//!   containment/overlap checks inside the mandatory R1 step, and only
//!   genuinely-opaque regions ride their `rho_wf` Proof rows (the
//!   pinned Opaque classification — the proof-row path itself rides the
//!   E1/E3 premise kits, outside R1 at both gates alike). Closure-side
//!   (the ρ-subtree ownership contract, from review): region
//!   subtrees are OWNED by sort-tracked
//!   reachability over the recognizer's roster — rostered-but-unknown
//!   StateF constructors (`SOr` kin) own their single row without
//!   recursion, so a STRUCTURED opaque region's subtree rows refuse at
//!   closure until `rho_wf` lands its own closure rules (a
//!   named widening event; any closure/recognizer divergence is an
//!   extra refusal, never an extra admission).
//! - The facet descriptor decodes the rev 2 GENERALIZED form
//!   `(group, facet)` with the degenerate reading (singleton group g =
//!   the axis; facet 0/1 = lower/upper).

use crate::morse::{
    check_kit, classify_region, BlockData, FacetRow, HEntry, KitViolation, MorseKit, RegionVocab,
};
use crate::rowctx::{AttrRow, CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// Decode budget: refusal beyond, never divergence (P-ACYCLIC posture,
/// same constant class as the R1 oracle's).
const MAX_ADMISSION_DECODE_STEPS: usize = 1 << 20;
/// Patch-tree depth budget (path length, not node count).
const MAX_TREE_DEPTH: usize = 1 << 10;

// ---------------------------------------------------------------------
// Profile versions (the explicit version on the admission path)
// ---------------------------------------------------------------------

/// The admission profile version. Widening is an EVENT: a new variant
/// here plus its predicate arm, never a silent behaviour change on an
/// existing tag (rev 2: "a new profile version and a reader-gate
/// widening event").
///
/// `V0` is the only version the visibility surfaces can cite AT ALL:
/// [`admit_certificate`] and [`CertStore::admit`] pin it internally
/// and take no version argument (review finding).
/// `V1WidenedChartForTest` exists as the widening-MECHANISM precedent
/// exercised by the versioned-reader acceptance test: it admits the
/// reserved digest-chart constructor on an otherwise-degenerate
/// complex (chart changes never re-index cells — rev 2's sigma
/// section — so the R1 recompute is identical). It is reachable ONLY
/// through the non-visibility [`probe_admission`] surface. The
/// *actual* future widenings (multi-patch, mixed generators) arrive as
/// their own variants WITH their recompute machinery (a named successor) and
/// their own production-door version event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProfileVersion {
    V0,
    V1WidenedChartForTest,
}

impl ProfileVersion {
    /// The explicit wire tag carried on the admission path.
    pub fn tag(self) -> u32 {
        match self {
            ProfileVersion::V0 => 0,
            ProfileVersion::V1WidenedChartForTest => 1,
        }
    }
}

// ---------------------------------------------------------------------
// The pinned constructor vocabulary (rev 2 delta + retained kit sorts)
// ---------------------------------------------------------------------

/// One fun's staged signature, as the admission gate validates rows
/// against it (review finding): argument sorts in wire order (bytewise
/// field-name order — the theory loader pre-sorts) and the codomain.
#[derive(Debug, Clone)]
pub struct FunSchema {
    pub domain: DomainSig,
    pub codomain: Option<SortKey>,
}

/// The staged-signature table the admission gate's schema step (step
/// 2b) checks every owned row against (review finding).
/// [`ArenaVocab::from_indices`] populates it from every non-relational
/// declaration in the swept indices — binding the `DomainSig` data the
/// pre-r3 resolver discarded; synthetic test vocabularies must supply
/// an equivalent table (a fun with no entry refuses fail-closed).
#[derive(Debug, Clone, Default)]
pub struct VocabSchema {
    pub funs: HashMap<Chid, FunSchema>,
}

/// The admission gate's constructor vocabulary. Production pins it by
/// name from staged theory indices ([`ArenaVocab::from_indices`] — the
/// vocabulary integration seam); tests inject chids directly (the fields are
/// public by design: the gate's logic is identity-driven, never
/// name-driven, per C-ORACLE — identity-driven, but since the staged-schema repair
/// always schema-checked: the injected identities carry their own
/// [`VocabSchema`]).
#[derive(Debug, Clone)]
pub struct ArenaVocab {
    // --- the rev 2 unified-arena constructors --------------------------
    /// `qgcMk : [dom: Box, tree: QPatchTree] -> QGridCx`
    pub qgc_mk: Chid,
    /// `qptLeaf : [chart: QChartRef, gens: QGenList, part: Shape-ground] -> QPatchTree`
    /// (bytewise field order; the partition rides a finite-Nat-sequence
    /// ground literal — order-preserving, duplicates representable).
    pub qpt_leaf: Chid,
    /// `qptSplit : [axis: Nat, cut: Q, hi: QPatchTree, lo: QPatchTree] -> QPatchTree`
    pub qpt_split: Chid,
    /// `qglNil : QGenList`
    pub qgl_nil: Chid,
    /// `qglCons : [gen: QGroupGen, tail: QGenList] -> QGenList`
    pub qgl_cons: Chid,
    /// `qgenInterval : [cuts: QRatList] -> QGroupGen`
    pub qgen_interval: Chid,
    /// `qgenKuhn : [res: QNatList, splits: QSplitList] -> QGroupGen` —
    /// the staged field layout (decoded and validated at admission,
    /// never carried opaquely).
    pub qgen_kuhn: Chid,
    /// `qnlNil : QNatList`
    pub qnl_nil: Chid,
    /// `qnlCons : [head: Nat, tail: QNatList] -> QNatList`
    pub qnl_cons: Chid,
    /// `qstLeaf : QSplitTree`
    pub qst_leaf: Chid,
    /// `qstSplit : [hi: QSplitTree, lo: QSplitTree] -> QSplitTree`
    /// (bytewise field order; traversal is lo-before-hi — a separate
    /// semantic fact, not derivable from the field order).
    pub qst_split: Chid,
    /// `qslNil : QSplitList`
    pub qsl_nil: Chid,
    /// `qslCons : [head: QSplitTree, tail: QSplitList] -> QSplitList`
    pub qsl_cons: Chid,
    /// `qchIdentity : QChartRef`
    pub qch_identity: Chid,
    /// The reserved digest chart constructor (name provisional until
    /// the vocabulary staging lands it).
    pub qch_digest: Chid,
    /// `qarMk : [cells: Shape, cx: QGridCx] -> QArena` — the unified
    /// arena value pair (the chase equation's object).
    pub qar_mk: Chid,

    // --- retained Qtsl box constructors --------------------------------
    /// `boxNil : Box`
    pub box_nil: Chid,
    /// `boxCons : [head: Interval, tail: Box] -> Box`
    pub box_cons: Chid,
    /// `mkInterval : [hi: Q, lo: Q] -> Interval`
    pub mk_interval: Chid,

    // --- retained kit constructors (unchanged from the staged theory) --
    pub qdag_mk: Chid,
    pub qde_nil: Chid,
    pub qde_cons: Chid,
    pub qcm_nil: Chid,
    pub qcm_vertex: Chid,
    pub qcm_transit: Chid,
    pub qvr_nil: Chid,
    pub qvr_cons: Chid,
    pub qrl_nil: Chid,
    pub qrl_cons: Chid,
    pub qb_nil: Chid,
    pub qb_cons: Chid,
    pub qf_nil: Chid,
    /// The rev 2 GENERALIZED facet cons:
    /// `qfCons : [cells: Shape, facet: Nat, group: Nat, proof: Proof, tail: QFacetList] -> QFacetList`
    /// (degenerate reading at v0: group = axis, facet 0/1 = lower/upper).
    pub qf_cons: Chid,

    // --- entity-attribute funs -----------------------------------------
    /// `QBlockLattice/cx : QBlockLattice -> QGridCx` (rev 2 retirement:
    /// was `/grid : QGrid`).
    pub lat_cx: Chid,
    pub lat_arena: Chid,
    pub lat_blocks: Chid,
    pub morse_judgment: Chid,
    pub morse_graph: Chid,
    pub morse_rho: Chid,
    /// `QMorse/arena : QMorse -> QArena` (rev 2 retirement: was
    /// `-> QRegionAtom`).
    pub morse_arena: Chid,
    pub dis_proof: Chid,
    pub dis_lattice: Chid,
    pub dis_h: Chid,
    /// `QProof/concludes : QProof -> QJudgment` — the linkage chain's
    /// middle identity. Admission-owned since the v0 object grammar
    /// requires the chain (review finding); previously resolved only
    /// by the chase consumer.
    pub concludes: Chid,

    // --- the ρ recognizer's spec-surface slice (the shared-recognizer contract) -------------
    /// The box-aligned region recognizer's vocabulary — chids + sort
    /// rosters, shared BY TYPE with the staged R1 decoder so the two
    /// gates classify identically (review finding; the recognizer itself
    /// is [`crate::morse::classify_region`]).
    pub region: RegionVocab,

    // --- the staged-signature table (review finding) -----------------------
    /// Per-fun staged signatures, checked by the schema step against
    /// every row of the body (arity, cell kinds, codomain, and — via
    /// the producer census — global P-FUN uniqueness across roster
    /// families).
    pub schema: VocabSchema,
}

impl ArenaVocab {
    /// Pin the vocabulary by name across staged theory indices — the
    /// vocabulary integration seam. Until the rev 2 vocabulary lands in
    /// the staged theory this returns `Err` naming the first missing
    /// constructor (correct pre-staging behaviour: nothing can be admitted
    /// against a vocabulary that is not staged).
    pub fn from_indices(indices: &[&TheoryIndex]) -> Result<ArenaVocab, String> {
        let find = |name: &str| -> Result<Chid, String> {
            for index in indices {
                if let Some(d) = index.fun(name) {
                    if d.relational {
                        return Err(format!("`{name}` is relational, not a constructor"));
                    }
                    return Ok(d.chid);
                }
            }
            Err(format!("no `{name}` constructor among the swept revisions"))
        };

        // The ρ recognizer's slice (the shared-recognizer contract): pin the eight
        // spec-surface constructors + build the full producer rosters
        // of their three sorts, so admission's classification runs the
        // recognizer against the SAME roster boundary the staged R1
        // decoder derives (definite-Opaque vs undecidable-refuse).
        let find_decl = |name: &str| -> Result<(Chid, DomainSig, Option<SortKey>), String> {
            for index in indices {
                if let Some(d) = index.fun(name) {
                    if d.relational {
                        return Err(format!("`{name}` is relational, not a constructor"));
                    }
                    return Ok((d.chid, d.domain.clone(), d.codomain));
                }
            }
            Err(format!("no `{name}` constructor among the swept revisions"))
        };
        // StateF = the sort of qvrCons's `region` field.
        let (_, vrc_domain, _) = find_decl("qvrCons")?;
        let statef_sort = match &vrc_domain {
            DomainSig::Record(fields) => fields
                .iter()
                .find_map(|(n, s)| match (n.as_str(), s) {
                    ("region", SortKey::Elem(c)) => Some(c),
                    _ => None,
                })
                .copied()
                .ok_or_else(|| "`qvrCons` has no elem-sorted `region` field".to_string())?,
            _ => return Err("`qvrCons` domain is not a record".into()),
        };
        // SFList = SAnd's unary domain; Poly = SAtomLE's `poly` field
        // (legacy shape) or the `oPoly` injection's field behind the
        // atom's `o: StateObservable` argument (the event-4
        // re-founding) — dual-shape, per the dual-pin discipline.
        let (s_and, sand_domain, sand_cod) = find_decl("SAnd")?;
        let DomainSig::Unary(SortKey::Elem(sflist_sort)) = sand_domain else {
            return Err("`SAnd` is not a unary elem-sorted constructor".into());
        };
        let (s_atom_le, le_domain, le_cod) = find_decl("SAtomLE")?;
        let atom_field = |name: &str| -> Option<Chid> {
            match &le_domain {
                DomainSig::Record(fields) => {
                    fields.iter().find_map(|(n, s)| match (n.as_str(), s) {
                        (fname, SortKey::Elem(c)) if fname == name => Some(*c),
                        _ => None,
                    })
                }
                _ => None,
            }
        };
        let (poly_sort, o_poly, stateobs_sort) = if let Some(ps) = atom_field("poly") {
            (ps, None, None)
        } else if let Some(so) = atom_field("o") {
            let (o_poly, op_domain, op_cod) = find_decl("oPoly")?;
            if op_cod != Some(SortKey::Elem(so)) {
                return Err("`oPoly` does not land in the atom's observable sort".into());
            }
            let ps = match &op_domain {
                DomainSig::Record(fields) => fields
                    .iter()
                    .find_map(|(n, s)| match (n.as_str(), s) {
                        ("poly", SortKey::Elem(c)) => Some(*c),
                        _ => None,
                    })
                    .ok_or_else(|| "`oPoly` has no elem-sorted `poly` field".to_string())?,
                _ => return Err("`oPoly` domain is not a record".into()),
            };
            (ps, Some(o_poly), Some(so))
        } else {
            return Err(
                "`SAtomLE` has neither a `poly` field (legacy) nor an `o` field \
                 (post-grid) — no atom shape resolves"
                    .into(),
            );
        };
        let expect_cod = |name: &str, cod: Option<SortKey>, want: Chid| -> Result<(), String> {
            if cod == Some(SortKey::Elem(want)) {
                Ok(())
            } else {
                Err(format!("`{name}` has an unexpected codomain sort"))
            }
        };
        expect_cod("SAnd", sand_cod, statef_sort)?;
        expect_cod("SAtomLE", le_cod, statef_sort)?;
        let (s_true, _, st_cod) = find_decl("STrue")?;
        expect_cod("STrue", st_cod, statef_sort)?;
        let (s_atom_ge, _, ge_cod) = find_decl("SAtomGE")?;
        expect_cod("SAtomGE", ge_cod, statef_sort)?;
        let (sl_nil, _, sln_cod) = find_decl("slNil")?;
        expect_cod("slNil", sln_cod, sflist_sort)?;
        let (sl_cons, _, slc_cod) = find_decl("slCons")?;
        expect_cod("slCons", slc_cod, sflist_sort)?;
        let (p_zero, _, pz_cod) = find_decl("pZero")?;
        expect_cod("pZero", pz_cod, poly_sort)?;
        let (p_term, _, pt_cod) = find_decl("pTerm")?;
        expect_cod("pTerm", pt_cod, poly_sort)?;
        // Rosters: slash-free non-relational funs with an Elem codomain
        // roster under that sort; attribute funs excluded (pinned
        // convention 6 — `build_morse_vocab`'s roster discipline).
        let mut statef_roster = HashSet::new();
        let mut sflist_roster = HashSet::new();
        let mut poly_roster = HashSet::new();
        let mut stateobs_roster = HashSet::new();
        for index in indices {
            for decl in &index.funs {
                if decl.relational || decl.name.contains('/') {
                    continue;
                }
                if let Some(SortKey::Elem(c)) = decl.codomain {
                    if c == statef_sort {
                        statef_roster.insert(decl.chid);
                    } else if c == sflist_sort {
                        sflist_roster.insert(decl.chid);
                    } else if c == poly_sort {
                        poly_roster.insert(decl.chid);
                    } else if Some(c) == stateobs_sort {
                        stateobs_roster.insert(decl.chid);
                    }
                }
            }
        }
        let region = RegionVocab {
            s_true,
            s_and,
            s_atom_le,
            s_atom_ge,
            sl_nil,
            sl_cons,
            p_zero,
            p_term,
            statef_roster,
            sflist_roster,
            poly_roster,
            o_poly,
            stateobs_roster,
        };

        // The staged-signature table (review finding): bind the
        // `DomainSig`/codomain data for EVERY non-relational fun in the
        // swept indices — the pre-r3 resolver checked `!relational` and
        // discarded the rest; the schema step (step 2b) validates every
        // owned row against these. Recording the whole sweep (not just
        // the 40-odd vocabulary funs) is deliberate: the rosters span
        // arbitrary same-sort constructors, and a fun with no entry
        // refuses fail-closed at admission.
        let mut schema = VocabSchema::default();
        for index in indices {
            for decl in &index.funs {
                if decl.relational {
                    continue;
                }
                schema.funs.insert(
                    decl.chid,
                    FunSchema {
                        domain: decl.domain.clone(),
                        codomain: decl.codomain,
                    },
                );
            }
        }

        Ok(ArenaVocab {
            qgc_mk: find("qgcMk")?,
            qpt_leaf: find("qptLeaf")?,
            qpt_split: find("qptSplit")?,
            qgl_nil: find("qglNil")?,
            qgl_cons: find("qglCons")?,
            qgen_interval: find("qgenInterval")?,
            qgen_kuhn: find("qgenKuhn")?,
            qnl_nil: find("qnlNil")?,
            qnl_cons: find("qnlCons")?,
            qst_leaf: find("qstLeaf")?,
            qst_split: find("qstSplit")?,
            qsl_nil: find("qslNil")?,
            qsl_cons: find("qslCons")?,
            qch_identity: find("qchIdentity")?,
            qch_digest: find("qchDigest")?,
            qar_mk: find("qarMk")?,
            box_nil: find("boxNil")?,
            box_cons: find("boxCons")?,
            mk_interval: find("mkInterval")?,
            qdag_mk: find("qdagMk")?,
            qde_nil: find("qdeNil")?,
            qde_cons: find("qdeCons")?,
            qcm_nil: find("qcmNil")?,
            qcm_vertex: find("qcmVertex")?,
            qcm_transit: find("qcmTransit")?,
            qvr_nil: find("qvrNil")?,
            qvr_cons: find("qvrCons")?,
            qrl_nil: find("qrlNil")?,
            qrl_cons: find("qrlCons")?,
            qb_nil: find("qbNil")?,
            qb_cons: find("qbCons")?,
            qf_nil: find("qfNil")?,
            qf_cons: find("qfCons")?,
            lat_cx: find("QBlockLattice/cx")?,
            lat_arena: find("QBlockLattice/arena")?,
            lat_blocks: find("QBlockLattice/blocks")?,
            morse_judgment: find("QMorse/judgment")?,
            morse_graph: find("QMorse/graph")?,
            morse_rho: find("QMorse/rho")?,
            morse_arena: find("QMorse/arena")?,
            dis_proof: find("QMorseDischarge/proof")?,
            dis_lattice: find("QMorseDischarge/lattice")?,
            dis_h: find("QMorseDischarge/h")?,
            concludes: find("QProof/concludes")?,
            region,
            schema,
        })
    }
}

// ---------------------------------------------------------------------
// Decoded data (pure — profile checks and R1 assembly run on this)
// ---------------------------------------------------------------------

/// An exact rational with positive denominator (comparisons by
/// cross-multiplication — the R1 oracle's own convention).
#[derive(Debug, Clone)]
pub struct Q {
    num: BigInt,
    den: BigInt,
}

impl Q {
    /// Public dtype-checked constructor (tests and the Lean twin's
    /// harness build decoded values through this).
    pub fn from_literal(l: &Literal) -> Option<Q> {
        matches!(l.view(), LiteralView::Q { .. }).then(|| Q::from_lit(l))
    }

    /// From a canonical Q literal (callers check the dtype).
    fn from_lit(l: &Literal) -> Q {
        let LiteralView::Q { num, den } = l.view() else {
            unreachable!("callers check the Q dtype")
        };
        Q {
            num: BigInt::from_signed_bytes_le(num),
            den: BigInt::from(BigUint::from_bytes_le(den)),
        }
    }

    fn cmp(&self, other: &Q) -> Ordering {
        // dens > 0, so cross-multiplication preserves order.
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }

    fn lt(&self, other: &Q) -> bool {
        self.cmp(other) == Ordering::Less
    }
}

/// A shape-only dyadic split tree (the staged `QSplitTree`): each
/// split's axis and cut are DERIVED (widest axis, exact midpoint), so
/// only the branching shape rides the wire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SplitTree {
    Leaf,
    Split {
        lo: Box<SplitTree>,
        hi: Box<SplitTree>,
    },
}

/// A per-group complex generator (rev 2 `QGroupGen`).
#[derive(Debug, Clone)]
pub enum GroupGen {
    /// Interior cut list (see the module docs' cut-list convention),
    /// with the source literals kept for degenerate-grid derivation.
    Interval { cuts: Vec<(Q, Literal)> },
    /// The staged Kuhn payload, decoded at admission (review finding).
    /// Validity (GV5's Kuhn arm): `len(res)` = the group's fibre size,
    /// every `res` entry ≥ 1, `len(splits) = Π res`. The v0 profile
    /// still refuses every non-singleton group downstream of these
    /// checks.
    Kuhn {
        res: Vec<u64>,
        splits: Vec<SplitTree>,
    },
}

/// A chart reference (rev 2 `QChartRef` — the sigma-variant's slot).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChartRef {
    Identity,
    /// The reserved digest constructor, payload uninterpreted.
    Digest,
}

/// A patch-tree leaf: the local presentation.
#[derive(Debug, Clone)]
pub struct PatchLeaf {
    /// The RGS partition wire, verbatim (axis k belongs to group
    /// part\[k\]).
    pub part: Vec<u64>,
    /// Aligned per-group generators.
    pub gens: Vec<GroupGen>,
    pub chart: ChartRef,
}

/// The split forest (rev 2 `QPatchTree`).
#[derive(Debug, Clone)]
pub enum PatchTree {
    Leaf(PatchLeaf),
    Split {
        axis: u64,
        cut: Q,
        lo: Box<PatchTree>,
        hi: Box<PatchTree>,
    },
}

/// The decoded unified grid complex (rev 2 `QGridCx`).
#[derive(Debug, Clone)]
pub struct GridCx {
    /// Per-axis ambient intervals, with source literals kept for
    /// degenerate-grid derivation.
    pub dom: Vec<(Q, Q, Literal, Literal)>,
    pub tree: PatchTree,
}

/// The decoded `QMorse/arena` value (rev 2 `QArena` = `qarMk(cells, cx)`),
/// exposed for the chase hook (the `ax/qmorsedischarge/arena`
/// equation compares it against the lattice's pair).
#[derive(Debug, Clone)]
pub struct ArenaValue {
    /// The QArena element itself (hash-consed identity).
    pub elem: u32,
    pub cells: Vec<u64>,
    /// The cx element cited by the pair (hash-consed identity — equal
    /// generators are the same element).
    pub cx_elem: u32,
}

/// The decoded certificate object — everything the profile checks, the
/// R1 assembly, and the chase hook consume.
#[derive(Debug, Clone)]
pub struct DecodedBundle {
    /// The sole QMorse subject.
    pub morse_elem: u32,
    /// The sole QMorseDischarge subject.
    pub discharge_elem: u32,
    /// The discharge's lattice element.
    pub lattice_elem: u32,
    /// The lattice's grid-complex element (hash-consed identity).
    pub cx_elem: u32,
    pub cx: GridCx,
    /// The lattice's arena Shape payload, verbatim.
    pub arena: Vec<u64>,
    pub blocks: Vec<BlockData>,
    pub dag_vertices: u64,
    pub dag_edges: Vec<(u64, u64)>,
    pub h: Vec<HEntry>,
    /// (vertex, region elem) pairs; classified at R1 assembly through
    /// the shared box-aligned recognizer (module docs, integration
    /// seams — the shared-recognizer contract).
    pub rho: Vec<(u64, u32)>,
    /// The judgement's arena pair, for the chase equation hook.
    pub morse_arena: ArenaValue,
    /// The discharge's proof element (`QMorseDischarge/proof` — the
    /// linkage chain's first hop; the review repair).
    pub proof_elem: u32,
    /// The QJudgment element BOTH `QProof/concludes` and
    /// `QMorse/judgment` resolve to (the chain's validated endpoint —
    /// a mismatch refused at decode).
    pub judgment_elem: u32,
}

// ---------------------------------------------------------------------
// Refusals (every step's named reasons)
// ---------------------------------------------------------------------

/// A generator-validity violation (version-INDEPENDENT structural
/// validity of the grid complex; the exact strictness statement lives
/// in the module docs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenViolation {
    /// GV1: `n = 0` (zero-dimensional domain — rev 2 pins refusal).
    ZeroDim,
    /// GV1: `dom[axis].lo < dom[axis].hi` fails (strict).
    DegenerateDomAxis { axis: usize },
    /// GV2: a split axis out of range.
    SplitAxisRange { axis: u64 },
    /// GV2: a split cut NOT strictly interior to its derived sub-box
    /// (equality with an endpoint included — the endpoint-cut fix).
    EndpointCut { axis: u64 },
    /// GV3: the partition wire is not length-n RGS-canonical.
    PartitionWire { why: String },
    /// GV4: `QGenList` length ≠ 1 + max(part).
    GenListAlignment { expected: usize, found: usize },
    /// GV5: generator kind vs fibre size (interval iff 1, Kuhn iff
    /// 2..=3).
    GeneratorKindFiber { group: usize, fiber: usize },
    /// GV6: interval cuts not strictly increasing strictly inside the
    /// derived sub-box interval.
    IntervalCuts { group: usize },
    /// GV5 Kuhn payload: `len(res)` ≠ the group's fibre size
    /// (`res` aligns with the group's axes).
    KuhnResLen {
        group: usize,
        expected: usize,
        found: usize,
    },
    /// GV5 Kuhn payload: a `res` entry of 0 (every base resolution
    /// must be ≥ 1).
    KuhnResEntry { group: usize, index: usize },
    /// GV5 Kuhn payload: `len(splits)` ≠ `Π res` (one split tree per
    /// base sub-box).
    KuhnSplitsLen {
        group: usize,
        expected: u64,
        found: usize,
    },
}

/// A versioned-profile violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProfileViolation {
    /// The tree is not a single leaf (multi-patch complexes await
    /// their own version event, with their recompute machinery).
    SingleLeafRequired,
    /// A non-singleton partition group (mixed complexes await the mixed-complex successor).
    NonSingletonGroup { group: usize },
    /// A chart other than `qchIdentity` at a version that requires
    /// identity charts.
    NonIdentityChart,
    /// A Shape payload indexes at or past the derived cell count.
    ShapeRange {
        what: &'static str,
        index: u64,
        cell_count: u64,
    },
}

/// A v0 object-graph linkage violation (review finding): the chain
/// `QMorseDischarge/proof → QProof/concludes → QMorse/judgment` must
/// bind the selected records uniquely, locally, and consistently.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkageViolation {
    /// A required chain row is absent (`what` names the fun).
    MissingRow { what: &'static str },
    /// A chain fun carries multiple rows on its subject — ambiguous.
    Ambiguous { what: &'static str },
    /// A chain link cites an external element (single-body context).
    External { what: &'static str },
    /// A chain link's value cell is not an element ref.
    NotAnElem { what: &'static str },
    /// `QProof/concludes` and `QMorse/judgment` resolve to different
    /// QJudgment elements: the discharge's proof does not conclude the
    /// selected judgement.
    Mismatch,
}

/// The admission verdict's refusal side. Refusal at ANY step admits
/// nothing.
#[derive(Debug, Clone)]
pub enum AdmissionRefusal {
    /// Step 1: the rows do not decode (structure undecidable,
    /// ambiguous, cyclic, or over budget) — refuse-not-guess.
    Decode(String),
    /// Step 1: the v0 object-graph linkage chain is missing, external,
    /// ambiguous, or mismatched (review finding).
    Linkage(LinkageViolation),
    /// Step 2a: an op the decoded certificate object does not own — an
    /// unattached row cannot piggyback on a green bundle (review finding).
    Closure(String),
    /// Step 2b: a row does not conform to its fun's STAGED signature
    /// (arity, cell kinds, codomain sort), or an element carries
    /// producer rows in more than one roster family (global P-FUN at
    /// the gate — the staged-schema repair: the door is a staged-schema boundary).
    Schema(String),
    /// Step 3a: generator validity failed.
    Generator(GenViolation),
    /// Step 3b: the versioned profile refused.
    Profile {
        version: ProfileVersion,
        violation: ProfileViolation,
    },
    /// Step 4: the mandatory R1 recompute DECIDED a violation.
    R1(KitViolation),
    /// Step 4: the R1 recompute REFUSED (budget/undecidable) — which
    /// also admits nothing.
    R1Refused(String),
    /// Step 5: the chase refused.
    Chase(String),
}

impl std::fmt::Display for AdmissionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AdmissionRefusal::Decode(why) => write!(f, "decode refused: {why}"),
            AdmissionRefusal::Linkage(v) => write!(f, "v0 linkage refused: {v:?}"),
            AdmissionRefusal::Closure(why) => write!(f, "object closure refused: {why}"),
            AdmissionRefusal::Schema(why) => {
                write!(f, "staged-schema conformance refused: {why}")
            }
            AdmissionRefusal::Generator(v) => write!(f, "generator validity: {v:?}"),
            AdmissionRefusal::Profile { version, violation } => {
                write!(f, "profile v{} refused: {violation:?}", version.tag())
            }
            AdmissionRefusal::R1(v) => write!(f, "R1 recompute violation: {v}"),
            AdmissionRefusal::R1Refused(why) => write!(f, "R1 recompute refused: {why}"),
            AdmissionRefusal::Chase(why) => write!(f, "admission chase refused: {why}"),
        }
    }
}

// ---------------------------------------------------------------------
// The chase hook (its position and signature are the frozen
// contract)
// ---------------------------------------------------------------------

/// Chase-checking of admission-relevant axioms, run AFTER the
/// mandatory R1 recompute and BEFORE any visibility. The consumer
/// is [`ArenaEquationChase`] (the rev 2 chase route: a bundle whose judgement
/// arena differs from `qarMk(lat arena, lat cx)` — fields
/// `[cells: Shape, cx: QGridCx]` — refuses at admission). A hook
/// refusal admits nothing, like every other step.
///
/// **Seam scope after the review repairs**: caller-implemented hooks reach
/// the pipeline only through [`probe_admission`], which cannot mint
/// visibility. The visibility doors ([`admit_certificate`],
/// [`CertStore::admit`]) construct their own [`ArenaEquationChase`]
/// and accept no hook.
pub trait AdmissionChase {
    fn check(&self, bundle: &DecodedBundle, rows: &CertRows) -> Result<(), String>;
}

/// The no-axiom hook: passes unconditionally. A DIAGNOSTIC element
/// only ("no admission-relevant axioms in scope" — profile-focused
/// probes): it is accepted solely by [`probe_admission`], so it cannot
/// mint visibility (review finding).
pub struct NoChaseAxioms;

impl AdmissionChase for NoChaseAxioms {
    fn check(&self, _bundle: &DecodedBundle, _rows: &CertRows) -> Result<(), String> {
        Ok(())
    }
}

/// The chase consumer (the rev 2 chase route): chase-checking of the staged
/// `ax/qmorsedischarge/arena` equation at admission.
///
/// The axiom (QtslCert.geolog axioms section — the staged rows are the
/// encoding authority; this checker is its admission-side evaluator):
///
/// ```text
/// ax/qmorsedischarge/arena : forall r : QMorseDischarge, p : QProof,
///     j : QMorse, lat : QBlockLattice.
///   r QMorseDischarge/proof = p,
///   p QProof/concludes = j QMorse/judgment,
///   r QMorseDischarge/lattice = lat
///   |- j QMorse/arena = [cells: lat QBlockLattice/arena,
///                        cx: lat QBlockLattice/cx] qarMk;
/// ```
///
/// **Semantics** (the chase reading, Enforced posture): every
/// instantiation of the premise over the body's rows must witness the
/// conclusion — a pure equational atom between hash-consed values.
/// The tie is *syntactic* (same generator element, same cell Shape),
/// deliberately: adjudicating semantic equality of regions is geometry
/// the certificate does not owe. Concretely, for each matched
/// `(r, p, j, lat)`: `j`'s `QMorse/arena` element must carry a `qarMk`
/// constructor row whose `cells` literal equals `lat`'s
/// `QBlockLattice/arena` Shape and whose `cx` ref cites `lat`'s
/// `QBlockLattice/cx` element (normalized identity — hash-consing
/// makes equal complexes the same element, so citation equality IS the
/// equation).
///
/// **Refusal posture** (R8 conservative rule — a gate that cannot
/// evaluate must not admit): once the premise matches, an undefined
/// `QMorse/arena`, a missing `qarMk` constructor row, missing lattice
/// attributes, any external ref in the matched pattern (the admission
/// context is single-body), or an exhausted budget all REFUSE — never
/// a silent pass. Multiplicities are checked exhaustively: every
/// premise-row combination and every `qarMk` producer row must
/// satisfy the equation (P-FUN ambiguity thereby refuses through the
/// equation itself). And BEFORE quantification (review finding): any
/// admission-relevant row keyed on an EXTERNAL subject refuses
/// outright — the universal loop enumerates local subjects, so such a
/// row would otherwise escape it entirely, contradicting this posture.
/// The step budget is charged across the conclusion loops as well as
/// premise enumeration (review finding).
///
/// **Vacuous satisfaction is NOT admissible** (review finding): logical
/// vacuity is correct for the conditional axiom, but a v0 data
/// product whose judgement and discharge were selected independently —
/// with no admitted row saying the discharge's proof concludes that
/// judgement — is unsound. Two independent teeth: the decode's linkage
/// rule (pipeline step 1) requires the unique local chain before this
/// consumer ever runs, and this consumer additionally counts matched
/// premise instances and refuses at zero — so even a caller reaching
/// it directly (or a future pipeline regression) cannot ride vacuity
/// into a pass.
pub struct ArenaEquationChase {
    /// `QMorseDischarge/proof : QMorseDischarge -> QProof`
    pub dis_proof: Chid,
    /// `QProof/concludes : QProof -> QJudgment` (also carried by
    /// [`ArenaVocab`] since the linkage rule landed; resolved
    /// independently here so the chase stands alone as a consumer).
    pub concludes: Chid,
    /// `QMorse/judgment : QMorse -> QJudgment`
    pub morse_judgment: Chid,
    /// `QMorseDischarge/lattice : QMorseDischarge -> QBlockLattice`
    pub dis_lattice: Chid,
    /// `QMorse/arena : QMorse -> QArena`
    pub morse_arena: Chid,
    /// `QBlockLattice/arena : QBlockLattice -> Shape`
    pub lat_arena: Chid,
    /// `QBlockLattice/cx : QBlockLattice -> QGridCx`
    pub lat_cx: Chid,
    /// `qarMk : [cells: Shape, cx: QGridCx] -> QArena`
    pub qar_mk: Chid,
}

impl ArenaEquationChase {
    /// Build from the admission vocabulary (which carries every chain
    /// identity including `QProof/concludes` since the review repair). Tests
    /// inject synthetic chids the same way they do for [`ArenaVocab`].
    pub fn new(vocab: &ArenaVocab) -> ArenaEquationChase {
        ArenaEquationChase {
            dis_proof: vocab.dis_proof,
            concludes: vocab.concludes,
            morse_judgment: vocab.morse_judgment,
            dis_lattice: vocab.dis_lattice,
            morse_arena: vocab.morse_arena,
            lat_arena: vocab.lat_arena,
            lat_cx: vocab.lat_cx,
            qar_mk: vocab.qar_mk,
        }
    }

    /// Pin the consumer's identities by name across staged theory
    /// indices — the same seam discipline as
    /// [`ArenaVocab::from_indices`], correct pre-staging behaviour
    /// included (`Err` names the first missing declaration).
    pub fn from_indices(indices: &[&TheoryIndex]) -> Result<ArenaEquationChase, String> {
        Ok(ArenaEquationChase::new(&ArenaVocab::from_indices(indices)?))
    }
}

/// Value equality at the chase's grain: refs by normalized pinned
/// identity (hash-consed citation equality), literals by canonical
/// bytes (the envelope's `Eq` IS semantic equality), never across the
/// ref/literal boundary.
fn value_eq(rows: &CertRows, a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Ref(x), Value::Ref(y)) => rows.norm(x) == rows.norm(y),
        (Value::Lit(x), Value::Lit(y)) => x == y,
        _ => false,
    }
}

/// One chase step against the shared budget — charged across premise
/// enumeration AND the multiplicative conclusion loops (review finding).
fn chase_step(steps: &mut usize) -> Result<(), String> {
    *steps += 1;
    if *steps > MAX_ADMISSION_DECODE_STEPS {
        Err(
            "ax/qmorsedischarge/arena: chase evaluation exhausted its step budget — \
             pathological rows"
                .to_string(),
        )
    } else {
        Ok(())
    }
}

impl AdmissionChase for ArenaEquationChase {
    fn check(&self, _bundle: &DecodedBundle, rows: &CertRows) -> Result<(), String> {
        const AX: &str = "ax/qmorsedischarge/arena";
        let mut steps: usize = 0;

        // Fail-closed prologue (a review repair): the universal loop below ranges
        // over `subject_elems()`, which indexes LOCAL subjects only —
        // a row keyed on an EXTERNAL subject would otherwise vanish
        // before quantification (an external-`r` discharge chain or an
        // external-`j` judgement row would be a premise instance the
        // chase never considers). The admission context is single-body:
        // a premise about another body's element cannot be evaluated
        // here, so any admission-relevant row with an external subject
        // refuses — never a silent pass.
        let relevant: [(Chid, &str); 7] = [
            (self.dis_proof, "QMorseDischarge/proof"),
            (self.concludes, "QProof/concludes"),
            (self.morse_judgment, "QMorse/judgment"),
            (self.dis_lattice, "QMorseDischarge/lattice"),
            (self.morse_arena, "QMorse/arena"),
            (self.lat_arena, "QBlockLattice/arena"),
            (self.lat_cx, "QBlockLattice/cx"),
        ];
        for row in rows.external_subject_rows() {
            chase_step(&mut steps)?;
            if let Some((_, name)) = relevant.iter().find(|(c, _)| *c == row.fun) {
                return Err(format!(
                    "{AX}: a `{name}` row is keyed on an EXTERNAL subject — the admission \
                     context is single-body and the universal loop ranges over local \
                     subjects only, so the row would escape quantification; fail-closed \
                     refusal"
                ));
            }
        }

        // Enumerate ALL subjects (sorted — deterministic verdicts):
        // the axiom's entity vars are universally quantified over the
        // body, not over the located sole bundle records.
        let mut matched: usize = 0;
        let subjects = rows.subject_elems();
        for &r in &subjects {
            // Premise 1: `r QMorseDischarge/proof = p`.
            for proof_row in rows.attrs(r).iter().filter(|a| a.fun == self.dis_proof) {
                chase_step(&mut steps)?;
                let p = match &proof_row.value {
                    Value::Ref(pr) => rows.local(pr).ok_or_else(|| {
                        format!(
                            "{AX}: `QMorseDischarge/proof` of element {r} cites an external \
                             element — the admission context is single-body"
                        )
                    })?,
                    _ => {
                        return Err(format!(
                            "{AX}: `QMorseDischarge/proof` of element {r} is not an element \
                             ref — malformed rows"
                        ))
                    }
                };
                // Premise 2 lhs: `p QProof/concludes` (no row: the
                // premise never matches — vacuous, chase-correct).
                for concl_row in rows.attrs(p).iter().filter(|a| a.fun == self.concludes) {
                    // Premise 2 rhs: every j with an equal judgement.
                    for &j in &subjects {
                        for j_row in rows
                            .attrs(j)
                            .iter()
                            .filter(|a| a.fun == self.morse_judgment)
                        {
                            chase_step(&mut steps)?;
                            if !value_eq(rows, &concl_row.value, &j_row.value) {
                                continue;
                            }
                            // Premise 3: `r QMorseDischarge/lattice = lat`.
                            for lat_row in
                                rows.attrs(r).iter().filter(|a| a.fun == self.dis_lattice)
                            {
                                chase_step(&mut steps)?;
                                let lat = match &lat_row.value {
                                    Value::Ref(lr) => rows.local(lr).ok_or_else(|| {
                                        format!(
                                            "{AX}: `QMorseDischarge/lattice` of element {r} \
                                             cites an external element — single-body context"
                                        )
                                    })?,
                                    _ => {
                                        return Err(format!(
                                            "{AX}: `QMorseDischarge/lattice` of element {r} \
                                             is not an element ref — malformed rows"
                                        ))
                                    }
                                };
                                matched += 1;
                                self.check_conclusion(rows, &mut steps, r, j, lat)?;
                            }
                        }
                    }
                }
            }
        }
        if matched == 0 {
            return Err(format!(
                "{AX}: no premise instance matched — the arena equation was never \
                 exercised, and vacuous satisfaction is not admissible at v0 (review finding)"
            ));
        }
        Ok(())
    }
}

impl ArenaEquationChase {
    /// The conclusion, for one matched premise instance: `j`'s arena
    /// element must be `qarMk(lat's arena Shape, lat's cx element)` by
    /// citation. Premise matched ⇒ every evaluation obstacle refuses.
    /// `steps` is the shared chase budget (D2: the conclusion loops
    /// multiply and are charged like the premise enumeration).
    fn check_conclusion(
        &self,
        rows: &CertRows,
        steps: &mut usize,
        r: u32,
        j: u32,
        lat: u32,
    ) -> Result<(), String> {
        const AX: &str = "ax/qmorsedischarge/arena";
        // RHS ingredients: lat's arena Shape + cx citation.
        let lat_arenas: Vec<&AttrRow> = rows
            .attrs(lat)
            .iter()
            .filter(|a| a.fun == self.lat_arena)
            .collect();
        let lat_cxs: Vec<&AttrRow> = rows
            .attrs(lat)
            .iter()
            .filter(|a| a.fun == self.lat_cx)
            .collect();
        if lat_arenas.is_empty() || lat_cxs.is_empty() {
            return Err(format!(
                "{AX}: premise matched (discharge {r}, judgment {j}, lattice {lat}) but the \
                 lattice lacks a `QBlockLattice/{}` row — the equation cannot be evaluated",
                if lat_arenas.is_empty() { "arena" } else { "cx" }
            ));
        }
        // LHS: j's arena element(s).
        let arena_rows: Vec<&AttrRow> = rows
            .attrs(j)
            .iter()
            .filter(|a| a.fun == self.morse_arena)
            .collect();
        if arena_rows.is_empty() {
            return Err(format!(
                "{AX}: premise matched (discharge {r}, judgment {j}, lattice {lat}) but \
                 `QMorse/arena` is undefined at the judgment — the equation has no witness"
            ));
        }
        for arena_row in arena_rows {
            chase_step(steps)?;
            let a_elem = match &arena_row.value {
                Value::Ref(ar) => rows.local(ar).ok_or_else(|| {
                    format!(
                        "{AX}: `QMorse/arena` of judgment {j} cites an external element — \
                         single-body context"
                    )
                })?,
                _ => {
                    return Err(format!(
                        "{AX}: `QMorse/arena` of judgment {j} is not an element ref — \
                         malformed rows"
                    ))
                }
            };
            let qar_rows: Vec<&CtorRow> = rows
                .producers(a_elem)
                .iter()
                .filter(|c| c.fun == self.qar_mk)
                .collect();
            if qar_rows.is_empty() {
                return Err(format!(
                    "{AX}: judgment {j}'s arena element {a_elem} carries no `qarMk` \
                     constructor row — the equation cannot be witnessed"
                ));
            }
            for qar in qar_rows {
                chase_step(steps)?;
                // qarMk [cells: Shape, cx: QGridCx] — bytewise field
                // order, same as the decode's reading.
                let [cells, cx] = qar.args.as_slice() else {
                    return Err(format!(
                        "{AX}: `qarMk` row producing element {a_elem} has the wrong arity — \
                         malformed rows"
                    ));
                };
                for la in &lat_arenas {
                    chase_step(steps)?;
                    if !value_eq(rows, cells, &la.value) {
                        return Err(format!(
                            "{AX}: judgment arena differs from the lattice's — \
                             `qarMk/cells` of arena element {a_elem} ≠ `QBlockLattice/arena` \
                             of lattice {lat} (the syntactic tie refuses at admission)"
                        ));
                    }
                }
                for lc in &lat_cxs {
                    chase_step(steps)?;
                    if !value_eq(rows, cx, &lc.value) {
                        return Err(format!(
                            "{AX}: judgment arena differs from the lattice's — \
                             `qarMk/cx` of arena element {a_elem} does not cite lattice \
                             {lat}'s `QBlockLattice/cx` element (the syntactic tie refuses \
                             at admission)"
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------
// Visibility (the atomic boundary)
// ---------------------------------------------------------------------

/// An admitted certificate — the ONLY reader surface. Constructed
/// exclusively by the production-fixed doors ([`admit_certificate`] /
/// [`CertStore::admit`]: V0 + the sealed [`ArenaEquationChase`]); its
/// existence witnesses that every admission step was green under the
/// recorded profile version. [`probe_admission`] runs the same
/// pipeline but can never construct one.
#[derive(Debug, Clone)]
pub struct AdmittedCert {
    version: ProfileVersion,
    rows: CertRows,
    row_count: usize,
    bundle: DecodedBundle,
}

impl AdmittedCert {
    pub fn version(&self) -> ProfileVersion {
        self.version
    }

    pub fn rows(&self) -> &CertRows {
        &self.rows
    }

    /// The bundle's op count at admission (a visibility measure for
    /// the atomicity witness: refused bundles contribute zero).
    pub fn row_count(&self) -> usize {
        self.row_count
    }

    pub fn bundle(&self) -> &DecodedBundle {
        &self.bundle
    }
}

/// The reference reader surface: certificates become visible here ONLY
/// via [`CertStore::admit`]. The atomicity acceptance test witnesses
/// (not asserts) that a refused bundle leaves the store byte-for-byte
/// unchanged.
#[derive(Default)]
pub struct CertStore {
    certs: Vec<AdmittedCert>,
}

impl CertStore {
    pub fn new() -> CertStore {
        CertStore::default()
    }

    /// Atomic admission into the store: on refusal the store is
    /// untouched (no partial row, no placeholder, no tombstone).
    ///
    /// Policy-fixed (review finding): no version argument (V0), no chase
    /// argument (the sealed [`ArenaEquationChase`], built here from
    /// the vocabulary). The vocabulary is identity binding, not
    /// policy — production callers pass
    /// [`ArenaVocab::from_indices`]'s result; tests inject synthetic
    /// chids (C-ORACLE: the gate's logic is identity-driven).
    pub fn admit(
        &mut self,
        vocab: &ArenaVocab,
        ops: &[Op],
        own: [u8; 32],
        deps: &[[u8; 32]],
    ) -> Result<&AdmittedCert, AdmissionRefusal> {
        let cert = admit_certificate(vocab, ops, own, deps)?;
        self.certs.push(cert);
        Ok(self.certs.last().expect("just pushed"))
    }

    pub fn certs(&self) -> &[AdmittedCert] {
        &self.certs
    }

    /// Total reader-visible rows across admitted certificates (zero
    /// contribution from every refused bundle — the witness quantity).
    pub fn visible_row_count(&self) -> usize {
        self.certs.iter().map(|c| c.row_count).sum()
    }
}

// ---------------------------------------------------------------------
// Step 1: decode (refuse-not-guess)
// ---------------------------------------------------------------------

/// What the decode consumed — the closure check's evidence (review finding): a body op is OWNED iff it is the sole constructor row of a
/// walked element or a consumed `(subject, fun)` attribute row.
#[derive(Default)]
struct Consumed {
    /// Elements whose sole constructor row the walk consumed.
    ctor_elems: HashSet<u32>,
    /// `(subject, fun)` attribute rows the walk consumed.
    attrs: HashSet<(u32, Chid)>,
}

/// The constructor funs the admission grammar knows (the `sole`
/// roster; also the closure sweep's constructor-reading filter).
/// Public since r4-F03 so the test suite's identity-collision census
/// sweeps THE SAME roster the door filters by (a roster member the
/// census misses cannot exist by construction).
pub fn ctor_roster(v: &ArenaVocab) -> [Chid; 33] {
    [
        v.qgc_mk,
        v.qpt_leaf,
        v.qpt_split,
        v.qgl_nil,
        v.qgl_cons,
        v.qgen_interval,
        v.qgen_kuhn,
        v.qnl_nil,
        v.qnl_cons,
        v.qst_leaf,
        v.qst_split,
        v.qsl_nil,
        v.qsl_cons,
        v.qch_identity,
        v.qch_digest,
        v.qar_mk,
        v.box_nil,
        v.box_cons,
        v.mk_interval,
        v.qdag_mk,
        v.qde_nil,
        v.qde_cons,
        v.qcm_nil,
        v.qcm_vertex,
        v.qcm_transit,
        v.qvr_nil,
        v.qvr_cons,
        v.qrl_nil,
        v.qrl_cons,
        v.qb_nil,
        v.qb_cons,
        v.qf_nil,
        v.qf_cons,
    ]
}

struct Dec<'a> {
    v: &'a ArenaVocab,
    rows: &'a CertRows,
    steps: usize,
    used: Consumed,
}

type DecResult<T> = Result<T, AdmissionRefusal>;

fn refuse<T>(why: impl Into<String>) -> DecResult<T> {
    Err(AdmissionRefusal::Decode(why.into()))
}

impl<'a> Dec<'a> {
    fn step(&mut self) -> DecResult<()> {
        self.steps += 1;
        if self.steps > MAX_ADMISSION_DECODE_STEPS {
            refuse("structural walk exhausted its node budget — pathological rows")
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value, what: &str) -> DecResult<u32> {
        match val {
            Value::Ref(r) => match self.rows.local(r) {
                Some(e) => Ok(e),
                None => refuse(format!(
                    "`{what}` is an external element ref — the admission context is \
                     single-body at this leg"
                )),
            },
            _ => refuse(format!("`{what}` is not an element ref — malformed rows")),
        }
    }

    /// The unique constructor row producing `elem` among the funs the
    /// admission vocabulary knows (the `sole_roster_row` discipline:
    /// ambiguity refuses). Consumption is registered for the closure
    /// check.
    fn sole(&mut self, elem: u32, what: &str) -> DecResult<&'a CtorRow> {
        self.step()?;
        let roster = ctor_roster(self.v);
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains(&row.fun) {
                continue;
            }
            if found.is_some() {
                return refuse(format!(
                    "element {elem} ({what}) is produced by multiple constructor rows — \
                     ambiguous structure (P-FUN territory)"
                ));
            }
            found = Some(row);
        }
        match found {
            Some(r) => {
                self.used.ctor_elems.insert(elem);
                Ok(r)
            }
            None => refuse(format!(
                "element {elem} ({what}) has no constructor row in the bundle — \
                 structure undecidable"
            )),
        }
    }

    /// The unique attribute row `fun(subject) = value`. Consumption is
    /// registered for the closure check.
    fn sole_attr(&mut self, subject: u32, fun: Chid, what: &str) -> DecResult<&'a AttrRow> {
        self.step()?;
        let mut found: Option<&AttrRow> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return refuse(format!(
                    "element {subject} carries multiple `{what}` attribute rows — ambiguous"
                ));
            }
            found = Some(row);
        }
        match found {
            Some(r) => {
                self.used.attrs.insert((subject, fun));
                Ok(r)
            }
            None => refuse(format!(
                "element {subject} has no `{what}` attribute row — undecidable"
            )),
        }
    }

    fn nat(&self, val: &Value, what: &str) -> DecResult<u64> {
        if let Value::Lit(l) = val {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        refuse(format!("`{what}` is not a Nat literal — malformed rows"))
    }

    fn shape(&self, val: &Value, what: &str) -> DecResult<Vec<u64>> {
        if let Value::Lit(l) = val {
            if let LiteralView::Shape(s) = l.view() {
                return Ok(s.iter().collect());
            }
        }
        refuse(format!("`{what}` is not a Shape literal — malformed rows"))
    }

    fn q_lit(&self, val: &Value, what: &str) -> DecResult<Literal> {
        if let Value::Lit(l) = val {
            if matches!(l.view(), LiteralView::Q { .. }) {
                return Ok(l.clone());
            }
        }
        refuse(format!("`{what}` is not a Q literal — malformed rows"))
    }

    /// Walk a nil/cons list (cycle-checked within THIS walk; a shared
    /// tail across two walks is hash-consing-legal and fine).
    fn walk_list<T>(
        &mut self,
        head: u32,
        nil: Chid,
        cons: Chid,
        what: &str,
        mut on_cons: impl FnMut(&mut Self, &CtorRow) -> DecResult<(T, u32)>,
    ) -> DecResult<Vec<T>> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head;
        loop {
            if !visited.insert(cur) {
                return refuse(format!(
                    "element {cur} recurs along its own {what} tail (P-ACYCLIC territory)"
                ));
            }
            let row = self.sole(cur, what)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return refuse(format!(
                    "element {cur} is constructed outside the expected {what} nil/cons pair"
                ));
            }
            let (item, tail) = on_cons(self, row)?;
            out.push(item);
            cur = tail;
        }
    }

    /// Decode a Box element: cons-list of `mkInterval[hi, lo]`.
    fn decode_box(&mut self, elem: u32) -> DecResult<Vec<(Q, Q, Literal, Literal)>> {
        let interval_elems =
            self.walk_list(elem, self.v.box_nil, self.v.box_cons, "Box", |d, row| {
                let [head, tail] = row.args.as_slice() else {
                    return refuse("boxCons row arity mismatch");
                };
                let head = d.elem(head, "boxCons/head")?;
                let tail = d.elem(tail, "boxCons/tail")?;
                Ok((head, tail))
            })?;
        let mut out = Vec::with_capacity(interval_elems.len());
        for iv in interval_elems {
            let row = self.sole(iv, "Interval")?;
            if row.fun != self.v.mk_interval {
                return refuse("interval element not constructed by mkInterval");
            }
            let [hi, lo] = row.args.as_slice() else {
                return refuse("mkInterval row arity mismatch");
            };
            let hi_lit = self.q_lit(hi, "mkInterval/hi")?;
            let lo_lit = self.q_lit(lo, "mkInterval/lo")?;
            out.push((Q::from_lit(&lo_lit), Q::from_lit(&hi_lit), lo_lit, hi_lit));
        }
        Ok(out)
    }

    /// Decode a QSplitTree element (shape-only; `qstSplit [hi, lo]`
    /// bytewise, traversal lo-before-hi). Cycle discipline mirrors
    /// [`Dec::decode_tree`]: refusal on an element recurring along its
    /// OWN path; sharing across branches is hash-consing-legal.
    fn decode_split_tree(&mut self, elem: u32, path: &mut Vec<u32>) -> DecResult<SplitTree> {
        self.step()?;
        if path.contains(&elem) {
            return refuse(format!(
                "split-tree element {elem} recurs along its own path (P-ACYCLIC territory)"
            ));
        }
        if path.len() >= MAX_TREE_DEPTH {
            return refuse("split tree exceeds the depth budget — pathological rows");
        }
        let row = self.sole(elem, "QSplitTree")?.clone();
        if row.fun == self.v.qst_leaf {
            return Ok(SplitTree::Leaf);
        }
        if row.fun != self.v.qst_split {
            return refuse("split-tree element constructed outside the QSplitTree roster");
        }
        let [hi, lo] = row.args.as_slice() else {
            return refuse("qstSplit row arity mismatch");
        };
        let hi_elem = self.elem(hi, "qstSplit/hi")?;
        let lo_elem = self.elem(lo, "qstSplit/lo")?;
        path.push(elem);
        let lo = self.decode_split_tree(lo_elem, path)?;
        let hi = self.decode_split_tree(hi_elem, path)?;
        path.pop();
        Ok(SplitTree::Split {
            lo: Box::new(lo),
            hi: Box::new(hi),
        })
    }

    /// Decode a QGroupGen element.
    fn decode_gen(&mut self, elem: u32) -> DecResult<GroupGen> {
        let row = self.sole(elem, "QGroupGen")?;
        if row.fun == self.v.qgen_kuhn {
            // The staged layout: qgenKuhn [res, splits] (review finding).
            let row = row.clone();
            let [res, splits] = row.args.as_slice() else {
                return refuse("qgenKuhn row arity mismatch");
            };
            let res_elem = self.elem(res, "qgenKuhn/res")?;
            let res = self.walk_list(
                res_elem,
                self.v.qnl_nil,
                self.v.qnl_cons,
                "QNatList",
                |d, row| {
                    let [head, tail] = row.args.as_slice() else {
                        return refuse("qnlCons row arity mismatch");
                    };
                    let n = d.nat(head, "qnlCons/head")?;
                    let tail = d.elem(tail, "qnlCons/tail")?;
                    Ok((n, tail))
                },
            )?;
            let splits_elem = self.elem(splits, "qgenKuhn/splits")?;
            let split_elems = self.walk_list(
                splits_elem,
                self.v.qsl_nil,
                self.v.qsl_cons,
                "QSplitList",
                |d, row| {
                    let [head, tail] = row.args.as_slice() else {
                        return refuse("qslCons row arity mismatch");
                    };
                    let head = d.elem(head, "qslCons/head")?;
                    let tail = d.elem(tail, "qslCons/tail")?;
                    Ok((head, tail))
                },
            )?;
            let mut splits = Vec::with_capacity(split_elems.len());
            for t in split_elems {
                let mut path = Vec::new();
                splits.push(self.decode_split_tree(t, &mut path)?);
            }
            return Ok(GroupGen::Kuhn { res, splits });
        }
        if row.fun != self.v.qgen_interval {
            return refuse("group generator constructed outside the QGroupGen roster");
        }
        let [cuts] = row.args.as_slice() else {
            return refuse("qgenInterval row arity mismatch");
        };
        let cuts_elem = self.elem(cuts, "qgenInterval/cuts")?;
        let cuts = self.walk_list(
            cuts_elem,
            self.v.qrl_nil,
            self.v.qrl_cons,
            "QRatList",
            |d, row| {
                let [head, tail] = row.args.as_slice() else {
                    return refuse("qrlCons row arity mismatch");
                };
                let lit = d.q_lit(head, "qrlCons/head")?;
                let tail = d.elem(tail, "qrlCons/tail")?;
                Ok(((Q::from_lit(&lit), lit), tail))
            },
        )?;
        Ok(GroupGen::Interval { cuts })
    }

    /// Decode a QPatchTree element. Cycle discipline: refusal on an
    /// element recurring along its OWN PATH (a genuine cycle); a
    /// subtree shared between the two halves of a split is
    /// hash-consing-legal and decodes twice.
    fn decode_tree(&mut self, elem: u32, path: &mut Vec<u32>) -> DecResult<PatchTree> {
        self.step()?;
        if path.contains(&elem) {
            return refuse(format!(
                "patch-tree element {elem} recurs along its own path (P-ACYCLIC territory)"
            ));
        }
        if path.len() >= MAX_TREE_DEPTH {
            return refuse("patch tree exceeds the depth budget — pathological rows");
        }
        let row = self.sole(elem, "QPatchTree")?.clone();
        if row.fun == self.v.qpt_leaf {
            let [chart, gens, part] = row.args.as_slice() else {
                return refuse("qptLeaf row arity mismatch");
            };
            let part = self.shape(part, "qptLeaf/part")?;
            let chart_elem = self.elem(chart, "qptLeaf/chart")?;
            let chart_row = self.sole(chart_elem, "QChartRef")?;
            let chart = if chart_row.fun == self.v.qch_identity {
                ChartRef::Identity
            } else if chart_row.fun == self.v.qch_digest {
                ChartRef::Digest
            } else {
                return refuse("chart element constructed outside the QChartRef roster");
            };
            let gens_elem = self.elem(gens, "qptLeaf/gens")?;
            let gen_elems = self.walk_list(
                gens_elem,
                self.v.qgl_nil,
                self.v.qgl_cons,
                "QGenList",
                |d, row| {
                    let [gen, tail] = row.args.as_slice() else {
                        return refuse("qglCons row arity mismatch");
                    };
                    let gen = d.elem(gen, "qglCons/gen")?;
                    let tail = d.elem(tail, "qglCons/tail")?;
                    Ok((gen, tail))
                },
            )?;
            let mut gens = Vec::with_capacity(gen_elems.len());
            for g in gen_elems {
                gens.push(self.decode_gen(g)?);
            }
            return Ok(PatchTree::Leaf(PatchLeaf { part, gens, chart }));
        }
        if row.fun != self.v.qpt_split {
            return refuse("patch-tree element constructed outside the QPatchTree roster");
        }
        let [axis, cut, hi, lo] = row.args.as_slice() else {
            return refuse("qptSplit row arity mismatch");
        };
        let axis = self.nat(axis, "qptSplit/axis")?;
        let cut = Q::from_lit(&self.q_lit(cut, "qptSplit/cut")?);
        let lo_elem = self.elem(lo, "qptSplit/lo")?;
        let hi_elem = self.elem(hi, "qptSplit/hi")?;
        path.push(elem);
        let lo = self.decode_tree(lo_elem, path)?;
        let hi = self.decode_tree(hi_elem, path)?;
        path.pop();
        Ok(PatchTree::Split {
            axis,
            cut,
            lo: Box::new(lo),
            hi: Box::new(hi),
        })
    }

    /// Decode a QGridCx element.
    fn decode_cx(&mut self, elem: u32) -> DecResult<GridCx> {
        let row = self.sole(elem, "QGridCx")?.clone();
        if row.fun != self.v.qgc_mk {
            return refuse("grid-complex element not constructed by qgcMk");
        }
        let [dom, tree] = row.args.as_slice() else {
            return refuse("qgcMk row arity mismatch");
        };
        let dom_elem = self.elem(dom, "qgcMk/dom")?;
        let tree_elem = self.elem(tree, "qgcMk/tree")?;
        let dom = self.decode_box(dom_elem)?;
        let mut path = Vec::new();
        let tree = self.decode_tree(tree_elem, &mut path)?;
        Ok(GridCx { dom, tree })
    }
}

/// Locate the sole subject carrying a given attribute fun among the
/// bundle's ops (the entity-sort location pass: `QMorse` and
/// `QMorseDischarge` are attribute-defined).
fn sole_subject(ops: &[Op], rows: &CertRows, fun: Chid, what: &str) -> DecResult<u32> {
    let mut found: Option<u32> = None;
    for op in ops {
        let Op::Funa {
            fun: f,
            args,
            value: _,
        } = op
        else {
            continue;
        };
        if rows.norm(f) != fun {
            continue;
        }
        let Some(Value::Ref(r)) = args.first() else {
            continue;
        };
        let Some(subject) = rows.local(r) else {
            continue;
        };
        match found {
            None => found = Some(subject),
            Some(prev) if prev == subject => {}
            Some(_) => {
                return refuse(format!(
                    "multiple `{what}` subjects in one certificate object — the v0 bundle \
                     grammar admits exactly one"
                ))
            }
        }
    }
    match found {
        Some(s) => Ok(s),
        None => refuse(format!("no `{what}` subject in the certificate object")),
    }
}

/// Step 1 in full: rows → [`DecodedBundle`] + the consumption evidence
/// the closure check (step 2) sweeps against.
fn decode_bundle(
    vocab: &ArenaVocab,
    ops: &[Op],
    rows: &CertRows,
) -> DecResult<(DecodedBundle, Consumed)> {
    let morse_elem = sole_subject(ops, rows, vocab.morse_graph, "QMorse/graph")?;
    let discharge_elem = sole_subject(ops, rows, vocab.dis_lattice, "QMorseDischarge/lattice")?;

    let mut d = Dec {
        v: vocab,
        rows,
        steps: 0,
        used: Consumed::default(),
    };

    // The judgement record's kit halves.
    let graph_attr = d.sole_attr(morse_elem, vocab.morse_graph, "QMorse/graph")?;
    let rho_attr = d.sole_attr(morse_elem, vocab.morse_rho, "QMorse/rho")?;
    let arena_attr = d.sole_attr(morse_elem, vocab.morse_arena, "QMorse/arena")?;
    let dag_elem = d.elem(&graph_attr.value.clone(), "QMorse/graph value")?;
    let rho_elem = d.elem(&rho_attr.value.clone(), "QMorse/rho value")?;
    let morse_arena_elem = d.elem(&arena_attr.value.clone(), "QMorse/arena value")?;

    // The discharge record's kit halves.
    let lat_attr = d.sole_attr(discharge_elem, vocab.dis_lattice, "QMorseDischarge/lattice")?;
    let h_attr = d.sole_attr(discharge_elem, vocab.dis_h, "QMorseDischarge/h")?;
    let lattice_elem = d.elem(&lat_attr.value.clone(), "QMorseDischarge/lattice value")?;
    let h_elem = d.elem(&h_attr.value.clone(), "QMorseDischarge/h value")?;

    // dag: qdagMk [edges, vertices].
    let dag_row = d.sole(dag_elem, "QDag")?.clone();
    if dag_row.fun != vocab.qdag_mk {
        return refuse("dag element not constructed by qdagMk");
    }
    let [edges_val, vertices_val] = dag_row.args.as_slice() else {
        return refuse("qdagMk row arity mismatch");
    };
    let dag_vertices = d.nat(vertices_val, "qdagMk/vertices")?;
    let edges_elem = d.elem(edges_val, "qdagMk/edges")?;
    let dag_edges = d.walk_list(
        edges_elem,
        vocab.qde_nil,
        vocab.qde_cons,
        "QDagEdgeList",
        |d, row| {
            let [dst, src, tail] = row.args.as_slice() else {
                return refuse("qdeCons row arity mismatch");
            };
            let pair = (d.nat(src, "qdeCons/src")?, d.nat(dst, "qdeCons/dst")?);
            let tail = d.elem(tail, "qdeCons/tail")?;
            Ok((pair, tail))
        },
    )?;

    // h: the two-cons cellmap walk.
    let h = {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = h_elem;
        loop {
            if !visited.insert(cur) {
                return refuse(format!(
                    "element {cur} recurs along its own QCellMap tail (P-ACYCLIC territory)"
                ));
            }
            let row = d.sole(cur, "QCellMap")?;
            if row.fun == vocab.qcm_nil {
                break out;
            }
            if row.fun == vocab.qcm_vertex {
                let [cell, tail, vertex] = row.args.as_slice() else {
                    return refuse("qcmVertex row arity mismatch");
                };
                out.push(HEntry::Vertex {
                    cell: d.nat(cell, "qcmVertex/cell")?,
                    vertex: d.nat(vertex, "qcmVertex/vertex")?,
                });
                cur = d.elem(tail, "qcmVertex/tail")?;
            } else if row.fun == vocab.qcm_transit {
                let [cell, tail] = row.args.as_slice() else {
                    return refuse("qcmTransit row arity mismatch");
                };
                out.push(HEntry::Transit {
                    cell: d.nat(cell, "qcmTransit/cell")?,
                });
                cur = d.elem(tail, "qcmTransit/tail")?;
            } else {
                return refuse("cellmap element constructed outside the QCellMap roster");
            }
        }
    };

    // The lattice: cx + arena + blocks.
    let cx_attr = d.sole_attr(lattice_elem, vocab.lat_cx, "QBlockLattice/cx")?;
    let arena_lat_attr = d.sole_attr(lattice_elem, vocab.lat_arena, "QBlockLattice/arena")?;
    let blocks_attr = d.sole_attr(lattice_elem, vocab.lat_blocks, "QBlockLattice/blocks")?;
    let cx_elem = d.elem(&cx_attr.value.clone(), "QBlockLattice/cx value")?;
    let arena = d.shape(&arena_lat_attr.value.clone(), "QBlockLattice/arena")?;
    let blocks_elem = d.elem(&blocks_attr.value.clone(), "QBlockLattice/blocks value")?;

    let cx = d.decode_cx(cx_elem)?;

    let block_rows = d.walk_list(
        blocks_elem,
        vocab.qb_nil,
        vocab.qb_cons,
        "QBlockList",
        |d, row| {
            let [cells, facets, tail] = row.args.as_slice() else {
                return refuse("qbCons row arity mismatch");
            };
            let cells = d.shape(cells, "qbCons/cells")?;
            let facets = d.elem(facets, "qbCons/facets")?;
            let tail = d.elem(tail, "qbCons/tail")?;
            Ok(((cells, facets), tail))
        },
    )?;
    let mut blocks = Vec::with_capacity(block_rows.len());
    for (cells, facets_elem) in block_rows {
        // The rev 2 generalized facet descriptor, degenerate reading:
        // group = axis, facet 0 = lower / 1 = upper (any other facet
        // index refuses at v0 decode — no simplex cells exist below
        // the mixed profile).
        let facets = d.walk_list(
            facets_elem,
            vocab.qf_nil,
            vocab.qf_cons,
            "QFacetList",
            |d, row| {
                let [cells, facet, group, proof, tail] = row.args.as_slice() else {
                    return refuse("qfCons row arity mismatch");
                };
                if !matches!(proof, Value::Ref(_)) {
                    return refuse("qfCons/proof is not an element ref — malformed rows");
                }
                let facet_idx = d.nat(facet, "qfCons/facet")?;
                if facet_idx > 1 {
                    return refuse(
                        "qfCons/facet outside the degenerate 0/1 (lower/upper) range — \
                         simplex facets await the mixed profile",
                    );
                }
                // morse::FacetRow carries the generalized (group,
                // facet) descriptor natively since the staged-vocabulary
                // oracle adaptation landed.
                let f = FacetRow {
                    group: d.nat(group, "qfCons/group")?,
                    facet: facet_idx,
                    cells: d.shape(cells, "qfCons/cells")?,
                };
                let tail = d.elem(tail, "qfCons/tail")?;
                Ok((f, tail))
            },
        )?;
        blocks.push(BlockData { cells, facets });
    }

    // rho: (vertex, region) pairs — region elems collected here,
    // classified at R1 assembly (the shared recognizer, the shared-recognizer contract);
    // subtree OWNERSHIP for the closure step rides
    // [`own_region_rows`]'s sort-tracked walk.
    let rho = d.walk_list(
        rho_elem,
        vocab.qvr_nil,
        vocab.qvr_cons,
        "QVertexRegionList",
        |d, row| {
            let [region, tail, vertex] = row.args.as_slice() else {
                return refuse("qvrCons row arity mismatch");
            };
            let vertex = d.nat(vertex, "qvrCons/vertex")?;
            let region = d.elem(region, "qvrCons/region")?;
            let tail = d.elem(tail, "qvrCons/tail")?;
            Ok(((vertex, region), tail))
        },
    )?;

    // The judgement's arena pair (the chase equation's object).
    let arena_row = d.sole(morse_arena_elem, "QArena")?.clone();
    if arena_row.fun != vocab.qar_mk {
        return refuse("judgment arena element not constructed by qarMk");
    }
    let [ar_cells, ar_cx] = arena_row.args.as_slice() else {
        return refuse("qarMk row arity mismatch");
    };
    let morse_arena = ArenaValue {
        elem: morse_arena_elem,
        cells: d.shape(ar_cells, "qarMk/cells")?,
        cx_elem: d.elem(ar_cx, "qarMk/cx")?,
    };
    // The judgement's cited arena complex is REACHABLE from the
    // selected roots, so it is part of the object closure (review finding) and its structure decodes here: in the tied case
    // hash-consing makes it the very element already walked for the
    // lattice; a structurally distinct citation decodes as rows and
    // then refuses at the chase's syntactic tie (never as an
    // unowned-row escape); a dangling citation refuses here
    // (refuse-not-guess).
    let _ = d.decode_cx(morse_arena.cx_elem)?;

    // The v0 object-graph linkage chain (review finding): the
    // selected records must be bound by a unique local
    // `QMorseDischarge/proof → QProof/concludes → QMorse/judgment`
    // chain, refused BEFORE R1 and the chase on any defect.
    let (proof_elem, judgment_elem) = decode_linkage(&mut d, vocab, morse_elem, discharge_elem)?;

    Ok((
        DecodedBundle {
            morse_elem,
            discharge_elem,
            lattice_elem,
            cx_elem,
            cx,
            arena,
            blocks,
            dag_vertices,
            dag_edges,
            h,
            rho,
            morse_arena,
            proof_elem,
            judgment_elem,
        },
        d.used,
    ))
}

/// The v0 linkage rule (review finding): decode the unique local chain binding the SELECTED records —
/// `discharge --QMorseDischarge/proof--> p --QProof/concludes--> J`
/// and `morse --QMorse/judgment--> J'` with `J = J'` — refusing
/// missing, ambiguous, external, or mismatched links with the
/// [`LinkageViolation`] class. Axiom semantics are untouched: this
/// tightens the certificate-object GRAMMAR, not the chase.
fn decode_linkage(
    d: &mut Dec<'_>,
    vocab: &ArenaVocab,
    morse_elem: u32,
    discharge_elem: u32,
) -> Result<(u32, u32), AdmissionRefusal> {
    let proof_val = unique_link(d, discharge_elem, vocab.dis_proof, "QMorseDischarge/proof")?;
    let proof_elem = link_local(d.rows, &proof_val, "QMorseDischarge/proof")?;
    let concl_val = unique_link(d, proof_elem, vocab.concludes, "QProof/concludes")?;
    let concl_elem = link_local(d.rows, &concl_val, "QProof/concludes")?;
    let judg_val = unique_link(d, morse_elem, vocab.morse_judgment, "QMorse/judgment")?;
    let judg_elem = link_local(d.rows, &judg_val, "QMorse/judgment")?;
    if concl_elem != judg_elem {
        return Err(AdmissionRefusal::Linkage(LinkageViolation::Mismatch));
    }
    Ok((proof_elem, judg_elem))
}

/// One chain fun, one subject: the unique row, with Linkage-class
/// refusals (the decode's `sole_attr` speaks the Decode class; the
/// chain has its own adjudicated vocabulary). Consumption registered.
fn unique_link(
    d: &mut Dec<'_>,
    subject: u32,
    fun: Chid,
    what: &'static str,
) -> Result<Value, AdmissionRefusal> {
    let mut found: Option<&AttrRow> = None;
    for row in d.rows.attrs(subject) {
        if row.fun != fun {
            continue;
        }
        if found.is_some() {
            return Err(AdmissionRefusal::Linkage(LinkageViolation::Ambiguous {
                what,
            }));
        }
        found = Some(row);
    }
    match found {
        Some(r) => {
            d.used.attrs.insert((subject, fun));
            Ok(r.value.clone())
        }
        None => Err(AdmissionRefusal::Linkage(LinkageViolation::MissingRow {
            what,
        })),
    }
}

/// A chain link must stay inside the body (single-body context) and be
/// an element ref at all.
fn link_local(rows: &CertRows, v: &Value, what: &'static str) -> Result<u32, AdmissionRefusal> {
    match v {
        Value::Ref(r) => {
            rows.local(r)
                .ok_or(AdmissionRefusal::Linkage(LinkageViolation::External {
                    what,
                }))
        }
        _ => Err(AdmissionRefusal::Linkage(LinkageViolation::NotAnElem {
            what,
        })),
    }
}

// ---------------------------------------------------------------------
// Step 3a: generator validity (version-independent; the exact
// strictness statement is in the module docs)
// ---------------------------------------------------------------------

/// Check GV1–GV6 over a decoded complex. Public so the Lean
/// generator-validity statement has a named Rust twin to disagree with.
pub fn generator_validity(cx: &GridCx) -> Result<(), GenViolation> {
    let n = cx.dom.len();
    // GV1.
    if n == 0 {
        return Err(GenViolation::ZeroDim);
    }
    for (k, (lo, hi, _, _)) in cx.dom.iter().enumerate() {
        if !lo.lt(hi) {
            return Err(GenViolation::DegenerateDomAxis { axis: k });
        }
    }
    // Walk the tree with derived per-axis bounds.
    let bounds: Vec<(Q, Q)> = cx
        .dom
        .iter()
        .map(|(lo, hi, _, _)| (lo.clone(), hi.clone()))
        .collect();
    validity_walk(&cx.tree, n, bounds)
}

fn validity_walk(tree: &PatchTree, n: usize, bounds: Vec<(Q, Q)>) -> Result<(), GenViolation> {
    match tree {
        PatchTree::Split { axis, cut, lo, hi } => {
            let k = usize::try_from(*axis).unwrap_or(usize::MAX);
            if k >= n {
                return Err(GenViolation::SplitAxisRange { axis: *axis });
            }
            // GV2 — STRICT interiority, both sides (the endpoint-cut
            // fix's checker half).
            let (blo, bhi) = &bounds[k];
            if !(blo.lt(cut) && cut.lt(bhi)) {
                return Err(GenViolation::EndpointCut { axis: *axis });
            }
            let mut lo_bounds = bounds.clone();
            lo_bounds[k].1 = cut.clone();
            let mut hi_bounds = bounds;
            hi_bounds[k].0 = cut.clone();
            validity_walk(lo, n, lo_bounds)?;
            validity_walk(hi, n, hi_bounds)
        }
        PatchTree::Leaf(leaf) => validity_leaf(leaf, n, &bounds),
    }
}

fn validity_leaf(leaf: &PatchLeaf, n: usize, bounds: &[(Q, Q)]) -> Result<(), GenViolation> {
    // GV3: length-n RGS-canonical.
    if leaf.part.len() != n {
        return Err(GenViolation::PartitionWire {
            why: format!(
                "partition length {} ≠ ambient dimension {n}",
                leaf.part.len()
            ),
        });
    }
    if leaf.part[0] != 0 {
        return Err(GenViolation::PartitionWire {
            why: "part[0] ≠ 0".into(),
        });
    }
    let mut max_so_far = 0u64;
    for (k, &p) in leaf.part.iter().enumerate().skip(1) {
        if p > max_so_far + 1 {
            return Err(GenViolation::PartitionWire {
                why: format!("part[{k}] = {p} skips a label (max so far {max_so_far})"),
            });
        }
        max_so_far = max_so_far.max(p);
    }
    let g = usize::try_from(1 + max_so_far).expect("group count bounded by n");
    // GV4.
    if leaf.gens.len() != g {
        return Err(GenViolation::GenListAlignment {
            expected: g,
            found: leaf.gens.len(),
        });
    }
    // GV5 + GV6.
    for (j, gen) in leaf.gens.iter().enumerate() {
        let fiber: Vec<usize> = leaf
            .part
            .iter()
            .enumerate()
            .filter(|(_, &p)| p as usize == j)
            .map(|(k, _)| k)
            .collect();
        match gen {
            GroupGen::Interval { cuts } => {
                if fiber.len() != 1 {
                    return Err(GenViolation::GeneratorKindFiber {
                        group: j,
                        fiber: fiber.len(),
                    });
                }
                let k = fiber[0];
                let (blo, bhi) = &bounds[k];
                let mut prev = blo;
                for (c, _) in cuts {
                    if !prev.lt(c) {
                        return Err(GenViolation::IntervalCuts { group: j });
                    }
                    prev = c;
                }
                if !prev.lt(bhi) {
                    return Err(GenViolation::IntervalCuts { group: j });
                }
            }
            GroupGen::Kuhn { res, splits } => {
                if !(fiber.len() == 2 || fiber.len() == 3) {
                    return Err(GenViolation::GeneratorKindFiber {
                        group: j,
                        fiber: fiber.len(),
                    });
                }
                // The Kuhn-payload admission obligations (review finding):
                // len(res) = |G_j|, entries ≥ 1, len(splits) = Π res.
                if res.len() != fiber.len() {
                    return Err(GenViolation::KuhnResLen {
                        group: j,
                        expected: fiber.len(),
                        found: res.len(),
                    });
                }
                if let Some(index) = res.iter().position(|&r| r == 0) {
                    return Err(GenViolation::KuhnResEntry { group: j, index });
                }
                // Saturating product: a genuinely-saturated product can
                // never equal a decoded list length (decode budget
                // bounds it far below u64::MAX), so saturation refuses
                // through the same comparison.
                let expected = res.iter().fold(1u64, |a, &r| a.saturating_mul(r));
                if splits.len() as u64 != expected {
                    return Err(GenViolation::KuhnSplitsLen {
                        group: j,
                        expected,
                        found: splits.len(),
                    });
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Step 3b: the versioned profile
// ---------------------------------------------------------------------

/// The versioned capability-profile gate (run AFTER generator
/// validity). On the versions that admit only degenerate complexes it
/// also performs the Shape range checks against the derived cell
/// count (the Shape index-domain registry's admission column).
pub fn profile_check(
    version: ProfileVersion,
    bundle: &DecodedBundle,
) -> Result<(), ProfileViolation> {
    let leaf = match &bundle.cx.tree {
        PatchTree::Leaf(l) => l,
        PatchTree::Split { .. } => return Err(ProfileViolation::SingleLeafRequired),
    };
    // All-singleton partition (every current version; mixed complexes
    // await the mixed-complex recompute machinery as their own version event).
    let n = bundle.cx.dom.len();
    for j in 0..leaf.gens.len() {
        let fiber = leaf.part.iter().filter(|&&p| p as usize == j).count();
        if fiber != 1 {
            return Err(ProfileViolation::NonSingletonGroup { group: j });
        }
    }
    debug_assert_eq!(leaf.gens.len(), n, "GV3+GV4+all-singleton force g = n");
    // Chart gate — the axis `V1WidenedChartForTest` widens.
    if version == ProfileVersion::V0 && leaf.chart != ChartRef::Identity {
        return Err(ProfileViolation::NonIdentityChart);
    }
    // Shape ranges against the derived cell count.
    let cell_count = degenerate_cell_count(leaf);
    let check = |what: &'static str, xs: &[u64]| -> Result<(), ProfileViolation> {
        for &x in xs {
            if x >= cell_count {
                return Err(ProfileViolation::ShapeRange {
                    what,
                    index: x,
                    cell_count,
                });
            }
        }
        Ok(())
    };
    check("QBlockLattice/arena", &bundle.arena)?;
    check("qarMk/cells", &bundle.morse_arena.cells)?;
    for b in &bundle.blocks {
        check("qbCons/cells", &b.cells)?;
        for f in &b.facets {
            check("qfCons/cells", &f.cells)?;
        }
    }
    Ok(())
}

/// Per-axis cell counts of a degenerate (all-singleton) leaf under the
/// interior-only cut convention: `cuts.len() + 1` cells per axis.
/// (The vocabulary staging landed the interior-only reading; the once-hedged
/// endpoint-inclusive contingency is retired. Isolated here with
/// [`derive_degenerate_grid`] as the one place the convention lives.)
fn degenerate_cell_count(leaf: &PatchLeaf) -> u64 {
    let mut total: u64 = 1;
    for gen in &leaf.gens {
        let per_axis = match gen {
            GroupGen::Interval { cuts } => cuts.len() as u64 + 1,
            GroupGen::Kuhn { .. } => unreachable!("all-singleton profile has no Kuhn groups"),
        };
        total = total.saturating_mul(per_axis);
    }
    total
}

// ---------------------------------------------------------------------
// Step 4: mandatory R1 (the recompute runs at admission)
// ---------------------------------------------------------------------

/// Assemble the degenerate complex into the R1 oracle's kit form:
/// per-axis cut lists = derived sub-box endpoints + interior cuts
/// (axis order = group order — identical under all-singleton
/// canonical partitions, where group j IS axis j).
///
/// The gens are aligned by group index; ρ regions ride Opaque (module
/// docs, integration seams).
fn derive_degenerate_grid(cx: &GridCx, leaf: &PatchLeaf) -> Vec<Vec<Literal>> {
    let mut grid = Vec::with_capacity(cx.dom.len());
    for (k, (_, _, lo_lit, hi_lit)) in cx.dom.iter().enumerate() {
        let mut cuts = Vec::new();
        cuts.push(lo_lit.clone());
        if let GroupGen::Interval { cuts: interior } = &leaf.gens[k] {
            for (_, lit) in interior {
                cuts.push(lit.clone());
            }
        }
        cuts.push(hi_lit.clone());
        grid.push(cuts);
    }
    grid
}

fn run_r1(v: &ArenaVocab, rows: &CertRows, bundle: &DecodedBundle) -> Result<(), AdmissionRefusal> {
    let leaf = match &bundle.cx.tree {
        PatchTree::Leaf(l) => l,
        PatchTree::Split { .. } => {
            // Unreachable behind the current profiles; stated as a
            // refusal (never a guess) should a future version arm
            // forget its recompute machinery.
            return Err(AdmissionRefusal::R1Refused(
                "no recompute machinery for multi-patch complexes at this version".into(),
            ));
        }
    };
    let grid = derive_degenerate_grid(&bundle.cx, leaf);
    let d_axes = grid.len();
    let grid_counts: Vec<u64> = grid.iter().map(|c| (c.len().max(1) - 1) as u64).collect();
    // The ρ lane (the shared-recognizer contract, review finding): classify every region
    // through the SAME recognizer the staged R1 decoder runs, so
    // box-aligned regions face their containment/overlap checks at
    // admission too. A classification refusal (undecidable structure,
    // exhausted budget) refuses the bundle — refuse-not-guess, in R1's
    // refusal stratum.
    let mut steps = 0usize;
    let mut rho = Vec::with_capacity(bundle.rho.len());
    for (vertex, region_elem) in &bundle.rho {
        let class = classify_region(
            &v.region,
            rows,
            &mut steps,
            MAX_ADMISSION_DECODE_STEPS,
            *region_elem,
            d_axes,
            &grid_counts,
            &grid,
        )
        .map_err(AdmissionRefusal::R1Refused)?;
        rho.push((*vertex, class));
    }
    let kit = MorseKit {
        grid,
        arena: bundle.arena.clone(),
        blocks: bundle.blocks.clone(),
        dag_vertices: bundle.dag_vertices,
        dag_edges: bundle.dag_edges.clone(),
        h: bundle.h.clone(),
        rho,
    };
    match check_kit(&kit) {
        Ok(Ok(_readout)) => Ok(()),
        Ok(Err(violation)) => Err(AdmissionRefusal::R1(violation)),
        Err(why) => Err(AdmissionRefusal::R1Refused(why)),
    }
}

// ---------------------------------------------------------------------
// Step 2a: the certificate-object closure (review finding)
// ---------------------------------------------------------------------

/// The object boundary IS the row boundary: every op in the body must
/// be a row the decode consumed. A green primary object plus ANY
/// unowned row — an unattached second complex, a stray constructor
/// row, a row with an external or unselected subject, a non-row op —
/// refuses the whole bundle, so nothing piggybacks into the published
/// index ([`AdmittedCert::rows`] serves exactly the closed object).
fn check_closure(
    vocab: &ArenaVocab,
    ops: &[Op],
    rows: &CertRows,
    used: &Consumed,
    bundle: &DecodedBundle,
) -> Result<(), AdmissionRefusal> {
    let roster = ctor_roster(vocab);
    // ρ subtree ownership: the recognizer classifies
    // regions at R1 with early-exit semantics, so consumption cannot
    // define ownership there — this sort-tracked reachability walk
    // does (see [`own_region_rows`]).
    let region_rows = own_region_rows(&vocab.region, rows, &bundle.rho);
    for (i, op) in ops.iter().enumerate() {
        let Op::Funa { fun, args, value } = op else {
            return Err(AdmissionRefusal::Closure(format!(
                "op {i} is not a fun-value row — the v0 certificate-object grammar is \
                 rows-only at this leg (declarations and other op kinds arrive with the \
                 production loader's own closure rules, as an explicit widening event)"
            )));
        };
        let f = rows.norm(fun);
        // Constructor reading: the sole consumed constructor row of a
        // walked element, or an owned ρ-subtree row.
        if let Value::Ref(ElemRef::Local(e)) = value {
            if used.ctor_elems.contains(e) && roster.contains(&f) {
                continue;
            }
            if region_rows.contains(&(*e, f)) {
                continue;
            }
        }
        // Attribute reading: a consumed `(subject, fun)` row. The
        // decode's `sole_attr`/`unique_link` uniqueness guarantees make
        // this pair-level check row-level: one pair, one row.
        if let Some(Value::Ref(ElemRef::Local(s))) = args.first() {
            if used.attrs.contains(&(*s, f)) {
                continue;
            }
        }
        return Err(AdmissionRefusal::Closure(format!(
            "op {i} is not part of the selected certificate object's closure — \
             unowned rows cannot ride a checked object into visibility (review finding)"
        )));
    }
    Ok(())
}

/// ρ-subtree ownership for the closure step: from each
/// region root, walk by TRACKED SORT — StateF at the root, SFList
/// under `SAnd`/`slCons` tails, StateF under `slCons` heads, Poly
/// under atom `poly` fields and `pTerm` tails — owning every producer
/// row whose fun sits in THAT sort's roster. Recursion happens only
/// through the recognizer's eight known constructors: a
/// rostered-but-unknown constructor (`SOr` kin — definite-Opaque at
/// classification) owns its row without recursing, so a STRUCTURED
/// opaque region's subtree stays unowned and refuses at closure (the
/// `rho_wf`'s future closure rules are a named widening event).
/// Ownership ≠ validation: the recognizer remains the classification
/// authority at R1, and a divergence here can only ADD a refusal.
fn own_region_rows(rv: &RegionVocab, rows: &CertRows, rho: &[(u64, u32)]) -> HashSet<(u32, Chid)> {
    // Sort tags: 0 = StateF, 1 = SFList, 2 = Poly, 3 = StateObservable
    // (post-grid closures only: the atoms' oPoly hop).
    let mut owned: HashSet<(u32, Chid)> = HashSet::new();
    let mut stack: Vec<(u32, u8)> = rho.iter().map(|(_, e)| (*e, 0u8)).collect();
    let mut visited: HashSet<(u32, u8)> = HashSet::new();
    while let Some((e, sort)) = stack.pop() {
        if !visited.insert((e, sort)) {
            continue;
        }
        let roster = match sort {
            0 => &rv.statef_roster,
            1 => &rv.sflist_roster,
            3 => &rv.stateobs_roster,
            _ => &rv.poly_roster,
        };
        for row in rows.producers(e) {
            if !roster.contains(&row.fun) {
                continue;
            }
            owned.insert((e, row.fun));
            // Structural recursion — the eight known constructors only.
            if row.fun == rv.s_and {
                if let [Value::Ref(r)] = row.args.as_slice() {
                    if let Some(le) = rows.local(r) {
                        stack.push((le, 1));
                    }
                }
            } else if row.fun == rv.sl_cons {
                if let [head, tail] = row.args.as_slice() {
                    if let Value::Ref(r) = head {
                        if let Some(he) = rows.local(r) {
                            stack.push((he, 0));
                        }
                    }
                    if let Value::Ref(r) = tail {
                        if let Some(te) = rows.local(r) {
                            stack.push((te, 1));
                        }
                    }
                }
            } else if row.fun == rv.s_atom_le || row.fun == rv.s_atom_ge {
                if let [_c, Value::Ref(r)] = row.args.as_slice() {
                    if let Some(pe) = rows.local(r) {
                        // Post-grid the atom's argument is an
                        // observable (tag 3); legacy it is the
                        // polynomial directly.
                        stack.push((pe, if rv.o_poly.is_some() { 3 } else { 2 }));
                    }
                }
            } else if Some(row.fun) == rv.o_poly {
                if let [Value::Ref(r)] = row.args.as_slice() {
                    if let Some(pe) = rows.local(r) {
                        stack.push((pe, 2));
                    }
                }
            } else if row.fun == rv.p_term {
                if let [_coeff, _expts, Value::Ref(r)] = row.args.as_slice() {
                    if let Some(te) = rows.local(r) {
                        stack.push((te, 2));
                    }
                }
            }
            // s_true / sl_nil / p_zero: nullary; other rostered
            // constructors: owned, no recursion (see the doc above).
        }
    }
    owned
}

// ---------------------------------------------------------------------
// Step 2b: staged-schema conformance + global P-FUN (review finding) +
// element-reference typing (review finding)
// ---------------------------------------------------------------------

/// One cell against one staged sort: elem-sorted cells must be element
/// refs; ground-sorted cells must be literals of exactly that ground.
/// KIND only, by design: elem-sort IDENTITY (which sort a cited
/// element inhabits) is per-element data, not per-cell data, so it is
/// established by [`check_schema`]'s obligation resolution — producer
/// codomains for constructed elements, nominal-sort consistency for
/// everything else (review finding). Public so the test suite's typed
/// fixture builder validates its emissions with THE SAME predicate the
/// door runs (the artefact-pair: a fixture the builder accepts and the
/// door refuses, or vice versa, indicts one of them).
pub fn cell_conforms(sort: &SortKey, val: &Value) -> Result<(), String> {
    match sort {
        SortKey::Elem(_) => match val {
            Value::Ref(_) => Ok(()),
            _ => Err("expected an element ref".into()),
        },
        SortKey::Ground(g) => {
            let err = || Err(format!("expected a {} literal", g.name()));
            let Value::Lit(l) = val else {
                return err();
            };
            // The certificate grammar's ground set; other grounds
            // (Date/Interval/Timestamp/EnnRat …) have no position in
            // this vocabulary and fall through to the refusal.
            let ok = matches!(
                (g, l.view()),
                (Ground::Q, LiteralView::Q { .. })
                    | (Ground::Nat, LiteralView::Nat(_))
                    | (Ground::Z, LiteralView::Z(_))
                    | (Ground::B, LiteralView::B(_))
                    | (Ground::Str, LiteralView::Str(_))
                    | (Ground::Shape, LiteralView::Shape(_))
            );
            if ok {
                Ok(())
            } else {
                err()
            }
        }
        // No tensor-sorted position exists in the certificate grammar;
        // refuse-not-guess should one ever reach admission.
        SortKey::TensorOf(_) => {
            Err("tensor-sorted cells are outside the admission grammar at this leg".into())
        }
    }
}

/// A cited element in a schema-checked elem-sorted cell, retained past
/// the row loop so the obligation-resolution phase can key by
/// normalized identity and speak the citation's own vocabulary in
/// refusals (review finding).
#[derive(Clone, Copy)]
enum CitedElem {
    Local(u32),
    External { dep_index: u32, counter: u32 },
}

impl CitedElem {
    fn of(r: &ElemRef) -> CitedElem {
        match r {
            ElemRef::Local(e) => CitedElem::Local(*e),
            ElemRef::External { dep_index, counter } => CitedElem::External {
                dep_index: *dep_index,
                counter: *counter,
            },
        }
    }

    fn as_elem_ref(&self) -> ElemRef {
        match self {
            CitedElem::Local(e) => ElemRef::Local(*e),
            CitedElem::External { dep_index, counter } => ElemRef::External {
                dep_index: *dep_index,
                counter: *counter,
            },
        }
    }
}

impl std::fmt::Display for CitedElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CitedElem::Local(e) => write!(f, "element {e}"),
            CitedElem::External { dep_index, counter } => {
                write!(f, "external element (dep {dep_index}, elem {counter})")
            }
        }
    }
}

/// Step 2b: every row of the (closure-checked) body conforms to its
/// fun's STAGED signature, and constructor production is globally
/// unique per element ACROSS roster families (review finding).
///
/// Runs AFTER the ownership closure (step 2a), so every row here has a
/// known fun: unknown funs already refused as unowned, and the refusal
/// classes of the closure batteries are undisturbed. Five checks:
///
/// 1. **row conformance** — arity, per-cell kind against the staged
///    argument sorts (wire order), value cell against the codomain;
/// 2. **external-reference validity** (review finding) — every external
///    element ref in a schema-checked cell cites an in-range dep
///    index. Deeper dep-typing — resolving the ref against the
///    admitted dependency's own sort — is a NAMED WIDENING OBLIGATION
///    on the first production loader: deps are bare hashes at this
///    door pre-byte, so cross-commit sort witnesses do not exist yet,
///    and the in-range check plus check 5's internal consistency are
///    the whole of what the raw door can honestly establish;
/// 3. **global P-FUN** — at most one producer row per element across
///    the arena roster AND the region rosters (the projection-side
///    conformance row, enforced at the gate rather than assumed —
///    `rowctx.rs`'s malformation posture says evaluation cannot assume
///    it, so admission must establish it);
/// 4. **elem-sort cross-check, anchored** — an elem-sorted cell citing
///    a LOCAL element with a (unique, per check 3) rostered producer
///    must cite one whose codomain is that sort;
/// 5. **per-element nominal-sort consistency** (review finding) — every
///    OTHER cited element (bare locals — entity records, proof refs —
///    and in-range external refs, keyed by normalized identity)
///    carries ONE sort across the whole body: the first elem-sorted
///    citation binds, and any later citation at a different sort chid
///    refuses. One element inhabits one staged sort; the pre-r4 door
///    assigned this to "the decode/closure steps' obligation", which
///    neither step discharged — decode establishes linkage and
///    closure ownership, not nominal sorts.
fn check_schema(
    vocab: &ArenaVocab,
    ops: &[Op],
    rows: &CertRows,
    deps: &[[u8; 32]],
) -> Result<(), AdmissionRefusal> {
    let arena_roster = ctor_roster(vocab);
    let rv = &vocab.region;
    let is_producer_fun = |f: &Chid| {
        arena_roster.contains(f)
            || rv.statef_roster.contains(f)
            || rv.sflist_roster.contains(f)
            || rv.poly_roster.contains(f)
            || rv.stateobs_roster.contains(f)
    };
    let fmt_chid = |c: &Chid| format!("({:02x}{:02x}…, {})", c.0[0], c.0[1], c.1);

    let mut producer: HashMap<u32, Chid> = HashMap::new();
    // (op index, cited element, expected sort chid) — resolved after
    // the producer census completes. Body order is preserved so the
    // first offending citation refuses, deterministically.
    let mut sort_obligations: Vec<(usize, CitedElem, Chid)> = Vec::new();
    // Check 2: an external ref in a schema-checked cell must cite an
    // in-range dep index (the dangling `qfCons/proof` witness — decode
    // checks that cell only as is-a-ref and discards it).
    let check_external = |i: usize, r: &ElemRef, place: &str, f: &Chid| {
        if let ElemRef::External { dep_index, .. } = r {
            if *dep_index as usize >= deps.len() {
                return Err(AdmissionRefusal::Schema(format!(
                    "op {i}: {place} of fun {}: external element ref cites dep index \
                     {dep_index} where the body carries {} dependency hash(es) — a \
                     dangling cross-commit reference cannot be admitted",
                    fmt_chid(f),
                    deps.len()
                )));
            }
        }
        Ok(())
    };

    for (i, op) in ops.iter().enumerate() {
        let Op::Funa { fun, args, value } = op else {
            // Non-row ops refused at closure (step 2a).
            continue;
        };
        let f = rows.norm(fun);
        let Some(sig) = vocab.schema.funs.get(&f) else {
            return Err(AdmissionRefusal::Schema(format!(
                "op {i}: fun {} has no staged signature in the admission vocabulary — \
                 conformance cannot be checked, fail-closed",
                fmt_chid(&f)
            )));
        };
        let sorts = sig.domain.arg_sorts();
        if args.len() != sorts.len() {
            return Err(AdmissionRefusal::Schema(format!(
                "op {i}: fun {} carries {} argument cell(s) where the staged signature \
                 declares {}",
                fmt_chid(&f),
                args.len(),
                sorts.len()
            )));
        }
        for (k, (cell, sort)) in args.iter().zip(sorts.iter()).enumerate() {
            cell_conforms(sort, cell).map_err(|why| {
                AdmissionRefusal::Schema(format!(
                    "op {i}: argument cell {k} of fun {}: {why}",
                    fmt_chid(&f)
                ))
            })?;
            if let (SortKey::Elem(c), Value::Ref(r)) = (sort, cell) {
                check_external(i, r, &format!("argument cell {k}"), &f)?;
                sort_obligations.push((i, CitedElem::of(r), *c));
            }
        }
        match &sig.codomain {
            Some(sk) => {
                cell_conforms(sk, value).map_err(|why| {
                    AdmissionRefusal::Schema(format!(
                        "op {i}: value cell of fun {}: {why}",
                        fmt_chid(&f)
                    ))
                })?;
                if let (SortKey::Elem(c), Value::Ref(r)) = (sk, value) {
                    check_external(i, r, "value cell", &f)?;
                    sort_obligations.push((i, CitedElem::of(r), *c));
                }
            }
            None => {
                return Err(AdmissionRefusal::Schema(format!(
                    "op {i}: fun {} is relational in the staged theory — a relational \
                     row is not certificate-object grammar",
                    fmt_chid(&f)
                )))
            }
        }
        if is_producer_fun(&f) {
            if let Value::Ref(ElemRef::Local(e)) = value {
                if let Some(prev) = producer.insert(*e, f) {
                    return Err(AdmissionRefusal::Schema(format!(
                        "element {e} is produced by two rostered constructor rows — \
                         {} and {} — global P-FUN uniqueness holds at the gate, across \
                         roster families",
                        fmt_chid(&prev),
                        fmt_chid(&f)
                    )));
                }
            }
        }
    }

    // Obligation resolution, in body order (first offence refuses,
    // deterministically). Check 4 anchors produced elements to their
    // unique rostered producer's staged codomain; check 5 holds every
    // other cited element — bare locals and in-range externals, keyed
    // by normalized identity — to ONE sort across the body.
    let mut first_seen: HashMap<Chid, (usize, Chid)> = HashMap::new();
    for (i, cited, want) in sort_obligations {
        if let CitedElem::Local(e) = cited {
            if let Some(pf) = producer.get(&e) {
                let cod = vocab.schema.funs.get(pf).and_then(|s| s.codomain);
                if cod != Some(SortKey::Elem(want)) {
                    return Err(AdmissionRefusal::Schema(format!(
                        "op {i}: a cell sorted {} cites element {e}, whose producing \
                         constructor {} has a different codomain sort",
                        fmt_chid(&want),
                        fmt_chid(pf)
                    )));
                }
                continue;
            }
        }
        let key = rows.norm(&cited.as_elem_ref());
        match first_seen.get(&key) {
            None => {
                first_seen.insert(key, (i, want));
            }
            Some(&(j, prev)) => {
                if prev != want {
                    return Err(AdmissionRefusal::Schema(format!(
                        "op {i}: {cited} is cited at sort {} where op {j} cited it at \
                         sort {} — one element inhabits one staged sort (nominal \
                         element-sort consistency)",
                        fmt_chid(&want),
                        fmt_chid(&prev)
                    )));
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------

/// The full pipeline: decode (with linkage) → closure → staged-schema
/// conformance + global P-FUN → generator validity → versioned
/// profile → mandatory R1 → chase → the admitted value. Private: the
/// public doors below fix the policy
/// ([`admit_certificate`], [`CertStore::admit`]) or discard the
/// visibility ([`probe_admission`]).
fn run_pipeline(
    version: ProfileVersion,
    vocab: &ArenaVocab,
    ops: &[Op],
    own: [u8; 32],
    deps: &[[u8; 32]],
    chase: &dyn AdmissionChase,
) -> Result<AdmittedCert, AdmissionRefusal> {
    // Step 1: decode, including the v0 linkage chain (review repairs).
    let rows = CertRows::from_ops(ops, own, deps);
    let (bundle, used) = decode_bundle(vocab, ops, &rows)?;
    // Step 2a: the certificate-object closure (review finding).
    check_closure(vocab, ops, &rows, &used, &bundle)?;
    // Step 2b: staged-schema conformance + global P-FUN (review finding)
    // + element-reference typing (review finding).
    check_schema(vocab, ops, &rows, deps)?;
    // Step 3a: generator validity (version-independent).
    generator_validity(&bundle.cx).map_err(AdmissionRefusal::Generator)?;
    // Step 3b: the versioned profile.
    profile_check(version, &bundle)
        .map_err(|violation| AdmissionRefusal::Profile { version, violation })?;
    // Step 4: mandatory R1 (the ρ lane classifies through the shared
    // recognizer — the shared-recognizer contract).
    run_r1(vocab, &rows, &bundle)?;
    // Step 5: the chase.
    chase
        .check(&bundle, &rows)
        .map_err(AdmissionRefusal::Chase)?;
    // Step 6: visibility.
    Ok(AdmittedCert {
        version,
        rows,
        row_count: ops.len(),
        bundle,
    })
}

/// Atomic certificate admission through the PRODUCTION door (review finding): profile pinned to [`ProfileVersion::V0`], chase pinned to
/// the sealed [`ArenaEquationChase`] built from the vocabulary — no
/// policy parameters exist on this surface. Refusal at any step
/// returns `Err` and NOTHING of the bundle becomes reader-visible
/// ([`AdmittedCert`] is the only surface, and only the production
/// doors construct it).
pub fn admit_certificate(
    vocab: &ArenaVocab,
    ops: &[Op],
    own: [u8; 32],
    deps: &[[u8; 32]],
) -> Result<AdmittedCert, AdmissionRefusal> {
    let chase = ArenaEquationChase::new(vocab);
    run_pipeline(ProfileVersion::V0, vocab, ops, own, deps, &chase)
}

/// The NON-VISIBILITY diagnostic surface: run the full pipeline under
/// an arbitrary profile version and chase, returning only the verdict.
/// No [`AdmittedCert`] and no row index escape — a caller-implemented
/// [`AdmissionChase`] here can inspect its own input's decode, never
/// mint visibility (review finding). This is where the
/// widening-mechanism precedent ([`ProfileVersion::V1WidenedChartForTest`])
/// and [`NoChaseAxioms`] remain exercisable.
pub fn probe_admission(
    version: ProfileVersion,
    vocab: &ArenaVocab,
    ops: &[Op],
    own: [u8; 32],
    deps: &[[u8; 32]],
    chase: &dyn AdmissionChase,
) -> Result<(), AdmissionRefusal> {
    run_pipeline(version, vocab, ops, own, deps, chase).map(|_| ())
}

// ---------------------------------------------------------------------
// Sort-key helper for prospective from_indices consumers (kept private
// until a second caller wants it)
// ---------------------------------------------------------------------

#[allow(dead_code)]
fn is_elem(k: &SortKey) -> bool {
    matches!(k, SortKey::Elem(_))
}
