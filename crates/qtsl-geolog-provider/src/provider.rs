//! [`QtslGroundProvider`] — the QTSL application's one value at the
//! plugin seam.
//!
//! Curated expectation tables (claims: the name selects, the engine's
//! binder verifies signatures against declared theory rows) plus the
//! evaluator over this crate's certificate side-condition families.
//! Every relation here is `Scope::Snapshot`: the families are
//! row-context checks — they read the certificate's constructor rows,
//! which the engine supplies per evaluation, never the provider.
//!
//! # The claimed families
//!
//! **The applicability family** (16 relations): exact-rational
//! combination replay (`farkasCombinationValid`,
//! `syzygyCombinationValid`, `pBoundCombinationValid`), the PSD
//! certificate checks (`psdCertTWitness`/`psdCertTConcl`,
//! `psdCertDDWitness`/`psdCertDDConcl`,
//! `psdCertKWitness`/`psdCertKConcl`), wire-size positivity
//! (`positiveSizeWires`/`...Form`/`...Term`), polynomial canonical
//! forms (`polynomialCanonicalEq`), premise sub-conjunction
//! containment (`premiseContains`), the syzygy conclusion-form
//! selector (`syzygyConclusionFormRel`), and closed exact evaluation
//! (`constExactEvalTrue`). Evaluators: [`crate::blapplic`]; the Lean
//! catalogue (`lean/`) is the spec authority each mirrors.
//!
//! **The atomic-compare family** (2 relations): `atomicCompareForm`
//! and `atomicCompareZero`, the pinned syntactic-shape checks over
//! Formula/Term rows ([`crate::atomic`]).
//!
//! **The recompute families** (4 relations): `qtsl_morse_readout`
//! ([`crate::morse`]), `qtsl_miranda_battery` ([`crate::miranda`]),
//! `qtsl_stochwire_shape` ([`crate::stochwire`]), and `qtsl_bag_canon`
//! ([`crate::bagcanon`]) — certificate-kit recomputation over data
//! rows, each the sole authority its certificate's claims are read
//! against (recompute, don't trust).
//!
//! **The mask family** (6 relations): `simplexSameMembers`,
//! `simplexIsFaceMinus`, `simplexIsIntersection`, `extensionSetOmits`,
//! `extensionSetSameMembers`, and `isExtensionSetEmpty` — bounded
//! sweeps over the sealed finite membership data of
//! Simplex/ExtensionSet rows ([`crate::blmask`]).
//!
//! **The system-spec family** (4 relations):
//! `qtsl_poly_canonical` ([`crate::polycanon`]) — the Poly
//! canonical-form receipt — the composite well-posedness
//! pair `qtsl_sys_causal`/`qtsl_sys_w3` ([`crate::syswire`]):
//! instantaneous-dependency causality (with directed-only stochastic
//! composition, v1) and W3 simultaneity resolution — and
//! `qtsl_flatten`, the QFlatEq discharge's v1 fiber (the reflexive
//! SysMech face decided; the composite fiber a loud deferral until
//! its SwitchEdge/product row vocabulary stages).
//!
//! **The ProbLog family** (8 relations, [`crate::problog`]): the
//! certified-bracket obligation species over ground definite programs
//! — `qtsl_problog_wf`, `qtsl_problog_derives`, `qtsl_problog_blocks`
//! (saturation runs), `qtsl_problog_exact` (world enumeration),
//! `qtsl_problog_lower`/`qtsl_problog_upper` (event-algebra bracket
//! arithmetic, exact ℚ), `qtsl_problog_bonferroni` (the even-depth
//! inclusion–exclusion prefix — sound lower bounds past the full-IE
//! cap), and `qtsl_problog_compiled` (exact beyond enumeration: a
//! leaf-covered decision term verified by the memoized requirement-set
//! calculus — claimed only when the swept revisions declare the
//! decision-term vocabulary).
//!
//! **The conclusion-form family** (6 relations,
//! [`crate::blconclform`] over the [`crate::barycoord`] substrate):
//! `barycentricHalfspaceForm` — the region-atom rules' barycentric
//! halfspace conjunction, recomputed from the simplex's vertex table
//! and compared structurally against the formula's rows — the
//! four cell-schema forms (`cellStrictInteriorForm`, `cellOneHotForm`,
//! `cellOutWitnessForm`, `cellOutZeroForm`): the cell rules'
//! conclusion syntax, destructuring the cell application's port rows
//! behind one shared arity/range gate — and `lirpaConclusionForm`,
//! the LiRPA relaxation rule's conclusion shape (no geometry).
//!
//! **The NN conclusion-form oracle family** (9 relations,
//! [`crate::nnform`]): the ReLU/LiRPA premise- and
//! conclusion-shape relations (`reluPremNonnegForm` …
//! `lirpaSandwichForm`) — the cell-form pattern over the cited PReLU
//! application's position-0 ports, shapes pinned by the Lean
//! catalogue's rule-data types.
//!
//! **The semiring-cell family** (2 relations,
//! [`crate::contract`]): `qtsl_contract_param` (conjugation-parameter
//! conformance, exactly as `qtsl_hplate_param_wire`) and
//! `qtsl_contract_cell` v1 (hagSum decides TRUE; conjugated kinds
//! loud-defer; idempotent kinds decide FALSE) over the
//! `contract_semiring` cell rows.
//!
//! **The carillon discharge-plan family** (4 relations,
//! [`crate::carillon`]): the R2–R5 grid/region/manifest recomputes
//! ported from the carillon producer's executable references —
//! `qtsl_cell_cover` (named grid cells cover a region box, fail-closed
//! on holes), `qtsl_dbar_closure` (the one-jump closed-domain hull),
//! `qtsl_gap_a` (reset images land in their destination domains, 1-D
//! as specced), and `qtsl_lowbound_boxes` (an exact box cover of
//! region ∩ dbar).
//! **The surgery family** (4 relations, [`crate::blsurgery`]): the
//! proof-theory context machinery — `conjunctAt`/`conjReplace` (∧-tree
//! path reads and writes over `CtxPath` rows, the Lean
//! `conjGet?`/`conjReplace?`) and the substitution pair
//! `substituteInFormula`/`applyPredicateToTerm` (`Formula.subst` at a
//! genuine wire / at the predicate hole), each decided by parallel
//! structural descent of input and claimed output.
//!
//! **The promise interface-confinement family** (2 relations,
//! [`crate::blpromise`]): the `PPromise` wire obligations —
//! `promiseContractConfined` (every free wire of the contract is among
//! the node's declared interface wires) and `promiseWiresSeparated`
//! (every supplier-premise wire shared with the RECOMPUTED context —
//! the consumer's premise with the contract slot blanked to `FTrue` —
//! or with the node's conclusion is among the interface wires).
//!
//! **The Bernstein-cone family** (3 relations, [`crate::berncone`]):
//! the region calculus's heavy recomputes —
//! `allForwardDiffBernCoeffsSatisfyP` (the exact-rational Bernstein
//! forward-difference coefficient sweep, recomputed from the simplex's
//! vertex table: BernCone nodes carry no coefficient data),
//! `coverInfeasibilityValid` (the subdivision rule's 1-D interval
//! cover, recomputed from the branch regions; the carried cover
//! certificate is not consulted), and
//! `allForwardDiffBernIntvEnclosuresSatisfyP` (the float lane: the
//! same grid in validated dtype-interval arithmetic, P at the lower
//! endpoints — [`crate::fpintv`] carries the Lean-pinned rounding).
//!
//! **The transition/bag well-formedness family** (5 relations,
//! [`crate::trwf`]): the Transition former's admission
//! side-conditions and the bag former's counting demands —
//! `qtsl_tr_content` (exactly one content presentation, the
//! exactly-one grain/clock attributes, and the mirrored clock-floor
//! rows), `qtsl_tr_grain`/`qtsl_tr_endo` (the marked-population
//! fragment: grain wire lists and next payloads against the marking
//! block), `qtsl_massone` (branch weights total exactly one, exact
//! ℚ), and `qtsl_bag_wf` (base/capacity/marking/loop counting per
//! bag mechanism).
//!
//! **The deadline-table family** (1 relation, [`crate::deadline`]):
//! `qtsl_deadline_table` — the exact finite-horizon walk,
//! recomputing the certified-gym exact-lane checker's WF/B/S/C
//! obligations verbatim from the node's closure alone (Dtmc kernel +
//! policy mechanisms through `QSat/sys`, the reach spec formers
//! through `QSat/spec`, the flat `(T+1) × ns` table).
//!
//! No ground functions are claimed: every entry is a relation.
//! None declares order semantics (`RangeSupport::None`).
//!
//! # Evaluation surfaces, honestly split
//!
//! [`QtslGroundProvider::filter_rows`] is the full evaluation path:
//! argument cells plus a [`CertRows`] row context in, verdict out. It
//! is what the seam-facing `filter` will delegate to once the engine's
//! `RowView` exposes typed row content; until then the seam-facing
//! path REFUSES with a named reason rather than guessing (the
//! conservative rule: under an enforced axiom, a gate that cannot
//! evaluate must not admit). Binding is unaffected — entries verify
//! and bind now, and the refusal is an evaluation-time value, exactly
//! the safe-fail the seam's laws prescribe.

use crate::asel::{build_asel_vocab, eval_asel, AselVocab};
use crate::atomic::{elem_local, eval_atomic, SyntaxVocab};
use crate::avgbattery::{build_avgbattery_vocab, AvgBatteryVocab};
use crate::bagcanon::{build_bagcanon_vocab, eval_bag_canon, BagCanonVocab};
use crate::barycoord::{build_bary_vocab, BaryVocab};
use crate::berncone::{build_subdivide_vocab, eval_berncone, SubdivideVocab};
use crate::blapplic::{self as bl, BlVocab};
use crate::blconclform::{build_cellapp_vocab, eval_conclform, CellAppVocab};
use crate::bllattice::{
    build_lattice_vocab, eval_block_lattice_wf, eval_product_lattice_checks, LatticeVocab,
};
use crate::blmask::{build_mask_vocab, eval_mask, MaskVocab};
use crate::blpredclass::eval_predclass;
use crate::blpromise::{build_promise_vocab, eval_promise, PromiseVocab};
use crate::blsurgery::{build_surgery_vocab, eval_surgery, SurgeryVocab};
use crate::carillon::{build_carillon_vocab, eval_carillon, CarillonVocab};
use crate::circuit::{
    build_circuit_vocab, build_gatescalar_vocab, CircuitVocab, DecodeCache, GateScalarVocab,
    StoreCtx,
};
use crate::contract::{build_contract_vocab, eval_contract, ContractVocab};
use crate::dabs::{build_dabs_vocab, eval_dabs, DabsVocab};
use crate::deadline::{build_deadline_vocab, eval_deadline_table, DeadlineVocab};
use crate::dgc::{build_dgc_vocab, eval_dgc, DgcVocab};
use crate::dwellgate::{build_dwellgate_vocab, DwellGateVocab};
use crate::enclosure::{build_enclosure_vocab, eval_enclosure_witness_valid, EncVocab};
use crate::error::EvalError;
use crate::fpintv::{build_dtype_vocab, DtypeVocab};
use crate::guard::{build_guard_vocab, eval_guard, GuardVocab};
use crate::gymeproc::{build_gymeproc_vocab, eval_gymeproc, GymEprocVocab};
use crate::gymrw::{build_gymrw_vocab, eval_gymrw, GymRwVocab};
use crate::hole::{build_hole_vocab, eval_hole_count, HoleVocab};
use crate::hplate::{build_hplate_vocab, eval_hplate, HPlateVocab};
use crate::markflow::{build_markflow_vocab, MarkflowVocab};
use crate::miranda::{build_miranda_vocab, eval_miranda, MirandaVocab};
use crate::morse::{build_morse_vocab, eval_morse, MorseVocab};
use crate::nnform::{build_nnform_vocab, eval_nnform, NnFormVocab};
use crate::polycanon::{build_polycanon_vocab, eval_poly_canonical, PolyCanonVocab};
use crate::problog::{build_problog_vocab, eval_problog, ProblogVocab};
use crate::ratecap::{build_ratecap_vocab, RatecapVocab};
use crate::roster::{BlKind, CircuitKind, EntryRow, RelKind, TrWfKind};
use crate::rowctx::CertRows;
use crate::spdemoment::{build_spdemoment_vocab, eval_spdemoment, SpdeMomentVocab};
use crate::stochwire::{build_stochwire_vocab, eval_stochwire, StochWireVocab};
use crate::store::StoreResolver;
use crate::swret::{build_swret_vocab, eval_swret, SwretVocab};
use crate::syswire::{
    build_syswire_vocab, eval_flatten, eval_sys_causal, eval_sys_w3, SysWireVocab,
};
use crate::theory::{Chid, TheoryIndex};
use crate::trwf::{build_trwf_vocab, eval_trwf, TrWfVocab};
use crate::wirecausality::{build_wirecausality_vocab, WireCausalityVocab};
use geolog_envelope::cbor_prim::Cursor;
use geolog_envelope::{LiteralView, Value};
use geolog_ground_api::{
    Bind, EvalCtx, FnExpectation, GroundEval, GroundProvider, LocalId, ProviderInfo, RangeSupport,
    RelExpectation, Scope, Verdict,
};
use std::cmp::Ordering;
use std::sync::{Arc, Mutex};

// ---------------------------------------------------------------- vocab

/// The applicability + atomic-compare families' resolved vocabulary
/// (they share the Term/Formula anchor sorts).
#[derive(Debug, Clone)]
pub struct BlFamilyVocab {
    pub term_sort: Chid,
    pub formula_sort: Chid,
    pub bl: BlVocab,
    pub syntax: SyntaxVocab,
}

/// The provider's resolved vocabulary: every pinned constructor and
/// field identity the evaluators dispatch on, resolved by name ONCE at
/// construction from declared-vocabulary data and verified against the
/// declared shapes (ambiguity and shape mismatch are loud errors, so a
/// misresolved vocabulary can never bind).
///
/// Resolution is PER FAMILY GROUP, and a group that does not resolve
/// against the loaded revisions is `None` with its reason recorded in
/// [`QtslVocab::notes`] — the provider then simply does not claim that
/// group's relations, so the binder defers them (declared-but-unbound,
/// safe-fail) instead of anything ever guessing.
#[derive(Debug, Clone)]
pub struct QtslVocab {
    pub bl: Option<BlFamilyVocab>,
    pub morse: Option<MorseVocab>,
    pub miranda: Option<MirandaVocab>,
    pub stochwire: Option<StochWireVocab>,
    pub bagcanon: Option<BagCanonVocab>,
    pub mask: Option<MaskVocab>,
    pub polycanon: Option<PolyCanonVocab>,
    pub syswire: Option<SysWireVocab>,
    pub hole: Option<HoleVocab>,
    pub problog: Option<ProblogVocab>,
    /// The barycentric-geometry vocabulary (the conclusion-form
    /// family also needs `bl` for its Formula/Term walks).
    pub barycoord: Option<BaryVocab>,
    /// The cell-application vocabulary (hypernet ports + the
    /// certificate extension's cell-list rows) — the cell-schema
    /// conclusion forms need it on top of `bl` and `barycoord`.
    pub cellapp: Option<CellAppVocab>,
    /// The block-lattice family (`blockLatticeWF` /
    /// `productLatticeChecks`); its evaluators also need [`Self::bl`]
    /// (the Formula/Term walk substrate), so its entries are claimed
    /// only when both groups resolve.
    pub lattice: Option<LatticeVocab>,
    /// The enclosure family (`enclosureWitnessValid`): plain field
    /// reads on the judgment element — no Formula/Term walk substrate
    /// needed, so the claim gates on this group alone.
    pub enclosure: Option<EncVocab>,
    /// The carillon discharge-plan family (the R2–R5 recomputes):
    /// manifest, grid-complex, and box-list rows — its own group, no
    /// Formula/Term substrate needed.
    pub carillon: Option<CarillonVocab>,
    /// The Formula/Term surgery family (`conjunctAt`, `conjReplace`,
    /// `substituteInFormula`, `applyPredicateToTerm`): the `CtxPath`
    /// constructors; the walks ride [`Self::bl`], so its entries are
    /// claimed only when both groups resolve.
    pub surgery: Option<SurgeryVocab>,
    /// The promise interface-confinement family
    /// (`promiseContractConfined`, `promiseWiresSeparated`): the
    /// `PPromise` field identities; the formula walks ride
    /// [`Self::bl`] and the path decode rides [`Self::surgery`], so
    /// its entries are claimed only when all three groups resolve.
    pub promise: Option<PromiseVocab>,
    /// The subdivision-node vocabulary (`PSubdivide` branch families)
    /// — the cover relation needs it on top of [`Self::barycoord`];
    /// the coefficient sweep rides [`Self::bl`] + [`Self::barycoord`]
    /// alone.
    pub subdivide: Option<SubdivideVocab>,
    /// The Dtype-theory vocabulary (axis fields, `mkDtype`, and the
    /// kind/sign/ext/alias constants) — the Bernstein-cone float lane
    /// (`allForwardDiffBernIntvEnclosuresSatisfyP`) needs it on top of
    /// [`Self::bl`] + [`Self::barycoord`].
    pub dtype: Option<DtypeVocab>,
    /// The deadline-table vocabulary (`qtsl_deadline_table` — the
    /// deadline-table walk): QtslCert node/judgment/table rows, the Qtsl
    /// spec formers + System constructors, and the Dtmc frame +
    /// bridge (kernel, init, policy). Its own group, no shared
    /// substrate needed.
    pub deadline: Option<DeadlineVocab>,
    /// The SPDE moment-core family ([`crate::spdemoment`]): plain
    /// field/constructor reads on its own sorts — no Formula/Term
    /// walk substrate needed, so its claims gate on this group alone.
    pub spdemoment: Option<SpdeMomentVocab>,
    /// The gym reward-table family ([`crate::gymrw`]): plain field
    /// reads on its own certificate sort — no shared substrate
    /// needed, so its claim gates on this group alone.
    pub gymrw: Option<GymRwVocab>,
    /// The gymnasium e-process family ([`crate::gymeproc`]): plain
    /// name-selected field/constructor identities over the declared
    /// indices.
    pub gymeproc: Option<GymEprocVocab>,
    /// The transition/bag well-formedness family ([`crate::trwf`]):
    /// the Transition former's content/grain/clock vocabulary and the
    /// bag former's relations — its own group, no shared substrate
    /// needed.
    pub trwf: Option<TrWfVocab>,
    /// The HPlate certificate-stratum + tie-walk family
    /// ([`crate::hplate`]): resolves ONLY against closures carrying
    /// the event-4 passenger names (`hplate_token`,
    /// `QPAlwaysFromFold`, `qpaf_upper`/`qpaf_lower`) — the family
    /// lands with the fragment, per the judgment-tie design.
    pub hplate: Option<HPlateVocab>,
    /// The guarded-specification / satisfaction-claim family
    /// ([`crate::guard`]): the event-4 spec-record vocabulary
    /// (spec_forall + StatePred/StateObservable/oPoly, the guard slot,
    /// the warrant routes) — its own group, no shared substrate needed.
    pub guard: Option<GuardVocab>,
    /// The angelic-selection family ([`crate::asel`]): the
    /// ASelWitness/ASelCell vocabulary, the TrClock three wings, and
    /// (optionally, for `attach`) the compiled verdict form — its own
    /// group, no shared substrate needed.
    pub asel: Option<AselVocab>,
    /// The drift-moment tie family ([`crate::swret`]): resolves ONLY
    /// against closures carrying the event-5 passenger names
    /// (`QIntBoundFromSW` + its fields + `qtsl_intbound_sw`) — the
    /// family lands with the mint, per the SPDE rung design.
    pub swret: Option<SwretVocab>,
    /// The kernel-citation circuit family ([`crate::circuit`]):
    /// `qtsl_kcite_wf` plus the grain/endo circuit arms — the
    /// KernelCite block's vocabulary (mkKernelCite/hnDigest, the Box
    /// kit, the grain/content rows, the init-box witness).
    pub circuit: Option<CircuitVocab>,
    /// The gate-scalar family ([`crate::circuit`]):
    /// `qtsl_gate_scalar` — gates on `hnDigest`/`HypernetRef` alone,
    /// independent of the KernelCite block.
    pub gatescalar: Option<GateScalarVocab>,
    /// The NN conclusion-form family ([`crate::nnform`]):
    /// hypernet port fields + `PrimApp/prim` + `PReLU` —
    /// deliberately smaller than the cell-application group (no
    /// `SimpC/nCells`), so it resolves on the baked closures where
    /// `cellapp` does not.
    pub nnform: Option<NnFormVocab>,
    /// The primitive-box semiring-cell family ([`crate::contract`]):
    /// `contract_semiring` + the five `HAggKind`
    /// constructors.
    pub contract: Option<ContractVocab>,
    /// The MarkFlow walk family ([`crate::markflow`]):
    /// `qtsl_wire_markflow` over the QWireComposeMarks node —
    /// event-5 passenger vocabulary (node sort + carve/diagonal
    /// spines); the family resolves only against closures carrying
    /// the marks-node block. No store dependency.
    pub markflow: Option<MarkflowVocab>,
    /// The dwell-gate family ([`crate::dwellgate`]):
    /// `qtsl_dwell_gate` — the carved-window wing's gate-inside-
    /// window walk (event-5 passenger vocabulary: `tkCarved` +
    /// `tr_dwell_gate`; the family resolves only against closures
    /// carrying the carved wing). Store-seam: the gate is cited by
    /// digest.
    pub dwellgate: Option<DwellGateVocab>,
    /// The rate-cap family ([`crate::ratecap`]):
    /// `qtsl_tr_ratecap` — rate ≤ majorant on the active region for
    /// scale-view race transitions. No store dependency.
    pub ratecap: Option<RatecapVocab>,
    /// The causality walk family ([`crate::wirecausality`]):
    /// `qtsl_wire_causality` over the QWireCompose node —
    /// the composition vocabulary (node attributes + the
    /// QNatList rank spine + the wiring machinery); resolves on any
    /// closure carrying the composition block. No store dependency.
    pub wirecausality: Option<WireCausalityVocab>,
    /// The LRA-battery walk family ([`crate::avgbattery`]):
    /// `qtsl_avg_battery` over the QAvgBattery node — the baked e6
    /// battery schema (node attributes at the `lowbounds` spelling +
    /// the SReturn/poAvg/oInd formers + the spec record), so the
    /// family resolves on both baked closures; the claim RELATION
    /// awaits the rules-as-rows fan's mint (the module doc's
    /// claim-status note). HOLDS unreachable at v0 (loud deferral).
    /// No store dependency.
    pub avgbattery: Option<AvgBatteryVocab>,
    /// The DtmcAbsorb family ([`crate::dabs`]): the absorption-query
    /// species' declarations over the chain species' stored grain —
    /// staged-fragment vocabulary (`DAbsQuery` is not in any baked
    /// closure), so the family resolves only against closures that
    /// carry the fragment. Its own group, no shared substrate needed.
    pub dabs: Option<DabsVocab>,
    /// The DtmcContraction family ([`crate::dgc`]): the strengthened
    /// generator-form witness species over the same stored grain —
    /// resolves only against closures carrying `DGenContraction`
    /// (the event-8 dcc closure and its staged pre-mint chains). Its
    /// own group, no shared substrate needed.
    pub dgc: Option<DgcVocab>,
    /// One line per unresolved family group: which group, and why.
    pub notes: Vec<String>,
}

/// Resolve a sort by name across the swept indices, refusing
/// cross-revision ambiguity — never picking through it. `Ok(None)` =
/// genuinely absent (the caller decides whether absence is an error —
/// optional vocabulary groups treat it as "not declared").
fn find_sort_opt(indices: &[&TheoryIndex], name: &str) -> Result<Option<Chid>, String> {
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
    Ok(found)
}

/// [`find_sort_opt`] with absence as an error — the required-sort form.
fn find_sort(indices: &[&TheoryIndex], name: &str) -> Result<Chid, String> {
    find_sort_opt(indices, name)?
        .ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
}

impl QtslVocab {
    /// Resolve every family group the loaded revisions support. Anchor
    /// sorts are found by name; each group's own builder verifies the
    /// declared shapes behind those anchors.
    pub fn build(indices: &[&TheoryIndex]) -> QtslVocab {
        let mut notes = Vec::new();
        let mut note = |family: &str, why: String| {
            notes.push(format!("{family}: not claimed — {why}"));
        };

        let bl = (|| -> Result<BlFamilyVocab, String> {
            let term_sort = find_sort(indices, "Term")?;
            let formula_sort = find_sort(indices, "Formula")?;
            Ok(BlFamilyVocab {
                term_sort,
                formula_sort,
                bl: BlVocab::build(indices, term_sort, formula_sort)?,
                syntax: SyntaxVocab::build(indices, term_sort, formula_sort)?,
            })
        })()
        .map_err(|e| note("applicability/atomic families", e))
        .ok();

        let morse = (|| -> Result<MorseVocab, String> {
            build_morse_vocab(
                indices,
                find_sort(indices, "QDag")?,
                find_sort(indices, "QCellMap")?,
                find_sort(indices, "QBlockLattice")?,
                find_sort(indices, "QVertexRegionList")?,
            )
        })()
        .map_err(|e| note("morse-readout family", e))
        .ok();

        let miranda = (|| -> Result<MirandaVocab, String> {
            build_miranda_vocab(
                indices,
                find_sort(indices, "QMirandaBattery")?,
                find_sort(indices, "QRegionAtom")?,
                find_sort(indices, "PolyVec")?,
            )
        })()
        .map_err(|e| note("miranda-battery family", e))
        .ok();

        let stochwire = (|| -> Result<StochWireVocab, String> {
            build_stochwire_vocab(indices, find_sort(indices, "QStochContribList")?)
        })()
        .map_err(|e| note("stochastic-wire family", e))
        .ok();

        let bagcanon = (|| -> Result<BagCanonVocab, String> {
            build_bagcanon_vocab(indices, find_sort(indices, "QBagVal")?)
        })()
        .map_err(|e| note("bag-canonicality family", e))
        .ok();

        let mask = (|| -> Result<MaskVocab, String> {
            build_mask_vocab(
                indices,
                find_sort(indices, "Simplex")?,
                find_sort(indices, "ExtensionSet")?,
                find_sort(indices, "SimpC")?,
            )
        })()
        .map_err(|e| note("mask family", e))
        .ok();

        let polycanon = (|| -> Result<PolyCanonVocab, String> {
            build_polycanon_vocab(indices, find_sort(indices, "Poly")?)
        })()
        .map_err(|e| note("poly-canonicality family", e))
        .ok();

        let syswire = (|| -> Result<SysWireVocab, String> {
            build_syswire_vocab(indices, find_sort(indices, "System")?)
        })()
        .map_err(|e| note("system-spec family", e))
        .ok();

        let hole = build_hole_vocab(indices)
            .map_err(|e| note("hole family", e))
            .ok();

        let problog = (|| -> Result<ProblogVocab, String> {
            // The compiled decision-term sorts are OPTIONAL as a pair
            // (revisions predating the compiled judgment keep the rest
            // of the family); exactly one present is half a vocabulary
            // — malformed, a hard error like any other shape mismatch.
            let tree_sorts = match (
                find_sort_opt(indices, "QPlogDecTree")?,
                find_sort_opt(indices, "QPlogArmList")?,
            ) {
                (Some(d), Some(a)) => Some((d, a)),
                (None, None) => None,
                _ => {
                    return Err("exactly one of QPlogDecTree/QPlogArmList is declared — \
                         half a compiled decision-term vocabulary"
                        .into())
                }
            };
            build_problog_vocab(
                indices,
                find_sort(indices, "QPlogProg")?,
                find_sort(indices, "QPlogSetList")?,
                tree_sorts,
            )
        })()
        .map_err(|e| note("problog family", e))
        .ok();

        let barycoord = (|| -> Result<BaryVocab, String> {
            build_bary_vocab(
                indices,
                find_sort(indices, "Simplex")?,
                find_sort(indices, "ExtensionSet")?,
                find_sort(indices, "SimpC")?,
            )
        })()
        .map_err(|e| note("conclusion-form family (barycentric vocabulary)", e))
        .ok();

        let cellapp = (|| -> Result<CellAppVocab, String> {
            build_cellapp_vocab(
                indices,
                find_sort(indices, "InputPort")?,
                find_sort(indices, "OutputPort")?,
                find_sort(indices, "PrimApp")?,
                find_sort(indices, "Wire")?,
                find_sort(indices, "SimpC")?,
            )
        })()
        .map_err(|e| {
            note(
                "cell-schema conclusion forms (cell-application vocabulary)",
                e,
            )
        })
        .ok();

        let lattice = build_lattice_vocab(indices)
            .map_err(|e| note("block-lattice family", e))
            .ok();

        let enclosure = build_enclosure_vocab(indices)
            .map_err(|e| note("enclosure family", e))
            .ok();

        let carillon = (|| -> Result<CarillonVocab, String> {
            build_carillon_vocab(
                indices,
                find_sort(indices, "QGridCx")?,
                find_sort(indices, "QBoxList")?,
                find_sort(indices, "QRegionAtom")?,
            )
        })()
        .map_err(|e| note("carillon discharge-plan family", e))
        .ok();
        let surgery = build_surgery_vocab(indices)
            .map_err(|e| note("surgery family (CtxPath vocabulary)", e))
            .ok();
        let promise = build_promise_vocab(indices)
            .map_err(|e| note("promise interface-confinement family", e))
            .ok();
        let subdivide = (|| -> Result<SubdivideVocab, String> {
            build_subdivide_vocab(
                indices,
                find_sort(indices, "PSubdivide")?,
                find_sort(indices, "Simplex")?,
                find_sort(indices, "ExtensionSet")?,
            )
        })()
        .map_err(|e| note("Bernstein-cone family (subdivision vocabulary)", e))
        .ok();

        let dtype = (|| -> Result<DtypeVocab, String> {
            build_dtype_vocab(
                indices,
                find_sort(indices, "Dtype")?,
                find_sort(indices, "Kind")?,
                find_sort(indices, "Sign")?,
                find_sort(indices, "Ext")?,
            )
        })()
        .map_err(|e| note("Bernstein-cone float lane (Dtype vocabulary)", e))
        .ok();

        let deadline = (|| -> Result<DeadlineVocab, String> {
            build_deadline_vocab(indices, find_sort(indices, "QDeadlineTable")?)
        })()
        .map_err(|e| note("deadline-table family", e))
        .ok();

        let spdemoment = build_spdemoment_vocab(indices)
            .map_err(|e| note("SPDE moment-core family", e))
            .ok();

        let gymrw = build_gymrw_vocab(indices)
            .map_err(|e| note("gym reward-table family", e))
            .ok();
        let gymeproc = build_gymeproc_vocab(indices)
            .map_err(|e| note("gymnasium e-process family", e))
            .ok();

        let trwf = (|| -> Result<TrWfVocab, String> {
            build_trwf_vocab(
                indices,
                find_sort(indices, "Transition")?,
                find_sort(indices, "ScaleView")?,
                find_sort(indices, "Mech")?,
                find_sort(indices, "System")?,
                find_sort(indices, "Poly")?,
            )
        })()
        .map_err(|e| note("transition/bag well-formedness family", e))
        .ok();

        let hplate = (|| -> Result<HPlateVocab, String> {
            build_hplate_vocab(
                indices,
                find_sort(indices, "HCert")?,
                find_sort(indices, "HPlate")?,
                find_sort(indices, "HFeature")?,
                find_sort(indices, "HFootprintRow")?,
                find_sort(indices, "QPAlwaysFromFold")?,
                find_sort(indices, "QFireBoundFromFold")?,
                find_sort(indices, "System")?,
                find_sort(indices, "Mech")?,
                find_sort(indices, "Transition")?,
                find_sort(indices, "ScaleView")?,
                find_sort(indices, "Poly")?,
                find_sort(indices, "HAggWire")?,
            )
        })()
        .map_err(|e| {
            note(
                "HPlate certificate-stratum family (event-4 passenger vocabulary)",
                e,
            )
        })
        .ok();

        let guard = build_guard_vocab(indices)
            .map_err(|e| note("guarded-specification family", e))
            .ok();

        let asel = build_asel_vocab(indices)
            .map_err(|e| note("angelic-selection family", e))
            .ok();

        let swret = build_swret_vocab(indices)
            .map_err(|e| note("drift-moment tie family (event-5 passenger vocabulary)", e))
            .ok();

        let circuit = build_circuit_vocab(indices)
            .map_err(|e| note("kernel-citation circuit family", e))
            .ok();

        let gatescalar = build_gatescalar_vocab(indices)
            .map_err(|e| note("gate-scalar family", e))
            .ok();

        let nnform = (|| -> Result<NnFormVocab, String> {
            build_nnform_vocab(
                indices,
                find_sort(indices, "InputPort")?,
                find_sort(indices, "OutputPort")?,
                find_sort(indices, "PrimApp")?,
                find_sort(indices, "Wire")?,
                find_sort(indices, "Primitive")?,
            )
        })()
        .map_err(|e| note("NN conclusion-form family (ReLU-application vocabulary)", e))
        .ok();

        let contract = (|| -> Result<ContractVocab, String> {
            build_contract_vocab(
                indices,
                find_sort(indices, "PrimApp")?,
                find_sort(indices, "HAggKind")?,
            )
        })()
        .map_err(|e| note("semiring-cell family (contract vocabulary)", e))
        .ok();
        let markflow = build_markflow_vocab(indices)
            .map_err(|e| note("markflow family (event-5 marks-node vocabulary)", e))
            .ok();
        let wirecausality = build_wirecausality_vocab(indices)
            .map_err(|e| note("causality walk family (composition-node vocabulary)", e))
            .ok();

        let dwellgate = build_dwellgate_vocab(indices)
            .map_err(|e| note("dwell-gate family (event-5 carved-window vocabulary)", e))
            .ok();

        let ratecap = build_ratecap_vocab(indices)
            .map_err(|e| note("rate-cap family (scale-view race vocabulary)", e))
            .ok();

        let avgbattery = build_avgbattery_vocab(indices)
            .map_err(|e| note("LRA-battery family (QAvgBattery e6 vocabulary)", e))
            .ok();

        let dabs = (|| -> Result<DabsVocab, String> {
            build_dabs_vocab(indices, find_sort(indices, "DAbsQuery")?)
        })()
        .map_err(|e| note("DtmcAbsorb family (staged-fragment vocabulary)", e))
        .ok();

        let dgc = (|| -> Result<DgcVocab, String> {
            build_dgc_vocab(indices, find_sort(indices, "DGenContraction")?)
        })()
        .map_err(|e| note("DtmcContraction family (dcc-closure vocabulary)", e))
        .ok();

        QtslVocab {
            bl,
            morse,
            miranda,
            stochwire,
            bagcanon,
            mask,
            polycanon,
            syswire,
            hole,
            problog,
            barycoord,
            cellapp,
            lattice,
            enclosure,
            carillon,
            surgery,
            promise,
            subdivide,
            dtype,
            deadline,
            spdemoment,
            gymrw,
            gymeproc,
            trwf,
            hplate,
            guard,
            asel,
            swret,
            circuit,
            gatescalar,
            nnform,
            contract,
            markflow,
            dwellgate,
            ratecap,
            wirecausality,
            avgbattery,
            dabs,
            dgc,
            notes,
        }
    }
}

// ------------------------------------------------------------- entries

/// The full claimed roster: the per-family entry tables (each a
/// `const ENTRIES` beside its family's evaluators — see
/// [`crate::roster`]), concatenated in this fixed family order.
///
/// Registration order is part of the seam surface: provider-local
/// indices are roster positions among the claimed entries
/// ([`LocalId`]), and the conformance fixtures mint declarations by
/// position. Append within a family table; keep the family order
/// stable.
const FAMILY_ENTRIES: &[&[EntryRow]] = &[
    crate::blapplic::ENTRIES,
    crate::atomic::ENTRIES,
    crate::morse::ENTRIES,
    crate::miranda::ENTRIES,
    crate::stochwire::ENTRIES,
    crate::bagcanon::ENTRIES,
    crate::blmask::ENTRIES,
    crate::polycanon::ENTRIES,
    crate::syswire::ENTRIES,
    crate::problog::ENTRIES,
    crate::blconclform::ENTRIES,
    crate::bllattice::ENTRIES,
    crate::enclosure::ENTRIES,
    crate::carillon::ENTRIES,
    crate::blsurgery::ENTRIES,
    crate::blpromise::ENTRIES,
    crate::blpredclass::ENTRIES,
    crate::berncone::ENTRIES,
    crate::deadline::ENTRIES,
    crate::spdemoment::ENTRIES,
    crate::gymrw::ENTRIES,
    crate::gymeproc::ENTRIES,
    crate::trwf::ENTRIES,
    crate::hplate::ENTRIES,
    crate::hole::ENTRIES,
    crate::guard::ENTRIES,
    crate::asel::ENTRIES,
    crate::swret::ENTRIES,
    // Appended at the END (existing roster positions are
    // provider-local indices — unchanged by construction).
    crate::circuit::ENTRIES,
    // Appended at the END (same reasoning): the NN
    // conclusion-form oracle family and the semiring-cell family.
    crate::nnform::ENTRIES,
    crate::contract::ENTRIES,
    // Appended at the END (same discipline).
    crate::markflow::ENTRIES,
    // Appended at the END (same discipline).
    crate::dwellgate::ENTRIES,
    crate::ratecap::ENTRIES,
    // Appended at the END (same discipline): the
    // causality walk — the ∀-face sibling of the markflow family.
    crate::wirecausality::ENTRIES,
    // Appended at the END (same discipline): the LRA-battery
    // walk — structural stratum decided, leaf-sequent stratum loudly
    // deferred (HOLDS unreachable at v0); its claim relation awaits
    // the rules-as-rows fan's mint, so no baked closure binds it yet.
    crate::avgbattery::ENTRIES,
    // Appended at the END (same discipline): the DtmcAbsorb
    // absorption-bracket family — staged-fragment vocabulary, so no
    // baked closure binds it yet.
    crate::dabs::ENTRIES,
    // Appended at the END (same discipline): the DtmcContraction
    // generator-form strengthening — the event-8 dcc closure's
    // family.
    crate::dgc::ENTRIES,
];

/// The full claimed roster size (every entry, all family groups).
pub const ENTRY_COUNT: usize = {
    let mut n = 0;
    let mut i = 0;
    while i < FAMILY_ENTRIES.len() {
        n += FAMILY_ENTRIES[i].len();
        i += 1;
    }
    n
};

// ------------------------------------------------------------- provider

/// The QTSL ground provider: one value carrying the application's
/// entire evaluation capability at the seam. Construct with the
/// semantics revisions the deployment's committed evaluation-semantics
/// rows carry (the binder cross-checks them; an entry whose committed
/// revision is not listed DEFERS — dispatch under unmet semantics
/// never happens) and the resolved vocabulary.
pub struct QtslGroundProvider {
    semantics_revs: Vec<[u8; 32]>,
    vocab: QtslVocab,
    rels: Vec<RelExpectation>,
    /// Parallel to `rels`: the claimed entries' rows in
    /// [`FAMILY_ENTRIES`].
    claimed: Vec<&'static EntryRow>,
    /// The content-addressed store behind the store-seam families
    /// (design point F-3). `None` = storeless: claims stay
    /// vocabulary-gated exactly as always, and each store-needing
    /// instance refuses loudly with the case named ("cited content
    /// unreachable — no store attached") — loud beats silent.
    store: Option<Arc<dyn StoreResolver>>,
    /// The named-violations register (design memo F-4): the
    /// store-seam evaluators push `"<relation>: <why>"` at every
    /// decided-false; [`QtslGroundProvider::take_violations`] drains
    /// it. Engine-side chase dispatch simply never drains it — no
    /// engine surface changes. The register also
    /// carries HOLDS-side vacuity notes (`qtsl_tr_ratecap`'s
    /// all-stay face) — a vacuous discharge is never silent.
    violations: Mutex<Vec<String>>,
    /// Per-digest decode cache (one container cites one hypernet from
    /// several claim rows — the atari measurement).
    decode_cache: DecodeCache,
}

impl QtslGroundProvider {
    /// Claims are gated on resolved vocabulary: an entry whose family
    /// group did not resolve is simply NOT claimed — the binder then
    /// defers it (no claimant, safe-fail), and
    /// [`QtslVocab::notes`] carries the reason. A claim without its
    /// evaluator's vocabulary is unconstructible here by design.
    pub fn new(semantics_revs: Vec<[u8; 32]>, vocab: QtslVocab) -> QtslGroundProvider {
        QtslGroundProvider::build(semantics_revs, vocab, None)
    }

    /// [`QtslGroundProvider::new`] with a content-addressed store
    /// attached for the store-seam families (design memo F-3). Claims
    /// are IDENTICAL to the storeless construction — the store gates
    /// per-instance evaluation, never the roster.
    pub fn with_store(
        semantics_revs: Vec<[u8; 32]>,
        vocab: QtslVocab,
        store: Arc<dyn StoreResolver>,
    ) -> QtslGroundProvider {
        QtslGroundProvider::build(semantics_revs, vocab, Some(store))
    }

    fn build(
        semantics_revs: Vec<[u8; 32]>,
        vocab: QtslVocab,
        store: Option<Arc<dyn StoreResolver>>,
    ) -> QtslGroundProvider {
        let mut rels = Vec::new();
        let mut claimed = Vec::new();
        for entry in FAMILY_ENTRIES.iter().flat_map(|family| family.iter()) {
            let (name, fields, kind) = entry;
            let available = match kind {
                RelKind::Bl(_) | RelKind::Atomic { .. } => vocab.bl.is_some(),
                RelKind::Morse => vocab.morse.is_some(),
                RelKind::Miranda => vocab.miranda.is_some(),
                RelKind::StochWire => vocab.stochwire.is_some(),
                RelKind::BagCanon => vocab.bagcanon.is_some(),
                RelKind::Mask(_) => vocab.mask.is_some(),
                RelKind::PolyCanon => vocab.polycanon.is_some(),
                // The flatten v1 fiber reads only System constructors +
                // the mech_manifest relation — all inside the syswire
                // group.
                RelKind::Sys { .. } | RelKind::FlatEq => vocab.syswire.is_some(),
                RelKind::HoleCount => vocab.hole.is_some(),
                RelKind::Deadline => vocab.deadline.is_some(),
                // The compiled judgment additionally needs the
                // decision-term vocabulary — swept revisions lacking
                // those declarations simply cannot claim the relation
                // while the rest of the family is untouched.
                RelKind::Problog(k) => match k {
                    crate::roster::ProblogKind::Compiled => {
                        vocab.problog.as_ref().is_some_and(|v| v.has_compiled())
                    }
                    _ => vocab.problog.is_some(),
                },
                // The conclusion-form walks read Formula/Term rows
                // through the `bl` substrate; the geometry-reading
                // entries additionally need the barycentric
                // vocabulary, and the cell-schema forms the
                // cell-application vocabulary on top. The LiRPA form
                // reads no geometry: `bl` alone claims it.
                RelKind::ConclForm(k) => {
                    vocab.bl.is_some()
                        && match k {
                            crate::roster::ConclFormKind::Lirpa => true,
                            crate::roster::ConclFormKind::BarycentricHalfspace => {
                                vocab.barycoord.is_some()
                            }
                            _ => vocab.barycoord.is_some() && vocab.cellapp.is_some(),
                        }
                }
                // The lattice evaluators walk Formula/Term rows through
                // the shared substrate, so both groups must resolve.
                RelKind::Lattice { .. } => vocab.lattice.is_some() && vocab.bl.is_some(),
                RelKind::Enclosure => vocab.enclosure.is_some(),
                RelKind::Carillon(_) => vocab.carillon.is_some(),
                // The surgery walks read Formula/Term rows through the
                // `bl` substrate and decode CtxPath rows through their
                // own vocabulary — both must resolve for the claim.
                RelKind::Surgery(_) => vocab.surgery.is_some() && vocab.bl.is_some(),
                // The promise evaluators read node fields through
                // their own vocabulary, Formula/Judgment rows through
                // the `bl` substrate, and CtxPath rows through the
                // surgery vocabulary — all three must resolve.
                RelKind::Promise(_) => {
                    vocab.promise.is_some() && vocab.bl.is_some() && vocab.surgery.is_some()
                }
                // The predicate classifiers walk Formula/Term rows
                // through the shared `bl` substrate alone.
                RelKind::PredClass(_) => vocab.bl.is_some(),
                // The coefficient sweep walks Formula/Term rows through
                // the `bl` substrate and simplex geometry through the
                // barycentric vocabulary; the cover reads geometry plus
                // the subdivision node's branch families (no
                // Formula/Term walks).
                RelKind::BernCone(k) => {
                    vocab.barycoord.is_some()
                        && match k {
                            crate::roster::BernConeKind::Coeffs => vocab.bl.is_some(),
                            crate::roster::BernConeKind::Cover => vocab.subdivide.is_some(),
                            crate::roster::BernConeKind::IntvCoeffs => {
                                vocab.bl.is_some() && vocab.dtype.is_some()
                            }
                        }
                }
                RelKind::SpdeMoment(_) => vocab.spdemoment.is_some(),
                RelKind::GymRw => vocab.gymrw.is_some(),
                RelKind::GymEproc(_) => vocab.gymeproc.is_some(),
                RelKind::TrWf(_) => vocab.trwf.is_some(),
                RelKind::HPlate(_) => vocab.hplate.is_some(),
                RelKind::Guard(_) => vocab.guard.is_some(),
                RelKind::ASel(_) => vocab.asel.is_some(),
                RelKind::Swret => vocab.swret.is_some(),
                // Claims are VOCABULARY-gated, never store-gated: a
                // storeless provider still claims the store-seam
                // relations and refuses per-instance (loud beats
                // silent — the s5c F-2 lesson).
                RelKind::Circuit(k) => match k {
                    CircuitKind::KciteWf => vocab.circuit.is_some(),
                    CircuitKind::GateScalar => vocab.gatescalar.is_some(),
                },
                // The NN conclusion-form walks read Formula/Term rows
                // through the `bl` substrate and the ReLU application
                // through their own vocabulary — both must resolve.
                RelKind::NnForm(_) => vocab.bl.is_some() && vocab.nnform.is_some(),
                RelKind::Contract(_) => vocab.contract.is_some(),
                RelKind::Markflow => vocab.markflow.is_some(),
                // Claims stay vocabulary-gated (never store-gated),
                // exactly as the circuit family's.
                RelKind::DwellGate => vocab.dwellgate.is_some(),
                RelKind::TrRatecap => vocab.ratecap.is_some(),
                RelKind::WireCausality => vocab.wirecausality.is_some(),
                RelKind::AvgBattery => vocab.avgbattery.is_some(),
                RelKind::Dabs(_) => vocab.dabs.is_some(),
                RelKind::Dgc(_) => vocab.dgc.is_some(),
            };
            if !available {
                continue;
            }
            rels.push(RelExpectation {
                name,
                fields,
                scope: Scope::Snapshot,
                range: RangeSupport::None,
            });
            claimed.push(entry);
        }
        QtslGroundProvider {
            semantics_revs,
            vocab,
            rels,
            claimed,
            store,
            violations: Mutex::new(Vec::new()),
            decode_cache: DecodeCache::default(),
        }
    }

    /// The resolved vocabulary this provider evaluates against.
    pub fn vocab(&self) -> &QtslVocab {
        &self.vocab
    }

    /// Drain the named-violations register (design memo F-4): one
    /// `"<relation>: <why>"` line per decided-false the store-seam
    /// evaluators reached since the last drain. The in-loop claim
    /// walk (the mtk-produce check surface — a provider-native
    /// caller) drains it into its report beside the verdicts;
    /// engine-side chase dispatch never drains it, and that is fine —
    /// verdicts are unchanged either way.
    pub fn take_violations(&self) -> Vec<String> {
        std::mem::take(&mut *self.violations.lock().expect("violations register lock"))
    }

    /// The store-seam evaluation context (store + decode cache).
    fn store_ctx(&self) -> StoreCtx<'_> {
        StoreCtx {
            store: self.store.as_deref(),
            cache: &self.decode_cache,
        }
    }

    /// Render a three-valued walk outcome into the dispatch's
    /// `Result<bool, EvalError>`, banking the named violation at
    /// every decided-false (design point F-4). Born with the
    /// store-seam family; the semiring-cell family
    /// routes here too — any family whose decided-false branches
    /// carry adjudication words may.
    fn circuit_out(
        &self,
        name: &str,
        out: Result<Result<(), String>, String>,
    ) -> Result<bool, EvalError> {
        match out {
            Ok(Ok(())) => Ok(true),
            Ok(Err(why)) => {
                self.violations
                    .lock()
                    .expect("violations register lock")
                    .push(format!("{name}: {why}"));
                Ok(false)
            }
            Err(refuse) => Err(EvalError::CtxArg {
                name: name.to_string(),
                index: 0,
                why: refuse,
            }),
        }
    }

    /// Render the rate-cap walk's outcome: the
    /// [`Self::circuit_out`] semantics plus the vacuous-Holds face —
    /// `Ok(Ok(Some(note)))` HOLDS with the note banked on the
    /// register, so a vacuously-discharged obligation stays visible
    /// (design point D-4; kin to markflow's A-7 register pins).
    fn registered_out(
        &self,
        name: &str,
        out: crate::ratecap::RatecapOut,
    ) -> Result<bool, EvalError> {
        match out {
            Ok(Ok(note)) => {
                if let Some(why) = note {
                    self.violations
                        .lock()
                        .expect("violations register lock")
                        .push(format!("{name}: {why}"));
                }
                Ok(true)
            }
            Ok(Err(why)) => {
                self.violations
                    .lock()
                    .expect("violations register lock")
                    .push(format!("{name}: {why}"));
                Ok(false)
            }
            Err(refuse) => Err(EvalError::CtxArg {
                name: name.to_string(),
                index: 0,
                why: refuse,
            }),
        }
    }

    /// The provider-local index of a claimed entry, by name (`None`
    /// for roster entries whose family group did not resolve).
    pub fn local_by_name(&self, name: &str) -> Option<LocalId> {
        self.claimed
            .iter()
            .position(|(n, _, _)| *n == name)
            .map(|i| LocalId(i as u32))
    }

    /// The full evaluation path: argument cells (canonical encoding,
    /// declared field order) plus the certificate row context. This is
    /// the surface the seam-facing `filter` delegates to once the
    /// engine's row view exposes typed rows; applications and
    /// conformance batteries drive it directly today.
    pub fn filter_rows(&self, rel: LocalId, args: &[&[u8]], rows: &CertRows) -> Verdict {
        let Some((name, fields, kind)) = self.claimed.get(rel.0 as usize) else {
            return Verdict::Refused(format!("unknown local relation index {}", rel.0));
        };
        if args.len() != fields.len() {
            return Verdict::Refused(format!(
                "`{name}` expects {} argument(s), got {}",
                fields.len(),
                args.len()
            ));
        }
        let mut vals = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            match decode_cell(a) {
                Ok(v) => vals.push(v),
                Err(e) => return Verdict::Refused(format!("`{name}` argument {i}: {e}")),
            }
        }
        let refs: Vec<&Value> = vals.iter().collect();
        // A claimed entry implies its family vocabulary resolved
        // (construction invariant of `new`).
        let out = match kind {
            RelKind::Atomic { zero } => {
                let v = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                eval_atomic(name, &v.syntax, *zero, &refs, rows)
            }
            RelKind::Bl(k) => {
                let v = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                eval_bl(name, &v.bl, *k, &refs, rows)
            }
            RelKind::Morse => {
                let v = self
                    .vocab
                    .morse
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_morse(name, v, &refs, rows)
            }
            RelKind::Miranda => {
                let v = self
                    .vocab
                    .miranda
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_miranda(name, v, &refs, rows)
            }
            RelKind::StochWire => {
                let v = self
                    .vocab
                    .stochwire
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_stochwire(name, v, &refs, rows)
            }
            RelKind::BagCanon => {
                let v = self
                    .vocab
                    .bagcanon
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_bag_canon(name, v, &refs, rows)
            }
            RelKind::Mask(k) => {
                let v = self
                    .vocab
                    .mask
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_mask(name, v, *k, &refs, rows)
            }
            RelKind::PolyCanon => {
                let v = self
                    .vocab
                    .polycanon
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_poly_canonical(name, v, &refs, rows)
            }
            RelKind::Sys { w3 } => {
                let v = self
                    .vocab
                    .syswire
                    .as_ref()
                    .expect("claimed implies vocabulary");
                if *w3 {
                    eval_sys_w3(name, v, &refs, rows)
                } else {
                    eval_sys_causal(name, v, &refs, rows)
                }
            }
            RelKind::FlatEq => {
                let v = self
                    .vocab
                    .syswire
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_flatten(name, v, &refs, rows)
            }
            RelKind::Deadline => {
                let v = self
                    .vocab
                    .deadline
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_deadline_table(name, v, &refs, rows)
            }
            RelKind::Problog(k) => {
                let v = self
                    .vocab
                    .problog
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_problog(name, v, *k, &refs, rows)
            }
            RelKind::ConclForm(k) => {
                let blv = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                eval_conclform(
                    name,
                    &blv.bl,
                    self.vocab.barycoord.as_ref(),
                    self.vocab.cellapp.as_ref(),
                    *k,
                    &refs,
                    rows,
                )
            }
            RelKind::Lattice { product } => {
                let lv = self
                    .vocab
                    .lattice
                    .as_ref()
                    .expect("claimed implies vocabulary");
                let bv = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                if *product {
                    eval_product_lattice_checks(name, &bv.bl, lv, &refs, rows)
                } else {
                    eval_block_lattice_wf(name, &bv.bl, lv, &refs, rows)
                }
            }
            RelKind::Enclosure => {
                let v = self
                    .vocab
                    .enclosure
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_enclosure_witness_valid(name, v, &refs, rows)
            }
            RelKind::Carillon(k) => {
                let v = self
                    .vocab
                    .carillon
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_carillon(name, v, *k, &refs, rows)
            }
            RelKind::Surgery(k) => {
                let blv = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                let sv = self
                    .vocab
                    .surgery
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_surgery(name, &blv.bl, sv, *k, &refs, rows)
            }
            RelKind::Promise(k) => {
                let blv = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                let sv = self
                    .vocab
                    .surgery
                    .as_ref()
                    .expect("claimed implies vocabulary");
                let pv = self
                    .vocab
                    .promise
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_promise(name, &blv.bl, pv, sv, *k, &refs, rows)
            }
            RelKind::PredClass(k) => {
                let v = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                eval_predclass(name, &v.bl, *k, &refs, rows)
            }
            RelKind::BernCone(k) => {
                let bv = self
                    .vocab
                    .barycoord
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_berncone(
                    name,
                    self.vocab.bl.as_ref().map(|v| &v.bl),
                    bv,
                    self.vocab.subdivide.as_ref(),
                    self.vocab.dtype.as_ref(),
                    *k,
                    &refs,
                    rows,
                )
            }
            RelKind::SpdeMoment(k) => {
                let v = self
                    .vocab
                    .spdemoment
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_spdemoment(*k, name, v, &refs, rows)
            }
            RelKind::GymRw => {
                let v = self
                    .vocab
                    .gymrw
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_gymrw(name, v, &refs, rows)
            }
            RelKind::HoleCount => {
                let v = self
                    .vocab
                    .hole
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_hole_count(name, v, &refs, rows)
            }
            RelKind::GymEproc(k) => {
                let v = self
                    .vocab
                    .gymeproc
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_gymeproc(*k, name, v, &refs, rows)
            }
            RelKind::TrWf(k) => {
                let v = self
                    .vocab
                    .trwf
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Circuit-fragment routing: a
                // kernel-citation transition (a tr_kernel row on `tr`,
                // args bytewise (sys, tr)) routes grain/endo to the
                // ported circuit walk; every other shape rides the
                // landed P/T walk COMPLETELY UNTOUCHED. Where the
                // circuit vocabulary did not resolve, the P/T walk's
                // refusal of kernel content stays the loud deferral.
                let circuit_arm = match k {
                    TrWfKind::Grain | TrWfKind::Endo => self
                        .vocab
                        .circuit
                        .as_ref()
                        .filter(|cv| refs.len() == 2 && cv.cites_kernel(rows, refs[1])),
                    _ => None,
                };
                match circuit_arm {
                    Some(cv) => {
                        let ctx = self.store_ctx();
                        let out = match k {
                            TrWfKind::Grain => cv.eval_circuit_grain(&ctx, &refs, rows),
                            TrWfKind::Endo => cv.eval_circuit_endo(&ctx, &refs, rows),
                            _ => unreachable!("routing gates on grain/endo"),
                        };
                        self.circuit_out(name, out)
                    }
                    None => eval_trwf(name, v, *k, &refs, rows),
                }
            }
            RelKind::HPlate(k) => {
                let v = self
                    .vocab
                    .hplate
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_hplate(name, v, *k, &refs, rows)
            }
            RelKind::Guard(k) => {
                let v = self
                    .vocab
                    .guard
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_guard(name, v, *k, &refs, rows)
            }
            RelKind::ASel(k) => {
                let v = self
                    .vocab
                    .asel
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_asel(name, v, *k, &refs, rows)
            }
            RelKind::Swret => {
                let v = self
                    .vocab
                    .swret
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_swret(name, v, &refs, rows)
            }
            RelKind::Circuit(k) => {
                let ctx = self.store_ctx();
                let out = match k {
                    CircuitKind::KciteWf => {
                        let v = self
                            .vocab
                            .circuit
                            .as_ref()
                            .expect("claimed implies vocabulary");
                        v.eval_kcite_wf(&ctx, &refs, rows)
                    }
                    CircuitKind::GateScalar => {
                        let v = self
                            .vocab
                            .gatescalar
                            .as_ref()
                            .expect("claimed implies vocabulary");
                        v.eval_gate_scalar(&ctx, &refs, rows)
                    }
                };
                self.circuit_out(name, out)
            }
            RelKind::NnForm(k) => {
                let blv = self.vocab.bl.as_ref().expect("claimed implies vocabulary");
                let v = self
                    .vocab
                    .nnform
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_nnform(name, &blv.bl, v, *k, &refs, rows)
            }
            RelKind::Contract(k) => {
                let v = self
                    .vocab
                    .contract
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Three-valued like the circuit walks: decided-false
                // banks its named branch in the violations register
                // (design memo F-4, generalized past the store seam).
                self.circuit_out(name, eval_contract(name, v, *k, &refs, rows))
            }
            RelKind::Markflow => {
                let v = self
                    .vocab
                    .markflow
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Three-valued like the store-seam walks; decided
                // violations ride the same named-violations register.
                self.circuit_out(name, v.eval_markflow(&refs, rows))
            }
            RelKind::DwellGate => {
                let v = self
                    .vocab
                    .dwellgate
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Three-valued like the circuit family; the walk
                // decodes the cited net itself (it needs the full
                // graph for the symbolic fold, not the interface
                // summary the circuit cache carries).
                self.circuit_out(name, v.eval_dwell_gate(self.store.as_deref(), &refs, rows))
            }
            RelKind::TrRatecap => {
                let v = self
                    .vocab
                    .ratecap
                    .as_ref()
                    .expect("claimed implies vocabulary");
                self.registered_out(name, v.eval_tr_ratecap(None, &refs, rows))
            }
            RelKind::WireCausality => {
                let v = self
                    .vocab
                    .wirecausality
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Three-valued like the markflow walk; decided
                // violations ride the same named-violations register.
                self.circuit_out(name, v.eval_wire_causality(&refs, rows))
            }
            RelKind::AvgBattery => {
                let v = self
                    .vocab
                    .avgbattery
                    .as_ref()
                    .expect("claimed implies vocabulary");
                // Three-valued; decided violations ride the named-
                // violations register. HOLDS is unreachable at v0
                // (the walk's loud deferral, its module doc arm 8).
                self.circuit_out(name, v.eval_avg_battery(&refs, rows))
            }
            RelKind::Dabs(k) => {
                let v = self
                    .vocab
                    .dabs
                    .as_ref()
                    .expect("claimed implies vocabulary");
                eval_dabs(name, v, *k, &refs, rows)
            }
            RelKind::Dgc(k) => {
                let v = self.vocab.dgc.as_ref().expect("claimed implies vocabulary");
                eval_dgc(name, v, *k, &refs, rows)
            }
        };
        match out {
            Ok(true) => Verdict::Holds,
            Ok(false) => Verdict::Fails,
            Err(e) => Verdict::Refused(e.to_string()),
        }
    }
}

impl GroundProvider for QtslGroundProvider {
    fn info(&self) -> ProviderInfo {
        ProviderInfo {
            name: "qtsl-ground".to_string(),
            semantics_revs: self.semantics_revs.clone(),
        }
    }
    fn relations(&self) -> &[RelExpectation] {
        &self.rels
    }
    fn functions(&self) -> &[FnExpectation] {
        &[]
    }
    fn evaluator(&self) -> &dyn GroundEval {
        self
    }
}

impl GroundEval for QtslGroundProvider {
    fn filter(&self, rel: LocalId, _args: &[&[u8]], ctx: &EvalCtx<'_>) -> Verdict {
        let name = self
            .claimed
            .get(rel.0 as usize)
            .map(|(n, _, _)| *n)
            .unwrap_or("?");
        match ctx {
            // Every claimed relation is Snapshot-scoped, so the engine
            // routes Pure evaluations to a refusal before the provider
            // is consulted; this arm is unreachable through the binder
            // and refuses identically if reached directly.
            EvalCtx::Pure => Verdict::Refused(format!(
                "`{name}` is a row-context relation and was evaluated without a row snapshot"
            )),
            // The seam's row view does not yet expose typed row
            // content; refusing (conservative, loud) is the honest
            // verdict — `filter_rows` is the full path, and this arm
            // delegates to it the moment the view carries rows.
            EvalCtx::Snapshot(_) => Verdict::Refused(format!(
                "`{name}`: the engine's row view does not yet expose typed row content; \
                 evaluation is available via QtslGroundProvider::filter_rows"
            )),
        }
    }

    fn eval_fn(&self, _f: LocalId, _args: &[&[u8]]) -> Bind {
        Bind::Refused("qtsl-ground claims no ground functions".to_string())
    }

    fn invert_fn(
        &self,
        _f: LocalId,
        _output: &[u8],
        _known: &[(usize, &[u8])],
        _missing: usize,
    ) -> Bind {
        Bind::Refused("qtsl-ground claims no ground functions".to_string())
    }

    fn cmp(&self, rel: LocalId, _a: &[u8], _b: &[u8]) -> Result<Ordering, String> {
        let name = self
            .claimed
            .get(rel.0 as usize)
            .map(|(n, _, _)| *n)
            .unwrap_or("?");
        Err(format!("`{name}` declares no order semantics"))
    }

    fn monotone_key(&self, rel: LocalId, _cell: &[u8]) -> Result<i128, String> {
        let name = self
            .claimed
            .get(rel.0 as usize)
            .map(|(n, _, _)| *n)
            .unwrap_or("?");
        Err(format!("`{name}` declares no fixed-width monotone key"))
    }
}

// ------------------------------------------------------------ dispatch

/// Decode exactly one canonical value from a cell. `Err` carries the
/// refusal reason (malformed, non-canonical, or trailing bytes) — a
/// tampered cell fails here, at the boundary, before any structural
/// walk could be misled by it.
fn decode_cell(bytes: &[u8]) -> Result<Value, String> {
    let mut c = Cursor::new(bytes);
    let v = Value::decode(&mut c).map_err(|e| format!("cell decode refused: {e}"))?;
    let rest = c.remaining();
    if rest != 0 {
        return Err(format!(
            "cell carries {rest} trailing byte(s) past one canonical value"
        ));
    }
    Ok(v)
}

/// Applicability-family dispatch: unpack the argument cells per family
/// shape (bytewise field order, verified at binding) and run the
/// [`crate::blapplic`] evaluator.
fn eval_bl(
    name: &str,
    v: &BlVocab,
    kind: BlKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let nat_arg = |index: usize| -> Result<u64, EvalError> {
        let Value::Lit(l) = args[index] else {
            return Err(EvalError::ArgDtype {
                name: name.into(),
                index,
                expected: "Nat",
                found: 0xFF,
            });
        };
        let LiteralView::Nat(n) = l.view() else {
            return Err(EvalError::ArgDtype {
                name: name.into(),
                index,
                expected: "Nat",
                found: l.dtype_code(),
            });
        };
        Ok(n)
    };
    match kind {
        BlKind::PolyCanonEq => {
            let l = elem_local(name, 0, args[0], rows)?;
            let r = elem_local(name, 1, args[1], rows)?;
            bl::eval_polynomial_canonical_eq(name, v, rows, l, r)
        }
        BlKind::PremiseContains => {
            let pre = elem_local(name, 0, args[0], rows)?;
            let sub = elem_local(name, 1, args[1], rows)?;
            bl::eval_premise_contains(name, v, rows, pre, sub)
        }
        BlKind::SyzygyConclForm => {
            let c = elem_local(name, 0, args[0], rows)?;
            let f = elem_local(name, 1, args[1], rows)?;
            bl::eval_syzygy_conclusion_form(name, v, rows, c, f)
        }
        BlKind::FarkasValid => {
            // Field order: combinationCoeffs, conclusion, premise.
            let cc = elem_local(name, 0, args[0], rows)?;
            let conclusion = elem_local(name, 1, args[1], rows)?;
            let premise = elem_local(name, 2, args[2], rows)?;
            bl::eval_farkas_combination_valid(name, v, rows, cc, conclusion, premise)
        }
        BlKind::SyzygyValid => {
            let p = elem_local(name, 0, args[0], rows)?;
            let fields = v.syzygy.clone();
            bl::eval_combo_node_valid(name, v, &fields, rows, p)
        }
        BlKind::PBoundValid => {
            let p = elem_local(name, 0, args[0], rows)?;
            let fields = v.pbound.clone();
            bl::eval_combo_node_valid(name, v, &fields, rows, p)
        }
        BlKind::PsdTWitness => {
            let p = elem_local(name, 0, args[0], rows)?;
            let fields = v.psd_t.clone();
            bl::eval_psd_square_witness(name, v, &fields, false, rows, p)
        }
        BlKind::PsdDdWitness => {
            let p = elem_local(name, 0, args[0], rows)?;
            let fields = v.psd_dd.clone();
            bl::eval_psd_square_witness(name, v, &fields, true, rows, p)
        }
        BlKind::PsdTConcl => {
            let p = elem_local(name, 0, args[0], rows)?;
            let f = v.psd_t.clone();
            bl::eval_psd_concl(name, v, rows, p, f.n, f.a, f.term, f.conclusion, None)
        }
        BlKind::PsdDdConcl => {
            let p = elem_local(name, 0, args[0], rows)?;
            let f = v.psd_dd.clone();
            bl::eval_psd_concl(name, v, rows, p, f.n, f.a, f.term, f.conclusion, None)
        }
        BlKind::PsdKWitness => {
            let p = elem_local(name, 0, args[0], rows)?;
            bl::eval_psd_k_witness(name, v, rows, p)
        }
        BlKind::PsdKConcl => {
            let p = elem_local(name, 0, args[0], rows)?;
            let f = v.psd_k.clone();
            bl::eval_psd_concl(
                name,
                v,
                rows,
                p,
                f.n_total,
                f.a,
                f.term,
                f.conclusion,
                Some((f.m, f.k)),
            )
        }
        BlKind::WiresPos => {
            // Field order: conclusion, pre.
            let conclusion = elem_local(name, 0, args[0], rows)?;
            let pre = elem_local(name, 1, args[1], rows)?;
            bl::eval_positive_size_wires(name, v, rows, conclusion, pre)
        }
        BlKind::WiresPosForm => {
            let form = elem_local(name, 0, args[0], rows)?;
            bl::eval_positive_size_wires_form(name, v, rows, form)
        }
        BlKind::WiresPosTerm => {
            let conclusion = elem_local(name, 0, args[0], rows)?;
            bl::eval_positive_size_wires_term(name, v, rows, conclusion)
        }
        BlKind::ConstExact => {
            // Field order: bowtie, l, r.
            let bowtie = nat_arg(0)?;
            let l = elem_local(name, 1, args[1], rows)?;
            let r = elem_local(name, 2, args[2], rows)?;
            bl::eval_const_exact_eval_true(name, v, rows, bowtie, l, r)
        }
    }
}
