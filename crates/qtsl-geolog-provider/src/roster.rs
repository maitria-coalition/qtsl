//! The claimed-roster row shape and dispatch kinds.
//!
//! Each evaluator family declares its slice of the claimed roster as a
//! `const ENTRIES` beside its evaluators ([`crate::blapplic`],
//! [`crate::atomic`], [`crate::morse`], [`crate::miranda`],
//! [`crate::stochwire`], [`crate::bagcanon`], [`crate::polycanon`],
//! [`crate::syswire`], [`crate::problog`], [`crate::trwf`]); the provider
//! concatenates the family slices at registration in a fixed family
//! order ([`crate::provider`]). Roster growth stays family-local: a
//! new relation is a row in its own family's table, never an edit to
//! a shared monolith.

/// One claimed entry: `(name, fields, kind)`. Field names and their
/// bytewise order are part of the claim: the binder verifies them
/// against the declared signature, and they fix the evaluator's
/// argument order.
pub(crate) type EntryRow = (
    &'static str,
    &'static [(&'static str, &'static str)],
    RelKind,
);

/// The applicability-family dispatch kinds, in expectation-table order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BlKind {
    PolyCanonEq,
    PremiseContains,
    SyzygyConclForm,
    FarkasValid,
    SyzygyValid,
    PBoundValid,
    PsdTWitness,
    PsdTConcl,
    PsdDdWitness,
    PsdDdConcl,
    PsdKWitness,
    PsdKConcl,
    WiresPos,
    WiresPosForm,
    WiresPosTerm,
    ConstExact,
}

/// The mask-family dispatch kinds ([`crate::blmask`]): bounded sweeps
/// over the sealed finite membership data of Simplex/ExtensionSet
/// rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MaskKind {
    /// `extensionSetOmits` — v is NOT in S's mask.
    ExtOmits,
    /// `extensionSetSameMembers` — mask equality on extension sets.
    ExtSameMembers,
    /// `isExtensionSetEmpty` — holds iff S's mask is EMPTY (the
    /// polarity adjudicated on the registry row: name + axiom guards
    /// against the declaration comment's source typo).
    ExtEmpty,
    /// `simplexIsFaceMinus` — sface's mask == s's mask minus {v0}.
    FaceMinus,
    /// `simplexIsIntersection` — sint's mask == s1's mask ∩ s2's mask.
    Intersection,
    /// `simplexSameMembers` — mask equality on simplexes.
    SameMembers,
}

/// The conclusion-form family dispatch kinds ([`crate::blconclform`]):
/// bounded checks that a Formula element IS a specific formula
/// constructed from certificate geometry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConclFormKind {
    /// `barycentricHalfspaceForm` — the region-atom rules'
    /// barycentric-halfspace conjunction, in the realized all-`le`
    /// canonical form.
    BarycentricHalfspace,
    /// `cellStrictInteriorForm` — the cell rules' strict-interior
    /// conjunction: per vertex of cell `whichI`'s simplex, one strict
    /// atom over the RAW λ-terms (`TAdd(TConst(c), TMul(TConst(s),
    /// TVar(input)))` — no rescale, no zero-offset layout; the
    /// `baryLambdas1D` rendering, distinct from the halfspace form's).
    CellStrictInterior,
    /// `cellOneHotForm` — `(b_whichI = 1) AND chainAnd(b_j = 0, j ≠
    /// whichI)` over the app's output wires (a single-cell schema
    /// yields `(b_0 = 1) AND FTrue`; a two-cell schema's second arm is
    /// the bare atom).
    CellOneHot,
    /// `cellOutWitnessForm` — ONE strict separating λ-atom at
    /// `witnessVertex` (which must belong to cell `whichJ`'s simplex
    /// mask — decided false otherwise), sign REVERSED against the
    /// strict-interior atoms.
    CellOutWitness,
    /// `cellOutZeroForm` — the single atom `(b_whichJ = 0)`.
    CellOutZero,
    /// `lirpaConclusionForm` — the LiRPA relaxation rule's conclusion
    /// shape: `FAnd(FAtomLE(affine(β, α, preact), TVar(post)),
    /// FAtomLE(TVar(post), affine(δ, γ, preact)))` where
    /// `affine(c, s, w) = TAdd(TConst(c), TMul(TConst(s), TVar(w)))`
    /// — the Lean `affineWireTerm` layout: offset FIRST in the sum,
    /// constants on the LEFT, no zero special cases.
    Lirpa,
}

/// The ProbLog-family dispatch kinds ([`crate::problog`]): the
/// certified-bracket obligation species — saturation runs and exact
/// product-measure arithmetic over ground definite programs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProblogKind {
    /// `qtsl_problog_wf` — P1 well-formedness of the program value.
    Wf,
    /// `qtsl_problog_derives` — P3: the query derives with exactly the
    /// world's coins true.
    Derives,
    /// `qtsl_problog_blocks` — P5: the cut's absence blocks every
    /// proof (complement run).
    Blocks,
    /// `qtsl_problog_exact` — P2: full world enumeration.
    Exact,
    /// `qtsl_problog_lower` — P3+P4: rows derive + inclusion–exclusion.
    Lower,
    /// `qtsl_problog_upper` — P5+P6: cuts block + min-over-cuts.
    Upper,
    /// `qtsl_problog_bonferroni` — P3+P4-truncated: rows derive + the
    /// even-depth inclusion–exclusion prefix (a sound lower bound past
    /// the full-IE cap, by Bonferroni's inequality).
    Bonferroni,
    /// `qtsl_problog_compiled` — P8+P9+P10 as one self-contained sound
    /// judgment: `p` is EXACTLY the query probability, certified by a
    /// leaf-covered decision term (exact beyond enumeration; the
    /// memoized requirement-set calculus).
    Compiled,
}

/// The carillon discharge-plan dispatch kinds ([`crate::carillon`]):
/// the R2–R5 grid/region/manifest recomputes ported from the carillon
/// producer's executable references.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CarillonKind {
    /// `qtsl_cell_cover` — R2: the named grid cells cover the region
    /// box, fail-closed on holes.
    CellCover,
    /// `qtsl_dbar_closure` — R3: dbar equals the mode's one-jump
    /// closed-domain hull.
    DbarClosure,
    /// `qtsl_gap_a` — R4: every reset image lands in its destination
    /// domain (1-D as specced; the stop set is empty at this
    /// declaration's grain).
    GapA,
    /// `qtsl_lowbound_boxes` — R5: the cover is an exact box cover of
    /// (region ∩ dbar).
    FloorBoxes,
}

/// The promise-family dispatch kinds ([`crate::blpromise`]): the two
/// PPromise interface-confinement side-conditions — free-wire sweeps
/// against the node's declared interface, the second over the
/// RECOMPUTED context (the consumer's premise with the contract slot
/// blanked to `FTrue` — never a carried formula).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PromiseKind {
    /// `promiseContractConfined` — every free wire of the contract is
    /// among the node's iface wires (Lean: `formulaWiresWithin`).
    ContractConfined,
    /// `promiseWiresSeparated` — every free wire of the supplier's
    /// premise that is also free in the recomputed context or in the
    /// node's conclusion is among the iface wires (Lean:
    /// `wiresSeparated`).
    WiresSeparated,
}

/// The predicate-class dispatch kinds ([`crate::blpredclass`]): the
/// three semantic-class verdicts over one total classifier
/// (`classifyPred` in the Lean catalogue) — a closed-world fragment
/// recognizer whose `none` is semantic falsity for all three Props.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PredClassKind {
    /// `isConicPredicate` — the satisfying set is a closed convex
    /// cone: `(classifyPred P).map (·.conic) = some true`.
    Conic,
    /// `isConvexPredicate` — the satisfying set is closed convex:
    /// `(classifyPred P).isSome` (recognizer acceptance — strictly
    /// weaker than the conic bit).
    Convex,
    /// `isUpwardClosedConicPredicate` — closed conic up-set: both
    /// class bits (`conic && upClosed`).
    UpClosedConic,
}

/// The surgery-family dispatch kinds ([`crate::blsurgery`]): the
/// proof-theory context machinery — ∧-tree path reads/writes and the
/// two substitution relations, each an equality-with-the-build decided
/// by parallel structural descent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SurgeryKind {
    /// `conjunctAt` — `form.conjGet? path = some sub` (off-tree paths
    /// decide false).
    ConjAt,
    /// `conjReplace` — `form.conjReplace? path sub = some result`.
    ConjReplace,
    /// `substituteInFormula` — `result = form[TVar(wire) := term]`.
    SubstForm,
    /// `applyPredicateToTerm` — `result = predicate[THole := arg]`
    /// (the row transport of `P.subst predicateHole arg`).
    ApplyPred,
}

/// The Bernstein-cone family's dispatch kinds ([`crate::berncone`]):
/// the region calculus's heavy recompute pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BernConeKind {
    /// `allForwardDiffBernCoeffsSatisfyP` — the exact-rational
    /// Bernstein forward-difference coefficient sweep (recomputed;
    /// BernCone nodes carry no coefficient data).
    Coeffs,
    /// `coverInfeasibilityValid` — the subdivision rule's 1-D interval
    /// cover, recomputed from the branch regions (the carried cover
    /// certificate is not consulted).
    Cover,
    /// `allForwardDiffBernIntvEnclosuresSatisfyP` — the float lane:
    /// the same forward-difference grid recomputed in validated
    /// dtype-interval arithmetic ([`crate::fpintv`]), P checked at the
    /// lower endpoints.
    IntvCoeffs,
}

/// Family dispatch: which evaluator a claimed entry routes to.
#[derive(Debug, Clone, Copy)]
pub(crate) enum RelKind {
    Bl(BlKind),
    Atomic {
        zero: bool,
    },
    Morse,
    Miranda,
    StochWire,
    BagCanon,
    Mask(MaskKind),
    PolyCanon,
    /// The composite well-posedness pair (`w3: false` =
    /// `qtsl_sys_causal`, `w3: true` = `qtsl_sys_w3`).
    Sys {
        w3: bool,
    },
    /// `qtsl_flatten` — the QFlatEq discharge's v1 fiber
    /// ([`crate::syswire`] module doc: reflexive SysMech face decided,
    /// the composite fiber a loud deferral until its row vocabulary
    /// stages).
    FlatEq,
    /// `qtsl_deadline_table` — the exact finite-horizon
    /// deadline-table walk ([`crate::deadline`]): the certified-gym
    /// exact-lane checker's WF/B/S/C obligations recomputed from the
    /// node's closure alone.
    Deadline,
    Problog(ProblogKind),
    ConclForm(ConclFormKind),
    /// The block-lattice family ([`crate::bllattice`]):
    /// `product: false` = `blockLatticeWF` (record well-formedness),
    /// `product: true` = `productLatticeChecks` (facet discharge,
    /// confinement, disjointness, product correctness).
    Lattice {
        product: bool,
    },
    /// The enclosure family ([`crate::enclosure`]):
    /// `enclosureWitnessValid` — the remainder-bound witness check
    /// (Maclaurin prefix recompute, radius guard, exact tail cap).
    Enclosure,
    /// The carillon discharge-plan family ([`crate::carillon`]): the
    /// R2–R5 grid/region/manifest recomputes.
    Carillon(CarillonKind),
    /// The Formula/Term surgery family ([`crate::blsurgery`]).
    Surgery(SurgeryKind),
    /// The promise interface-confinement family ([`crate::blpromise`]).
    Promise(PromiseKind),
    /// The predicate semantic-class family ([`crate::blpredclass`]):
    /// `isConicPredicate` / `isConvexPredicate` /
    /// `isUpwardClosedConicPredicate` over the shared Formula/Term
    /// walk substrate.
    PredClass(PredClassKind),
    /// The Bernstein-cone family ([`crate::berncone`]).
    BernCone(BernConeKind),
    /// The SPDE moment-core family ([`crate::spdemoment`]): the
    /// stochastic-heat/Burgers expected-energy certificates' beta
    /// discipline, tier-(ii)/(iii) witnesses, and S1 summed-floor
    /// enclosures — all recompute-from-primary-data.
    SpdeMoment(SpdeKind),
    /// The gym reward-table family ([`crate::gymrw`]):
    /// `gymRwTableValid` — the finite-horizon expected-total-reward
    /// table walk over primary-data rows (well-formedness, boundary,
    /// step, claim-mixture obligations recomputed from the
    /// dimensions in exact integer arithmetic).
    GymRw,
    /// The gymnasium e-process family ([`crate::gymeproc`]): the
    /// betting-martingale anytime-valid lower-confidence-bound
    /// certificates — the full Q32.96 wealth walk recomputed from the
    /// sealed protocol constants and rollout ledger at every
    /// discharge.
    GymEproc(GymEprocKind),
    /// The transition/bag well-formedness family ([`crate::trwf`]):
    /// the C-TR-CONTENT / C-TR-GRAIN / C-TR-ENDO / C-JD-MASSONE /
    /// C-BAG admission side-conditions over Transition, ScaleView,
    /// and bag-mechanism rows.
    TrWf(TrWfKind),
    /// The HPlate certificate-stratum family + the PAlways-from-fold
    /// tie walk ([`crate::hplate`]) — the P/T fragment evaluators,
    /// gated on the event-4 passenger vocabulary (`hplate_token`,
    /// `QPAlwaysFromFold`): the whole family resolves only against
    /// closures that carry those names.
    HPlate(HPlateKind),
    /// The hole family ([`crate::hole`]): `qtsl_hole_count` — the
    /// seat-regret linearity ledger, a bounded occurrence walk over
    /// the System term tree.
    HoleCount,
    /// The guarded-specification / satisfaction-claim family
    /// ([`crate::guard`]): the initial-membership demand, the
    /// warrant-component membership, and the C-SPEC / C-CERT-CLAIM
    /// conformance walks over the event-4 spec-record vocabulary.
    Guard(GuardKind),
    /// The angelic-selection family ([`crate::asel`]): the
    /// positional-selection witness's seven side-conditions over the
    /// ASelWitness/ASelCell vocabulary, the TrClock three wings, and
    /// the compiled verdict form.
    ASel(ASelKind),
    /// The drift-moment tie family ([`crate::swret`]):
    /// `qtsl_intbound_sw` — the `QIntBoundFromSW` node's nine-step
    /// integral-ceiling walk (event-5 passenger vocabulary: the family
    /// resolves only against closures carrying the node sort).
    Swret,
    /// The store-seam circuit family ([`crate::circuit`]):
    /// evaluators whose subject cites a hypernet by digest —
    /// decode-then-digest against the [`crate::store`] seam. The
    /// grain/endo circuit ARMS ride the trwf entries by dispatch
    /// routing; only the two NEW relations carry this kind.
    Circuit(CircuitKind),
    /// The NN conclusion-form oracle family ([`crate::nnform`]):
    /// the nine ReLU/LiRPA premise- and conclusion-shape
    /// relations — the cell-form pattern over the PReLU application's
    /// position-0 ports, shapes pinned by the Lean catalogue's
    /// rule-data types (`PReLUPosData` … `PLiRPAData`).
    NnForm(NnFormKind),
    /// The primitive-box semiring-cell family ([`crate::contract`]):
    /// conjugation-parameter conformance and the v1
    /// cell verdict over `contract_semiring` rows.
    Contract(ContractKind),
    /// The MarkFlow walk family ([`crate::markflow`]):
    /// `qtsl_wire_markflow` — the two-column recompute over a
    /// `QWireComposeMarks` node's declaration closure (stage-label
    /// difference constraints + zero-lag-cycle carve coverage), the
    /// ∃-dual of the causality walk. No store: carve gates are
    /// digest citations whose conformance is `qtsl_gate_scalar`'s
    /// own chased demand.
    Markflow,
    /// The dwell-gate walk ([`crate::dwellgate`]):
    /// `qtsl_dwell_gate` — gate-inside-window over the carved-window
    /// wing (containment + nonemptiness of the cited gate's
    /// sign-fiber against `[floor, ceil]`), a store-seam walk: the
    /// gate is cited by digest and the v1 fragment folds cell-free
    /// unary rational nets to one univariate polynomial. No
    /// certificate argument in the theory signature — evaluator-
    /// computed discharge (design points D-1/D-5).
    DwellGate,
    /// The rate-cap walk ([`crate::ratecap`]):
    /// `qtsl_tr_ratecap` — `rate(x) <= majorant` on the transition's
    /// active region (the kernel's non-stay support; ENABLING IS
    /// DERIVED), for scale-view transitions on a race clock. "Sound
    /// unconditionally, no citation spine" (the theory's own
    /// discharge semantics); no store. All-stay mixes hold vacuously
    /// with the vacuity register-named.
    TrRatecap,
    /// The causality walk family ([`crate::wirecausality`]):
    /// `qtsl_wire_causality` — the declared-rank recompute
    /// over a `QWireCompose` node's declaration closure (one rank
    /// per component, strict increase along every directed wire of
    /// the cited certificate's wiring — no cyclic wiring can pass),
    /// the ∀-face sibling the MarkFlow walk is the ∃-dual of. No
    /// store; no unminted content anywhere in the walk.
    WireCausality,
    /// The LRA-battery walk family ([`crate::avgbattery`]):
    /// `qtsl_avg_battery` — the structural stratum of the
    /// `QAvgBattery` node (conclusion resolution, face recompute from
    /// the concluded root, arg correspondence, face-keyed family
    /// demands, exact tie coherence), with the leaf-sequent
    /// correspondence stratum loudly deferred pending the
    /// generator-seam recompute — HOLDS is unreachable at v0 by
    /// design (fail-closed). The claim relation awaits the
    /// rules-as-rows fan's mint; see the module doc's claim-status
    /// note. No store.
    AvgBattery,
    /// The DtmcAbsorb family ([`crate::dabs`]): finite-horizon
    /// absorption brackets over the chain species' stored rows — the
    /// labeled-state well-formedness demand and the two bracket
    /// claims, all recomputed by the exact-Q T-step evaluation of the
    /// completed kernel. Staged-fragment vocabulary: the family
    /// resolves only against closures carrying `DAbsQuery`. No store.
    Dabs(DabsKind),
    /// The DtmcContraction family ([`crate::dgc`]): the strengthened
    /// generator-form demand (R18) and its four claim relations over
    /// the chain species' stored rows — regional contraction under
    /// the completed kernel, exact partial survival sums, the
    /// κ-derived geometric assemblies. Resolves only against closures
    /// carrying `DGenContraction`. No store.
    Dgc(DgcKind),
}

/// The DtmcContraction family's dispatch kinds ([`crate::dgc`]): the
/// strengthened generator-form demand and its claim relations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DgcKind {
    /// `qtsl_dtmc_genform_contraction` — the R18 demand: shape/range,
    /// no re-entry, per-region-state contraction, offset prologue
    /// determinism where declared, cross-face same-chain coincidence.
    Genform,
    /// `qtsl_dgc_partial_lo` — `lo ≤` the exact partial survival sum.
    PartialLo,
    /// `qtsl_dgc_ev_bracket` — the first-moment bracket
    /// (`lo ≤ L`, `hi ≥ L + κ·W/(1−c)`); demands `c < 1`.
    EvBracket,
    /// `qtsl_dgc_survival_tail` — the geometric survival envelope
    /// (`rate ∈ [c, 1)`, `coeff·rate^horizon ≥ κ·W`).
    SurvivalTail,
    /// `qtsl_dgc_z_one` — termination mass exactly one.
    ZOne,
}

/// The NN conclusion-form family's dispatch kinds
/// ([`crate::nnform`]). Every relation destructures the cited PReLU
/// application's position-0 ports (`h` = input wire, `y` = output
/// wire) and decides whether `formula` IS the pinned shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NnFormKind {
    /// `reluPremNonnegForm` — `FAtomGE(TVar(h), TConst(0))`
    /// (Lean: `.atom .ge (.var preact) (.const 0)`).
    ReluPremNonneg,
    /// `reluPremNonposForm` — `FAtomLE(TVar(h), TConst(0))`.
    ReluPremNonpos,
    /// `reluOutEqInputForm` — `FAtomEQ(TVar(y), TVar(h))`.
    ReluOutEqInput,
    /// `reluOutZeroForm` — `FAtomEQ(TVar(y), TConst(0))`.
    ReluOutZero,
    /// `reluOutNonnegForm` — `FAtomGE(TVar(y), TConst(0))`.
    ReluOutNonneg,
    /// `reluOutDominatesForm` — `FAtomGE(TVar(y), TVar(h))`.
    ReluOutDominates,
    /// `lirpaPremLoForm` — `FAtomLE(TConst(a), TVar(h))`, `a` pinned.
    LirpaPremLo,
    /// `lirpaPremHiForm` — `FAtomLE(TVar(h), TConst(b))`, `b` pinned.
    LirpaPremHi,
    /// `lirpaSandwichForm` — the `lirpaConclusionForm` build over the
    /// app's own ports: `FAnd(FAtomLE(affine(β, α, h), TVar(y)),
    /// FAtomLE(TVar(y), affine(δ, γ, h)))` — one rendering, one
    /// implementation (the walk reuses [`crate::blconclform`]'s
    /// `affine_wire_term`).
    LirpaSandwich,
}

/// The semiring-cell family's dispatch kinds ([`crate::contract`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractKind {
    /// `qtsl_contract_param` — conjugation-parameter conformance,
    /// exactly as `qtsl_hplate_param_wire`: integrality + the p ≥ 1
    /// floor decide false; even p refuses on the missing certified
    /// operand-range home; exp refuses on the enclosure register.
    Param,
    /// `qtsl_contract_cell` v1 — hagSum decides TRUE (φ = id, the
    /// default made formal); conjugated kinds LOUD-DEFER with the
    /// case named (positive φ-space checking awaits the
    /// semiring-generic evaluator); idempotent kinds decide FALSE
    /// (no φ-route exists structurally).
    CellV1,
}

/// The store-seam circuit family's dispatch kinds
/// ([`crate::circuit`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitKind {
    /// `qtsl_kcite_wf` — C-JD-KCITE: decode-then-digest against the
    /// cited store object plus the roster/arity/typing discipline
    /// (tags within arities, one-hot Boolean tag wires, payload
    /// positional).
    KciteWf,
    /// `qtsl_gate_scalar` — decode + digest tie + codomain exactly
    /// one rational scalar wire (Boolean scalar codomains refuse with
    /// the case named).
    GateScalar,
}

/// The guard family's dispatch kinds ([`crate::guard`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardKind {
    /// `qtsl_init_member` — the subject's initial data lies inside the
    /// warrant's region (bag-marking point and init-box leaves on
    /// `qraBox` regions; other constructor pairs loudly deferred).
    InitMember,
    /// `qtsl_warrant_member` — the cited component is among the
    /// claimed spec's consumed components, through any depth of
    /// disjunction (C-CERT-CLAIM membership).
    WarrantMember,
    /// `qtsl_spec_wf` — the record's own well-formedness walk
    /// (C-SPEC / C-SPEC-GUARD, incl. the PD-6 guard-vs-warrant
    /// store-and-check and the residual parity walk).
    SpecWf,
    /// `qtsl_cert_claim_wf` — the per-claim conformance walk
    /// (C-CERT-CLAIM: route counting + exclusivity, zero-hole ledger).
    CertClaimWf,
    /// `qtsl_base_exact` — positive Θ₀ membership: constants, atoms
    /// over actual `oPoly` images, and/or/or-list closure; provably
    /// nonbase formers decide false, unknown extension constructors
    /// refuse (the F-2 review repair: a fail-closed positive check).
    BaseExact,
}

/// The transition/bag well-formedness dispatch kinds
/// ([`crate::trwf`]): the Transition former's admission
/// side-conditions and the bag former's counting demands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TrWfKind {
    /// `qtsl_tr_content` — exactly one content presentation per
    /// transition (C-TR-CONTENT), plus the exactly-one grain/clock
    /// attributes and the mirrored clock-floor rows.
    Content,
    /// `qtsl_tr_grain` — the grain's wire list against the attached
    /// system's marked-population state block (C-TR-GRAIN).
    Grain,
    /// `qtsl_tr_endo` — next payloads typed at the attached system's
    /// state: reset widths, enclosure widths and bounds (C-TR-ENDO).
    Endo,
    /// `qtsl_massone` — per scale view, branch weights total exactly
    /// one in (0, 1] (C-JD-MASSONE).
    MassOne,
    /// `qtsl_bag_wf` — the bag former's counting demands (C-BAG).
    BagWf,
}

/// The HPlate family's dispatch kinds ([`crate::hplate`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HPlateKind {
    /// `qtsl_hplate_footprint` — subject agreement + the Dirac fold
    /// displacement against the row's polarity bound.
    Footprint,
    /// `qtsl_hplate_coverage` — the conservative may-touch roster
    /// carries a footprint row per cited plate.
    Coverage,
    /// `qtsl_hplate_flow` — the trivial P/T between-firings case.
    Flow,
    /// `qtsl_hplate_lowbound` — the fold's lower bound via the
    /// nonnegative-features route (P/T fragment; coupling routes
    /// refuse).
    Floor,
    /// `qtsl_palways_fold` — the judgment-tie design's ten-step
    /// walk + the step-4.11 pathwise-species demand.
    Tie,
    /// `qtsl_firebound_fold` — the transfer-former twelve-step walk
    /// (the FromFold genus's ranking face: count ceiling from one
    /// gap-rowed cert + pinned dmin + floor + flow).
    FireBound,
    /// `qtsl_firecount_roster` — pairing-relative roster conformance
    /// for `retFireCount` (membership, duplicate-freedom, nonempty).
    FireRoster,
    // Appended at the END (the colored tier joined after the
    // original roster; appending keeps existing positions stable).
    /// `qtsl_hplate_param_cert` — conjugation-parameter conformance
    /// at the certificate scale (integrality; even-p nonneg range;
    /// exp defers on the enclosure register).
    ParamCert,
    /// `qtsl_hplate_param_wire` — the same conformance at one pooled
    /// wire.
    ParamWire,
}

/// The gymnasium e-process dispatch kinds ([`crate::gymeproc`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GymEprocKind {
    /// `gymEprocDetValid` — the deterministic Ville verdict: wealth
    /// walk at `mDet` against `1/alpha`, plus the raw-units bound tie.
    Det,
    /// `gymEprocRandValid` — the randomized last look: wealth walk at
    /// `mRand` against `u/alpha` (exact 256-bit compare), the declared
    /// `u`-protocol row demanded, plus the improved bound's tie.
    Rand,
}

/// The SPDE moment-core dispatch kinds ([`crate::spdemoment`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpdeKind {
    /// `spdeClaimValid` — spectrum WF + Itô-correction recompute +
    /// beta discipline + floor row.
    Claim,
    /// `spdeTierWitnessValid` — tier-(ii) trajectory enclosures
    /// (verbatim exp-bracket recompute) + tier-(iii) attainment.
    TierWit,
    /// `spdeSummedFloorValid` — S1 powered-bracket enclosures at
    /// canonical minimal power + the floor-tie falsifier.
    SummedFloor,
}

/// The DtmcAbsorb family's dispatch kinds ([`crate::dabs`]): the
/// absorption-query species' three side-conditions over the chain
/// species' stored rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DabsKind {
    /// `qtsl_dabs_wf` — every classed or rejected state of the query
    /// is stored-absorbing (no stored outgoing row, or exactly the
    /// unit self-loop).
    Wf,
    /// `qtsl_dabs_absorb_bracket` — `lo ≤ N_c ∧ N_c + R ≤ hi`,
    /// recomputed by the T-step evaluation of the completed kernel.
    Absorb,
    /// `qtsl_dabs_posterior_bracket` — `lo ≤ N_c/(S+R) ∧
    /// (N_c+R)/(S+R) ≤ hi`; refuses at `S = 0`.
    Posterior,
}

/// The angelic-selection family's dispatch kinds ([`crate::asel`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ASelKind {
    /// `qtsl_asel_reach` — the cited warrant's subject is the
    /// witness's system (identity + agreement; never re-proves reach).
    Reach,
    /// `qtsl_asel_cover` — the cells cover the warrant region, per
    /// mode (exact-ℚ slab decomposition).
    Cover,
    /// `qtsl_asel_enabled` — attachment before enabledness; the
    /// dom-in-active-region facet refuses (kernel-cite stratum).
    Enabled,
    /// `qtsl_asel_closed` — landing-in-warrant-region: an all-refuse
    /// fiber past the structural decode (kernel-cite stratum).
    Closed,
    /// `qtsl_asel_ratecap` — dwell cells: roster completeness bound,
    /// majorant sum · eps ≤ 1, strict demonic/forced floors.
    Ratecap,
    /// `qtsl_asel_relay` — relay cells: zero-discretionary-delay
    /// choice, only-instant facet; landing facet refuses.
    Relay,
    /// `qtsl_asel_attach` — at-most-one witness per mark, marks-list
    /// placement (floors decide false), subject agreement.
    Attach,
}
