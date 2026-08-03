//! qtsl-geolog-provider — the QTSL application's ground provider for
//! the geolog engine.
//!
//! ## What this crate is
//!
//! geolog-alpha is an application-agnostic engine: theories are data,
//! tables are entailed, and the one sanctioned place an application
//! contributes *code* is the ground-provider plugin seam
//! (`geolog-ground-api`). This crate is QTSL's value at that seam: the
//! exact-rational evaluators for the QTSL certificate side-condition
//! relations, packaged as one [`GroundProvider`] the engine's binder
//! adjudicates like any other.
//!
//! The claimed roster (121 relations —
//! [`provider::ENTRY_COUNT`] is the computed authority, and this
//! headline count has grown family by family as evaluator groups
//! joined; the seam fixture stages 99 of the 121 — all
//! `Scope::Snapshot`: every one
//! is a row-context check over certificate rows):
//!
//! - **applicability** ([`blapplic`], 16 relations): exact-rational
//!   linear-combination replay, the PSD certificate witness/conclusion
//!   checks, wire-size positivity, polynomial canonical forms, premise
//!   containment, conclusion-form selection, closed exact evaluation;
//! - **atomic-compare** ([`atomic`], 2 relations): pinned
//!   syntactic-shape checks over Formula/Term rows;
//! - **recompute kits** (4 relations): the Morse discharge readout
//!   ([`morse`]), the Poincaré–Miranda battery walk ([`miranda`]), the
//!   stochastic-wire shape receipt ([`stochwire`]), and the Bag
//!   canonical-multiset receipt ([`bagcanon`]);
//! - **masks** ([`blmask`], 6 relations): bounded sweeps over the
//!   sealed finite membership data of Simplex/ExtensionSet rows
//!   (member equality, face-minus, intersection, omission, emptiness);
//! - **system-spec** (4 relations): the Poly canonical-form receipt
//!   ([`polycanon`]), the composite well-posedness pair —
//!   instantaneous-dependency causality and W3 simultaneity
//!   resolution — and the QFlatEq flatten discharge's v1 fiber
//!   (`qtsl_flatten`: the reflexive SysMech face decided, the
//!   composite fiber a loud deferral until its SwitchEdge/product
//!   row vocabulary stages) ([`syswire`]);
//! - **ProbLog brackets** ([`problog`], 8 relations): the
//!   certified query-probability bracket obligations over ground
//!   definite programs — well-formedness, explanation-row saturation
//!   (`derives`), cut-row saturation (`blocks`), exact enumeration,
//!   the two event-algebra bracket arithmetics (`lower`/`upper`), the
//!   even-depth inclusion–exclusion prefix (`bonferroni`), and the
//!   compiled decision-term judgment (`compiled` — exact beyond
//!   enumeration, claimed only when the decision-term vocabulary is
//!   declared);
//! - **conclusion forms** ([`blconclform`], 6 relations): the
//!   barycentric-halfspace conjunction (`barycentricHalfspaceForm`),
//!   recomputed from the simplex's vertex table over the barycentric
//!   substrate ([`barycoord`]) and compared structurally against the
//!   formula's rows; the four cell-schema forms
//!   (`cellStrictInteriorForm`, `cellOneHotForm`, `cellOutWitnessForm`,
//!   `cellOutZeroForm`) over the destructured cell application; and
//!   the LiRPA relaxation conclusion (`lirpaConclusionForm`), a pure
//!   shape equality with the Lean `affineWireTerm` build;
//! - **block lattices** ([`bllattice`], 2 relations): the
//!   certificate-family obligations — `blockLatticeWF` (record
//!   well-formedness: index families, gridlines, cell sets, canonical
//!   boundary-facet counts) and `productLatticeChecks` (facet
//!   discharge by citation, drift confinement, wire disjointness,
//!   composite-equals-product);
//! - **enclosures** ([`enclosure`], 1 relation): the remainder-bound
//!   witness check (`enclosureWitnessValid`) — exact Maclaurin prefix
//!   recompute, the strict radius guard, and the geometric tail cap,
//!   decided in exact rational arithmetic by cross-multiplication;
//! - **carillon discharge plans** ([`carillon`], 4 relations): the
//!   grid/region/manifest recomputes — `qtsl_cell_cover`,
//!   `qtsl_dbar_closure`, `qtsl_gap_a`, `qtsl_lowbound_boxes` — exact-Q
//!   and division-free;
//! - **Formula/Term surgery** ([`blsurgery`], 4 relations): the
//!   proof-theory context machinery — `conjunctAt`/`conjReplace`
//!   (∧-tree path walks over `CtxPath` rows) and
//!   `substituteInFormula`/`applyPredicateToTerm` (parallel structural
//!   descent of input against claimed output);
//! - **promise interface confinement** ([`blpromise`], 2 relations):
//!   the `PPromise` wire obligations — `promiseContractConfined`
//!   (contract free wires within the declared interface) and
//!   `promiseWiresSeparated` (supplier-premise wires shared with the
//!   RECOMPUTED context or the conclusion confined to the interface);
//! - **predicate semantic classes** ([`blpredclass`], 3 relations):
//!   the closed-world classification of a predicate formula's
//!   satisfying set — `isConicPredicate`, `isConvexPredicate`,
//!   `isUpwardClosedConicPredicate`, all three verdicts read off one
//!   total fragment recognizer (rays over the designated hole,
//!   positive literal scalings, `= 0` kernels, and conjunctions);
//!   outside-fragment shapes decide false (the recognizer is part of
//!   the spec), and only unresolvable rows refuse;
//! - **Bernstein cones** ([`berncone`], 3 relations): the region
//!   calculus's heavy recomputes —
//!   `allForwardDiffBernCoeffsSatisfyP` (the exact-rational Bernstein
//!   forward-difference coefficient sweep over the barycentric
//!   parametrization, degree-lie rejecting, recomputed from the
//!   vertex table), `coverInfeasibilityValid` (the subdivision
//!   rule's 1-D interval cover, recomputed from the branch regions),
//!   and `allForwardDiffBernIntvEnclosuresSatisfyP` (the float lane:
//!   the same grid recomputed in validated dtype-interval arithmetic
//!   over the [`fpintv`] substrate — the Lean `FloatFmt` rounding
//!   maps transcribed exactly — with P checked at the interval lower
//!   endpoints and the false verdict gated on the certified
//!   upward-closed classification);
//! - **the MarkFlow walk** ([`markflow`], 1 relation): the
//!   `QWireComposeMarks` node's two-column recompute
//!   (`qtsl_wire_markflow`) — stage-label difference constraints on
//!   the instant fragment plus zero-lag-cycle carve coverage (SCC
//!   pass, containment/carved-delivery pairing arithmetic, one
//!   species-tagged diagonal per cycle), the ∃-dual of the causality
//!   walk; the unminted species row conventions ride a loud v1
//!   refusal register, never silence;
//! - **the causality walk** ([`wirecausality`], 1 relation): the
//!   `QWireCompose` node's declared-rank recompute
//!   (`qtsl_wire_causality`) — one rank per component, strict
//!   increase along every directed wire of the cited certificate's
//!   wiring (no cyclic wiring can pass), the ∀-face sibling the
//!   MarkFlow walk is the ∃-dual of; fully decided in the landed
//!   vocabulary — no unminted content, no store;
//! - **deadline tables** ([`deadline`], 1 relation): the
//!   exact finite-horizon deadline-table walk
//!   (`qtsl_deadline_table`) — from the node's closure alone (the
//!   Dtmc kernel + policy mechs through `QSat/sys`, absorbing
//!   self-loops re-synthesized from marks; the reach spec formers
//!   through `QSat/spec`; the flat `(T+1) × ns` table), recomputing
//!   the certified-gym exact-lane checker's WF/B/S/C obligations
//!   verbatim in exact ℚ;
//! - **the carved-window pair** ([`dwellgate`] + [`ratecap`], 2
//!   relations): `qtsl_dwell_gate` — gate-inside-window
//!   over the cited duration gate (store-seam: cell-free unary
//!   rational nets folded to one univariate polynomial; containment
//!   by exact tail certificates, nonemptiness by witness search +
//!   Bernstein emptiness) — and `qtsl_tr_ratecap` — rate ≤ majorant
//!   on the derived active region (constants exact, whole-space
//!   certificates, exact grid witnesses; all-stay mixes hold
//!   vacuously with the vacuity register-named). Both are
//!   evaluator-computed side-conditions with no citation spine — the
//!   massone tier, never a certificate checker.
//! - **absorption brackets** ([`dabs`], 3 relations): the DtmcAbsorb
//!   species' side-conditions over the chain species' stored rows —
//!   `qtsl_dabs_wf` (labeled states stored-absorbing) and the
//!   `qtsl_dabs_absorb_bracket` / `qtsl_dabs_posterior_bracket` pair,
//!   recomputed by the exact-ℚ T-step evaluation of the completed
//!   kernel (staged-fragment vocabulary: resolves only against
//!   closures carrying `DAbsQuery`).
//!
//! Each evaluator mirrors a definition in the repository's Lean
//! development (`lean/`, the `Qtsl` packages) — the spec authority —
//! and recomputes the certificate's claims rather than trusting them:
//! a decided mismatch is a `false` verdict, and anything the row
//! context cannot decide REFUSES with a reason, never guessing (the
//! seam's refusal law).
//!
//! Supporting library surfaces: the certificate admission chase
//! ([`admission`]), grid-complex validation ([`gridcx`]), batch
//! verification kernels ([`blbatch`], [`blcsr`], [`blcolx`],
//! [`blpin`]), the shared Formula/Term row-walk substrate
//! ([`formrows`]), and the exact-rational substrate ([`qq`],
//! [`qpoly`]).
//!
//! ## Trust statement
//!
//! Everything here is untrusted producer-side tooling in the maitria
//! architecture's sense: strong claims are discharged by certificates
//! that independent checkers re-derive. A wrong evaluation in this
//! crate yields a certificate that fails checking — never a false
//! verdict in the trusted path. Do not promote this crate into any
//! trusted computing base.
//!
//! ## Using it
//!
//! ```no_run
//! use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};
//!
//! // Declaration indices come from the engine's theory loaders (or
//! // are constructed directly — declarations are plain data).
//! let indices = vec![];
//! let vocab = QtslVocab::build(&indices);
//! let provider = QtslGroundProvider::new(vec![/* semantics revs */], vocab);
//! // Engine::builder().provider(&core_floor).provider(&provider)…
//! ```
//!
//! A family group whose vocabulary does not resolve against the loaded
//! revisions is simply not claimed (the reasons are recorded on
//! [`QtslVocab::notes`]); the binder then defers those declarations —
//! declared-but-unbound, safe-fail. Verdicts never change with what
//! happens to be linked or loaded.
//!
//! [`GroundProvider`]: geolog_ground_api::GroundProvider

#![forbid(unsafe_code)]

pub mod admission;
pub mod asel;
pub mod atomic;
pub mod avgbattery;
pub mod bagcanon;
pub mod barycoord;
pub mod bernbox;
pub mod berncone;
pub mod blapplic;
pub mod blbatch;
pub mod blcolx;
pub mod blconclform;
pub mod blcsr;
pub mod bllattice;
pub mod blmask;
pub mod blpin;
pub mod blpredclass;
pub mod blpromise;
pub mod blsurgery;
pub mod carillon;
pub mod circuit;
pub mod constfold;
pub mod container;
pub mod contract;
pub mod dabs;
pub mod deadline;
pub mod dwellgate;
pub mod enclosure;
pub mod error;
pub mod formrows;
pub mod fpintv;
pub mod gridcx;
pub mod guard;
pub mod gymeproc;
pub mod gymrw;
pub mod hole;
pub mod hplate;
pub mod markflow;
pub mod miranda;
pub mod morse;
pub mod nnform;
pub mod polycanon;
pub mod problog;
pub mod provider;
pub mod qpoly;
pub mod qq;
pub mod ratecap;
pub mod reprovocab;
mod roster;
pub mod rowctx;
pub mod spdemoment;
pub mod stochwire;
pub mod store;
pub mod swret;
pub mod syswire;
pub mod theory;
pub mod trwf;
pub mod wirecausality;

pub use error::EvalError;
pub use provider::{QtslGroundProvider, QtslVocab};
pub use rowctx::{AttrRow, CertRows, CtorRow, RelRow};
pub use store::{DirStore, MemStore, StoreResolver};
pub use theory::{Chid, DomainSig, FunDecl, Ground, SortKey, TheoryIndex};
