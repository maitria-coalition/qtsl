# Lean developments

The machine-checked results behind the QTSL rule catalogue, the
certificate checkers, and the semantic universe. Nine Lake packages, one
shared toolchain (`leanprover/lean4:v4.32.0-rc1`), all pinned to the same
mathlib revision. The tree carries **zero `sorry`**: open questions are
recorded in module docstrings as stated successors, and design decisions
are witnessed by refutation theorems kept in the tree, not by prose.

## Packages

| package | library | depends on | contents |
|---|---|---|---|
| `qtsl/` | `Qtsl` | `qtsl-aux` | the certificate calculus and its checkers: hypernets, sequents, per-rule soundness, exact-rational and dyadic arithmetic kernels, grid geometry, the wire format, and the executable entry points |
| `qtsl-aux/` | `QtslAux` | `optional-sampling` | the analytic and probabilistic support strata: martingale arguments, composition kernels, the imprecise-probability stock, benchmark sweep rows |
| `su-functor/` | `SuFunctor` | `qtsl`, `qtsl-aux`, `double-cat` | **the semantic universe**: the penalty universe and its hyperspace presentation, the spec-class decoration functor and its totals, the graded judgment, and the adequacy squares |
| `double-cat/` | `DoubleCat` | — | pseudo and virtual double categories: lax/pseudo functors, Grothendieck totals, discrete double opfibrations, the wiring base |
| `optional-sampling/` | `OptionalSamplingRC` | — | self-contained continuous-time optional sampling for right-continuous nonnegative supermartingales, with the compensator and exponential-discount supermartingale constructions |
| `pointfree/` | `Pointfree` | — | the pointfree stochastics strand: valuations on frames, the cemetery promotion and its topology, the Borel bridge (τ-additivity as the exact hypothesis class), the classical subprobability carrier and measure-level dagger chart, and the ultrafilter escape witness |
| `checkers/reflection/` | `Reflection` | `qtsl` | the Lean reflection route: sealed geolog container bytes decoded, reconstructed, and elaborated into a kernel-accepted validity theorem (`Reflection.Accept`), with per-certificate kernel receipt modules and the route's executables |
| `checkers/qtslab-lean/` | `QtslabLean` | `checkers/reflection` | the program route: the reflection route's decode and check functions, unchanged, compiled to a native binary that prints the accepted sequent — Lean's code generator is in its trusted base (its README carries the exact trust statement) |
| `su-functor-legacy/` | `SuFunctorLegacy` | the live packages | the retired calculus-side semantic tier, archived buildable; **never imported by live code** (see its README) |

Dependency direction is strictly one-way, `su-functor` and the
`checkers/` packages downward; the legacy package sits outside the live
cone (it imports live modules, so live renames surface there as build
errors — by design).

## Orientation: where the semantic universe lives

The five-minute version, for someone about to build on the universe:

* **The total itself** — `SuFunctor.SingleSiteSemanticUniverse`:
  `dnfSpecFunctor` (the coupled-DNF spec decoration functor over the
  wiring base `DoubleCat.WireSpan`), `SingleSiteSemanticUniverse` (its plain
  double Grothendieck total), `singleSiteUniverseProj` (the strict
  projection), and `singleSiteUniverseProj_discreteOpfibration` (the
  projection is a discrete double opfibration). Systems enter as ideal
  points (`SuFunctor.Universe.IdealPoint`).
* **The universe strata** — `SuFunctor.Universe.*`: belief states and
  lsc penalty functionals (`Carrier`), the pointwise-order judgment
  (`Judgment`), closure under the calculus (`Closure`), the generation
  theorems (`Generation`, `Tents`), the hyperspace presentation
  (`VietorisStratum` and the `Fell*` family), and the coupled-DNF layer
  (`SpecDnf`, `CoupledJudgment`, `LocallyClosedLayer`).
* **The seam** — `SuFunctor.Plain.Seam`: `penEquiv`, the order
  isomorphism identifying the exact penalty stock over finite carriers
  with the semantic one, and `singleton_subset_iff_penEquiv_mem`, the
  judgment bridge across it.
* **The graded judgment and its target** — `SuFunctor.Judgment`
  (`seqValid`, `probGE`, `probLE`; composition is formal conjunction)
  and `SuFunctor.Target` (`Crd`, the thin single-object double category
  of per-element constraints on subprobability mass functions — the
  carrier on which adequacy squares are stated).
* **Sequent validity of the certificate calculus** — `Qtsl.Catalogue`:
  `Sequent.semanticallyValid` (truth in every admissible valuation of a
  hypernet); per-rule soundness in `Qtsl.Soundness` and its dynamical
  and structural companions (see the package guide below).
* **The adequacy squares** — `SuFunctor.Adequacy.*`: the shared
  inclusion library (`Inclusions`) and the landed instances (`Dtmc`,
  `Pgm`, `Mdp`, `MdpDemonic`, `DelayLine`, `Envelope`,
  `EnvelopeUnion`).
* **The proof calculus as a virtual double category** —
  `SuFunctor.Virtual` (multi-premise entailments as multicells), with
  `SuFunctor.VirtualComparison` and `SuFunctor.Plain.Comparison`
  relating the virtual and plain presentations.
* **Axiom receipts** — `SuFunctor.Probes.*Axioms` and each package's
  `AxiomReceipts` target: `#print axioms` outputs checked at build
  time, not documentation.

### Binding a new adequacy square

An adequacy square shows: *compile-then-denote agrees with
interpret-classically-then-include*. The working recipe, matching the
landed instances:

1. Read `SuFunctor.Adequacy.Inclusions` (the inclusion constructors and
   the invertible-globular-cell packaging), then one exemplar end to
   end — `Adequacy.Dtmc` for the precise face, `Adequacy.MdpDemonic`
   for the imprecise face.
2. State the classical object in its own textbook presentation, the
   compiled presentation at the appropriate system grain, and the
   denotation as a loose-arrow diagram of `Crd V`.
3. Keep the import cone tight: import the `Universe`/`Adequacy` modules
   you use, not the `SuFunctor` aggregator.
4. Add an axiom-receipt module under `SuFunctor/Probes/` (pattern:
   `<Name>Axioms.lean`), and an aggregator import in `SuFunctor.lean`.
5. Negative controls belong in the tree: refuting fixtures and
   load-bearing-hypothesis witnesses ride beside the theorem they
   guard (see `Universe/FellSeamWitness`, `StateSpace/Adjudication`).

A note on carriers: the admissible-valuation subtype (`AdmVal`)
currently lives only in the legacy package
(`SuFunctorLegacy.Functor`). The adequacy statements are
carrier-generic; tying a compiled system's record space to admissible
valuations over the wiring base is a stated successor and will need
that carrier restated over the live stack — do not import the legacy
package for it.

## Package guides

### qtsl — the certificate calculus and checkers

Flat module namespace, thematic groups:

* **contract and soundness spine**: `Catalogue` (the certificate
  contract: semantic model and rounding theory; `Hypernet`,
  `Sequent.semanticallyValid`), `Soundness` (per-rule), `Decide`
  (rule-applicability decidability), `QtslSoundness` (dynamical rules
  over semiflows), `TimedCore`, `LatticeInv`, `Tabular`, `Product`,
  `ProductLattice`, `ReluSplit`, `Switch`, `Composition` (small-gain),
  `Admissible` (context-carrying disjunction elimination), `Behavioral`
  (the behavioural floor), `Discharge`, `SoundnessDemo` (worked-example
  capstone).
* **exact arithmetic**: `QArith` (import seam), `QArithKernel`,
  `QArithCanon`, `QArithLemmas`, `ConvexRat`, `Dyadic`, `ERat`,
  `IEEE754` (bit-level refinement of the float model).
* **cone and geometry**: `ConeLemma`, `Farkas`, `PsdCert`,
  `GridGeometry`, `PolyGradient`, `PderivExpansion`, `PpolyExpansion`,
  `ReluExpansion`, `FacetExpansion`, `FacetRiding`, `Crossing`,
  `ChainMargin`, `ChainRecurrence`, `OrderAssembly`, `MeanValue`,
  `PoincareMiranda`, `EventualMember`, `StarIdentityDAG` (staged lemma
  graph; adversarial probes under `Probes/`).
* **dynamical profiles**: `DiniProfile`, `OdeProfile`, `RodeProfile`,
  `Reach`, `ReachContinuous`, `ChartPullback`, `Substitution`.
* **wire format**: `Wire` (binary parser), `WireSpec` (encoding
  relation), `WireCheck` (first-order checker), `WireDemo`/
  `WireDemoData` (end-to-end battery with negative-control mutants).
* **computational core** (`Core/`, mathlib-free so the emitted-C
  closure stays small and auditable): `Core.Catalogue`, `Core.Decide`,
  `Core.QArith`, `Core.Dyadic`, `Core.ERat`, `Core.Prim`,
  `Core.KernelReceipts` (kernel-side coverage receipts), `Core.Main`
  (the executable checker); `CoreBridge` ties core to mathlib.
* **harnesses**: `Comparator/` (compiled vs kernel vs interpreted
  paths, fixtures under `Comparator/Fixtures/`), `DiffHarness`
  (differential-testing leg), `Handshake/` (generated end-to-end
  certificates: cart-pole, composite small-gain/syzygy).

### qtsl-aux — analytic and probabilistic support

* **imprecise probability** (`Imprecise/`) — the credal stock the
  semantic universe builds on: `Credal` (finite credal sets,
  lower/upper expectations), `Compose`, `MarginalCompat`(`General`),
  `MarginalExtension`, `PenaltyCredalIso` (mass–direction
  decomposition), `PenaltyCoherence`, `CouplingGlue`, `Containment`
  and `ContainmentGeneral` (the composition law's containment in the
  glue, finite and general strata), `TowerWitness`
  (a Hurwicz tower-consistency refutation).
* **martingale toolkit**: `Ville`, `OptionalStopping`, `Excursions`,
  `QStreett`, `StreettDemonic`, `Deadline`, `FloorRenewal`,
  `CerfBound`.
* **composition kernels** (`QtslCompose/`): `AGCompose`(`Discrete`),
  `Flatten`(`Meas`), `SimTransport`(`Meas`), `Coherence`,
  `StochCoherence`, `AggReduce`, `Presentation`, `LtiSampled`,
  `WireCertDischarge`.
* **stochastic hybrid systems** (`LayerD/` and friends): `Skeleton`,
  `Streett`, `Until`, `Deadline`, `WZFreedom`, `DiniDischarge`,
  `PDMPDischarge`, `MPDischarge` (the martingale-problem profile:
  `MPFlow`, segment-Dynkin discharge, and the continuous-time
  battery soundness corollaries), `ItoInterface`/`ItoSampling`,
  `D3Faces`; `MaxFormPDMP`, `GaugeSmallGain`, `GshsFeedbackSum`,
  `AGCompose.GshsSeries`/`GshsParallel`.
* **analysis and geometry**: `BoxBern`, `Enclosure`, `Boundary`,
  `GridCx`, `ChartCover`, `Repar`/`ReparTame`, `Wasserstein/`
  (`Space`, `Coupling`, `Glue`, `Complete`), `PdeBridge`, `PdeFlow`,
  `PdeDini`, `PdeRungW`, `PdeUniqueness`.
* **logic and rewriting**: `NNFDuality`, `TemporalRewrite`,
  `Structural`, `Acceptance` (citation towers), `QtslAliases` (glue:
  rational certificate data to real semantics), `QtslBattery`,
  `Battery`.
* **Markov-chain quantitative layer**: `QRelChain`, `QDistTransport`,
  `QFixBall`, `QBeliefLowerBound`, `Pomdp`, `DefectBound`.
* **benchmark sweep** (`Sweep/`): shared infrastructure (`Sweep`,
  `Sweep.Discrete`, `Sweep.Uniform`, `Sweep.FaultyUniform`) and one
  module per benchmark row under `Sweep/Rows/`.

### su-functor — the semantic universe

* root: `SingleSiteSemanticUniverse` (the single-site total — start here), `Judgment`,
  `Target`, `Virtual`, `VirtualComparison`.
* `Universe/` — the penalty universe, in strata:
  * *core*: `Carrier`, `ProbCarrier`, `Judgment`, `Closure`,
    `Generation`, `TransposedGeneration`, `RadialGeneration`, `Tents`,
    `Riesz`, `Points`, `IdealPoint`, `Witnesses`, `ConvexChart`.
  * *the general carrier* (`General/`): `Carrier`, `Dictionary`,
    `Closedness` (compile closedness iff lsc, image characterization),
    `CheckerAnchor`, `CredalPoset`, `Richardson`, `Riesz` — the
    compile correspondence, atlas placements, and checker-anchor
    restriction over subprobability Borel measures on arbitrary
    carriers; plus `Marginalization` (inf-projection: escape witness,
    lsc-envelope reflector, tightness-certificate exactness) and
    `HullClosure` (closed binary hulls, levelwise coproduct
    exactness).
  * *hyperspace, compact stratum*: `VietorisStratum`,
    `VietorisDictionary`, `Hypograph`, `ImageChar`, `Sector`,
    `AtomMirrors`.
  * *hyperspace, noncompact stratum*: `FellTopology`, `FellRestrict`,
    `FellCapacity`, `FellDescent`, `FellDescentEqualizer`,
    `FellOnePoint`, `FellRecordLocus`, `FellRecordWitness`,
    `FellSeamWitness`.
  * *record lenses*: `RecordLens`, `RecordLensFell`,
    `RecordLensContinuum`.
  * *the coupled-DNF spec layer*: `SpecDnf`, `CoupledJudgment`,
    `LocallyClosedLayer`, `Fragments`, `DisjunctionElim`,
    `NablaDictionary`, `TransportCitizenship`, `ValuationUnit`.
  * *transport and composition*: `MeshCompositor`, `DemonicClock`,
    `SpacelikeSeam`.
* `Plain/` — the spec-class decoration tier: `SpecFunctor` (the lax
  double functor and its total `SpecTotal`), `Penalty` (exact penalty
  stock), `Seam` (the identification with `Universe.Carrier`),
  `Battery` (acceptance battery), `Comparison` (plain vs virtual);
  the general stratum: `MeasJoint` (subprobability Borel joints —
  pushforward, penalty transport, coherence cores, weak continuity,
  lsc closure and attainment, compactly-supported subclass),
  `GeneralFunctor` (the tight-tier functor `measSpecObj` with the
  transposed battery), `GeneralSeam` (the exact stock as a
  sub-instance, `Joint.toMeas`).
* `Site/` — the sheaf upgrade: `WindowPenalty`, `SiteFunctor`,
  `ClassDescent`, `MatchingFork` (a strict-sections refutation),
  `Battery`.
* `StateSpace/` — ω-semialgebraic state spaces: `Pieces`, `Maps`,
  `Category`, `Limits`, `CountableCoproducts`, `Citizens`,
  `Adjudication` (the separating counterexamples); the free countable
  coproduct completion: `FamCat`, `FamCoproducts`, `FamLimits`,
  `FamCompletion` (the completed state-space category, with the bag
  space as the coproduct of its sorted-cone sectors).
* `Adequacy/` — see the recipe above.
* `Probes/` — axiom-receipt modules, one per development.

### checkers — the Lean-route checkers

Two small packages, each with its own README carrying the full trust
statement and usage:

* `checkers/reflection/` — sealed geolog container bytes decoded
  (`Container`, `Body`, `Cells`, `Codec`), reconstructed
  (`CertRows`, `Vocab`), and elaborated (`Elab`, `Valid`) into a
  kernel-accepted validity theorem: `Reflection.Accept` states
  `acceptBytesSealed_sound` — an accepted claim's sequent is
  semantically valid (`Sequent.semanticallyValid`, from `Qtsl.Catalogue`).
  Decoder and reconstruction stages deliberately carry no correctness
  theorems of their own: a defect there loses completeness, never
  soundness. Timings and admission thresholds: `MEASUREMENTS.md`.
* `checkers/qtslab-lean/` — the same decode and check functions
  compiled to a native program (certificate file in, accepted sequent
  printed or nonzero-exit refusal). The positive control for the
  route's cost accounting: same logic, kernel removed.

### pointfree — the pointfree stochastics strand

* `Valuation/` — `Basic` (valuations on frames: strict, monotone,
  modular; Scott continuity as a mixin), `Topology` (the polarity
  package: evaluations lsc, mass usc, liveness walls closed),
  `Promotion` (the cemetery promotion, a homeomorphism onto the
  induced topology), `Bridge` (Borel measures restrict to
  valuations; Scott continuity is τ-additivity — Fremlin 414O as
  the exact hypothesis class), `BridgeContinuity`
  (`continuous_toSubProb`), `EscapeWitness` (the free-ultrafilter
  valuation: escaping mass with no points consulted).
* `Measure/` — `SubProbability` (the classical subprobability
  carrier under the narrow topology), `DaggerChart`
  (`daggerChartMeasure`, two-route compactness, metrizability).

### double-cat — the ambient double-category language

`Basic`, `Dbl`, `Sq`, `CellCategory`, `Companion`, `Span`, `WireSpan`
(the wiring base in state-family presentation), `DepSpan`, `CrossSite`,
`Grothendieck`/`GrothendieckMap` (plain totals), `Opfibration`
(discrete double opfibrations), `Functor/` (`Lax`, `Pseudo`,
`Composition`, `Whiskering`), `Transformation`, `Modification`,
`LooseBicategory`, `LooseTransformation`, `Monoidal/`, and `Virtual/`
(virtual double categories: `Functor`, `OfPseudo`, `Promote`,
`FreePromotion`, `Grothendieck`, `GrothendieckRestrict` — the
restriction correspondence, fully proven — and `Opfibration`).

## Building

Each package builds independently with Lake; path dependencies point at
sibling directories (the `checkers/` packages reach up one level, e.g.
`../../qtsl`), so keep the layout of this folder intact.

```
cd lean/qtsl
lake exe cache get   # optional: fetch the mathlib build cache
lake build           # the Qtsl library
lake build checker_core wire_check comparator diffharness wire_demo
```

The Lean-route checkers build the same way from their own directories:

```
cd lean/checkers/reflection
lake build                          # the Reflection library
lake build geolog_reflect geolog_read oracle_accept reflect_demo

cd ../qtslab-lean
lake build qtslab_lean              # the program-route binary
```

The reflection package's per-certificate kernel receipt modules
(`Reflection.Receipt*`) are deliberately outside the library root: each
one kernel-evaluates a whole acceptance run, at costs orders of
magnitude above every other module combined — build them by name, on
hardware sized for it (see `checkers/reflection/MEASUREMENTS.md`).

Memory expectations for full builds (peak resident set, measured on
warm dependency caches): `qtsl` ≈ 23 GiB, `qtsl-aux` ≈ 54 GiB,
`su-functor` ≈ 34 GiB,
`double-cat` ≈ 10 GiB. Plan machine placement accordingly; incremental
rebuilds of single modules are far lighter.

`AxiomReceipts` modules record the axiom closure of the principal
theorems (`#print axioms` outputs are part of the build, not
documentation): build them with `lake build AxiomReceipts` inside the
corresponding package. The `qtsl` package's kernel-side receipts live
at `Qtsl.Core.KernelReceipts`; `su-functor` additionally carries
per-development receipts under `SuFunctor/Probes/`.

## Relation to the book

The rule catalogue and the semantic-universe chapters cite these
developments by module name — e.g. `Qtsl.Soundness`,
`QtslAux.QtslCompose.AGCompose`, `SuFunctor.Universe.FellCapacity` —
and every mechanization badge resolves to a theorem in one of these
packages. **Module names are load-bearing citations**: renaming a
module requires patching every book and catalogue reference in the
same change.

## Conventions

* **Zero `sorry`.** Nothing lands with a `sorry`; a result that cannot
  yet be closed is stated as a successor in the docstring of the module
  that will consume it.
* **Refutations are kept.** When a design decision was forced by a
  counterexample, the counterexample stays in the tree as a theorem
  (`StateSpace.Adjudication`, `Universe.FellRecordWitness`,
  `Site.MatchingFork`, `Imprecise.TowerWitness`, the legacy `Refute`
  pins) — deleting them would delete the reasons.
* **Every module carries a module docstring** stating what it proves
  and where it sits. Claims about *another* module's open legs go
  stale; prefer pointing at the module and letting its own docstring
  speak.
* **Import discipline.** Live code never imports `su-functor-legacy`.
  Within `su-functor`, prefer the precise import cone to the
  aggregator. Aggregator files (`Qtsl.lean`, `QtslAux.lean`,
  `SuFunctor.lean`) list every library module of their package: a new
  module is added there (and to a receipts surface) in the same change
  that creates it.
