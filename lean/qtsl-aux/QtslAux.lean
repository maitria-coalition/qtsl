import QtslAux.Dyadic
import QtslAux.Ville
import QtslAux.Boundary
import QtslAux.Deadline
import QtslAux.DefectBound
import QtslAux.Enclosure
import QtslAux.Battery
import QtslAux.StochInvDecomp
import QtslAux.OptionalStopping
import QtslAux.AGCompose.GshsSeries
import QtslAux.AGCompose.GshsParallel
import QtslAux.GshsFeedbackSum
import QtslAux.GaugeSmallGain
import QtslAux.FloorRenewal
import QtslAux.Excursions
import QtslAux.Imprecise
import QtslAux.LeakAware
import QtslAux.DiamondSite
import QtslAux.DiamondTopology
import QtslAux.ChronologyInterior
import QtslAux.OpenQuantum
import QtslAux.QuantumRecords
import QtslAux.QuantumApproxConsistency
import QtslAux.QuantumDescent
import QtslAux.QuantumCovariance
import QtslAux.QuantumStates
import QtslAux.QuantumDeterminacy
import QtslAux.QuantumOuterStorey
import QtslAux.QuantumAssembly
import QtslAux.QuantumFunctoriality
import QtslAux.QuantumEmbedding
import QtslAux.QuantumExtension
import QtslAux.QuantumSheaf
import QtslAux.QuantumStack
import QtslAux.QuantumStackNecessity
import QtslAux.QuantumStackSufficiency
import QtslAux.QuantumStackVonNeumann
import QtslAux.QuantumStackConnectivity
import QtslAux.QuantumStackNormality
import QtslAux.QuantumStackScalars
import QtslAux.QuantumStackImplementer
import QtslAux.QuantumStackHolonomy
import QtslAux.LayerD
import QtslAux.LayerD.PDMPDischarge
import QtslAux.LayerD.DiniDischarge
import QtslAux.LayerD.Skeleton
import QtslAux.LayerD.D3Faces
import QtslAux.LayerD.WZFreedom
import QtslAux.LayerD.Deadline
import QtslAux.LayerD.Until
import QtslAux.LayerD.ItoInterface
import QtslAux.LayerD.ItoSampling
import QtslAux.LayerD.MPDischarge
import QtslAux.LayerD.Streett
import QtslAux.MaxFormPDMP
import QtslAux.NNFDuality
import QtslAux.SdeGenerator
import QtslAux.SdeGeneratorPoly
import QtslAux.SdeMartingaleProblem
import QtslAux.JumpDiffusion
import QtslAux.JumpDiffusionMartingaleProblem
import QtslAux.PdeBridge
import QtslAux.Pomdp
import QtslAux.GridCx
import QtslAux.Repar
import QtslAux.BoxBern
import QtslAux.ReparTame
import QtslAux.ChartCover
import QtslAux.QRelChain
import QtslAux.QFixBall
import QtslAux.QBeliefLowerBound
import QtslAux.QDistTransport
import QtslAux.QStreett
import QtslAux.QtslAliases
import QtslAux.QGuard
import QtslAux.QtslBattery
import QtslAux.QtslCompose
import QtslAux.StreettDemonic
import QtslAux.TemporalRewrite
import QtslAux.Structural
import QtslAux.Sweep
import QtslAux.Acceptance
import QtslAux.Wasserstein
import QtslAux.QuantumDForm
import QtslAux.QuantumConverse
import QtslAux.QuantumHierarchy
import QtslAux.QuantumCompleteness
import QtslAux.QuantumConsistentSets
import QtslAux.QuantumApproxCap
import QtslAux.QuantumProfligacy
import QtslAux.QuantumApproxExactInstance
import QtslAux.QuantumTransport
import QtslAux.QuantumCoarseGraining
import QtslAux.QuantumDiamondMeasure
import QtslAux.QuantumTower
import QtslAux.QuantumStrictness
import QtslAux.QuantumAlignment
import QtslAux.QuantumSpectrum
import QtslAux.BagLift
import QtslAux.BagLiftFixture
import QtslAux.BagLiftMultiplicity
import QtslAux.KilledTimeIndexed

/-! # Bernstein Logic auxiliary library

Supporting formalization for QTSL (Quantitative Temporal Specification
Logic) certificate checking: the theorems here make certified quantitative
bounds on stochastic and hybrid dynamical systems into Lean-checked
consequences of their certificates. Overview, by cluster:

- **Dyadic arithmetic** (`Dyadic`, `DyadicCore`): dyadic rationals with
  directed rounding, the exact number representation used by certificates.
- **Martingale engine** (`Ville`, `OptionalStopping`, `Excursions`,
  `FloorRenewal`, `Deadline`): Ville's inequality for nonnegative
  supermartingales, reach-avoid and excursion bounds, and the geometric
  supermartingale deadline kernel.
- **Certificate batteries** (`Battery`, `QtslBattery`): soundness theorems
  (`sound_QSafetyBattery`, `sound_QDeadline`, `sound_QUnionBound`,
  `sound_QUntilBattery`, …) for discrete-profile certificate batteries over
  the Ionescu–Tulcea trajectory kernel.
- **Killed time-indexed reads** (`KilledTimeIndexed`): the killed
  trajectory measure of a jump chain with independent holding times, the
  fixed-horizon transient read, its mass dichotomy against clock
  exhaustion, the factorization of timed prefix marginals through
  skeleton prefix laws and holding data, and the resulting comparison —
  equal skeleton prefix laws and equal holding families give equal
  killed time-indexed reads at every horizon (exit-rate exponential
  holding kernels as the closing instance).
- **Composition** (`QtslCompose/*`, `AGCompose/*`, `GshsFeedbackSum`,
  `GaugeSmallGain`): assume-guarantee composition of certified components —
  series, parallel, and feedback forms, presentation compilation,
  simulation transport, and the gauge small-gain calculus.
- **Hybrid-system execution layer** (`LayerD/*`, `MaxFormPDMP`): the
  segment/skeleton execution model for general stochastic hybrid systems
  (GSHS), Dynkin-formula discharges for PDMPs (via the explicit first-jump
  measure and via Dini derivatives), the Itô/diffusion interface with
  optional-sampling discharge, until and Streett batteries, and deadline
  tail bounds.
- **SDE profiles and the martingale problem** (`SdeGenerator`,
  `SdeGeneratorPoly`, `SdeMartingaleProblem`, `JumpDiffusion`): the SDE
  profile's extended generator with derived covariance, the Dynkin class
  through which certified generator rows become Ville/deadline
  probability bounds, the exact-rational computed generator with its
  evaluation splice, the stopped martingale problem — the community's
  solution semantics — whose solutions discharge the Dynkin class field
  as a theorem, closing the loop end-to-end for compiled polynomial
  certificates, and the multi-leg jump-diffusion generator (finitely
  many jump legs, sub-stochastic mixture resets, killing) at which the
  evaluation splice holds with no side conditions and the martingale
  problem, its Dynkin discharge, and the verdict headlines transplant
  verbatim (`JumpDiffusionMartingaleProblem`) — so the compiled avoid
  verdicts hold for every presentation, fence-free.
- **Imprecise probability** (`Imprecise/*`, `LeakAware`): credal
  composition, marginal compatibility and extension, coupling glue, tower
  witnesses, coherent lower previsions with the finite envelope theorem
  and natural extension, composition-law containment with its crisp locus
  and strict witness, the feasibility (properness) equivalence at both
  strata, and the leak-aware safe-side bound for submass models.
- **Sites and generalization columns** (`DiamondSite`, `OpenQuantum`):
  interior-coverage well-behavedness for causal-diamond sites at
  bicontinuous-poset generality with clock-map functoriality, and the
  bounded-generator fence transport theorem for open quantum systems.
- **PDE bridge** (`Pde*`): bridge lemmas connecting certificate vocabulary
  to PDE facts — flows, Dini derivatives, uniqueness, and spectral
  (Wirtinger-type) inequalities.
- **Reparameterization** (`Repar`, `ReparTame`, `ChartCover`, `GridCx`,
  `BoxBern`, `CerfBound`, `Enclosure`, `DefectBound`): soundness of
  polynomial reparameterizations, chart covers of semialgebraic regions,
  Bernstein-form enclosures on boxes, and remainder bounds for
  transcendental enclosures.
- **Quantitative operators** (`QStreett`, `QFixBall`, `QBeliefLowerBound`,
  `QDistTransport`, `QRelChain`, `StreettDemonic`, `Pomdp`): Streett
  acceptance conditions, fixpoint balls in Wasserstein space, belief lower
  bounds for partially observed models, distribution transport, and
  relational (two-trace) chain soundness.
- **Structural rules** (`Structural`, `NNFDuality`, `TemporalRewrite`,
  `QtslAliases`, `Acceptance`, `Boundary`): discharge of QTSL structural
  proof rules, negation-normal-form duality, temporal rewriting, alias
  lemmas, and the citation-tower induction underlying certificate
  acceptance.
- **Wasserstein space** (`Wasserstein/*`): couplings, the triangle
  inequality, and completeness for the 2-Wasserstein distance.
- **Benchmark rows** (`Sweep/*`): per-benchmark theorems making each
  certified bound of the accompanying benchmark suite a Lean-checked
  consequence of its certificate battery.

The separate `AxiomReceipts` build target re-checks the axiom closure of
the principal theorems. The package depends on mathlib and on the sibling
`optional-sampling-rc` package (continuous-time optional sampling for
right-continuous nonnegative supermartingales).
-/

