import SuFunctor.Judgment
import SuFunctor.Target
import SuFunctor.Universe.Carrier
import SuFunctor.Universe.ProbCarrier
import SuFunctor.Universe.Riesz
import SuFunctor.Universe.CoupledJudgment
import SuFunctor.Universe.Generation
import SuFunctor.Universe.Points
import SuFunctor.Universe.Fragments
import SuFunctor.Universe.VietorisDictionary
import SuFunctor.Universe.VietorisStratum
import SuFunctor.Universe.ImageChar
import SuFunctor.Universe.IdealPoint
import SuFunctor.Universe.Sector
import SuFunctor.Universe.Hypograph
import SuFunctor.Universe.TransposedGeneration
import SuFunctor.Universe.AtomMirrors
import SuFunctor.Universe.RadialGeneration
import SuFunctor.Universe.RecordLens
import SuFunctor.Universe.RecordLensContinuum
import SuFunctor.Universe.FellTopology
import SuFunctor.Universe.FellRestrict
import SuFunctor.Universe.FellOnePoint
import SuFunctor.Universe.FellSeamWitness
import SuFunctor.Universe.FellDescent
import SuFunctor.Universe.FellDescentEqualizer
import SuFunctor.Universe.FellCapacity
import SuFunctor.Universe.FellRecordLocus
import SuFunctor.Universe.FellRecordWitness
import SuFunctor.Universe.FellPairLocus
import SuFunctor.Universe.FellPairWitness
import SuFunctor.Universe.RecordLensFell
import SuFunctor.Universe.Closure
import SuFunctor.Universe.Judgment
import SuFunctor.Universe.ConvexChart
import SuFunctor.Universe.Witnesses
import SuFunctor.Universe.Tents
import SuFunctor.Universe.LocallyClosedLayer
import SuFunctor.Universe.NablaDictionary
import SuFunctor.Universe.DisjunctionElim
import SuFunctor.Universe.TransportCitizenship
import SuFunctor.Universe.TopologicalCitizenship
import SuFunctor.Universe.TotalCitizenship
import SuFunctor.Universe.SpecDnf
import SuFunctor.Universe.SpecElab
import SuFunctor.Universe.PairSequent
import SuFunctor.Universe.ReachAvoid
import SuFunctor.Universe.ValuationUnit
import SuFunctor.Universe.DemonicClock
import SuFunctor.Universe.MeshCompositor
import SuFunctor.Universe.SpacelikeSeam
import SuFunctor.Universe.StochasticWitnesses
import SuFunctor.Universe.ThinningAbsorption
import SuFunctor.Universe.DemonicPortCitizenship
import SuFunctor.Universe.HausdorffKL
import SuFunctor.Universe.EpistemicStates
import SuFunctor.Universe.Marginalization
import SuFunctor.Universe.HideFrobenius
import SuFunctor.Universe.HullClosure
import SuFunctor.Site.WindowPenalty
import SuFunctor.StateSpace.Pieces
import SuFunctor.StateSpace.Maps
import SuFunctor.StateSpace.Category
import SuFunctor.StateSpace.Limits
import SuFunctor.StateSpace.CountableCoproducts
import SuFunctor.StateSpace.Citizens
import SuFunctor.StateSpace.FamCat
import SuFunctor.StateSpace.FamCoproducts
import SuFunctor.StateSpace.FamLimits
import SuFunctor.StateSpace.FamCompletion
import SuFunctor.StateSpace.DenotationRealize
import SuFunctor.Site.SiteFunctor
import SuFunctor.Site.TemporalTypeTheory
import SuFunctor.Site.WavyCoverage
import SuFunctor.Site.CausalConcordance
import SuFunctor.Site.BehaviorSpec
import SuFunctor.Site.ClassDescent
import SuFunctor.Site.Battery
import SuFunctor.Site.MatchingFork
import SuFunctor.Plain.Penalty
import SuFunctor.Plain.SpecFunctor
import SuFunctor.Plain.Battery
import SuFunctor.Plain.Comparison
import SuFunctor.Plain.CheckerFace
import SuFunctor.Plain.MeasJoint
import SuFunctor.Plain.GeneralFunctor
import SuFunctor.Plain.GeneralSeam
import SuFunctor.Plain.SeamDensity
import SuFunctor.Plain.SeamDensityCore
import SuFunctor.Site.GeneralWindow
import SuFunctor.SingleSiteSemanticUniverse
import SuFunctor.Universe.CertificateLayer
import SuFunctor.Spacetime.Base
import SuFunctor.Spacetime.Universe
import SuFunctor.Spacetime.Walls
import SuFunctor.HypernetInclusion
import SuFunctor.HypernetComposition
import SuFunctor.HypernetDouble
import SuFunctor.HypernetWf
import SuFunctor.HypernetElaboration
import SuFunctor.Stochastic.NoiseSemantics
import SuFunctor.Stochastic.NoiseKleisli
import SuFunctor.Stochastic.JumpMeasure
import SuFunctor.Stochastic.JumpAlgebra
import SuFunctor.Stochastic.JumpDiffusionThinning
import SuFunctor.WiringModes
import SuFunctor.BagFormer
import SuFunctor.TokenArcs
import SuFunctor.TokenGame
import SuFunctor.Virtual
import SuFunctor.VirtualComparison
import SuFunctor.Adequacy.Inclusions
import SuFunctor.Adequacy.HybridTime
import SuFunctor.Adequacy.Dtmc
import SuFunctor.Adequacy.Pgm
import SuFunctor.Adequacy.Envelope
import SuFunctor.Adequacy.Mdp
import SuFunctor.Adequacy.CtmcJumpChain
import SuFunctor.Adequacy.MarkovAutomaton
import SuFunctor.Adequacy.EnvelopeUnion
import SuFunctor.Adequacy.MdpDemonic
import SuFunctor.Adequacy.MaDemonic
import SuFunctor.Adequacy.PetriVanilla
import SuFunctor.Adequacy.StochasticPetri
import SuFunctor.Adequacy.StochasticPetriCascade
import SuFunctor.Adequacy.StochasticPetriColoured
import SuFunctor.Adequacy.StochasticPetriColouredCascade
import SuFunctor.Adequacy.StochasticPetriColouredDemonic
import SuFunctor.Adequacy.StochasticPetriDemonic
import SuFunctor.Adequacy.StochasticPetriSetFiring
import SuFunctor.Adequacy.StochasticPetriFlatten
import SuFunctor.Adequacy.StochasticPetriAngelic
import SuFunctor.Adequacy.StochasticPetriComposed
import SuFunctor.Adequacy.StochasticPetriFlattenAgreement
import SuFunctor.Adequacy.StochasticPetriColouredComposed
import SuFunctor.Adequacy.StochasticPetriColouredDirected
import SuFunctor.Adequacy.StochasticPetriSupervise
import SuFunctor.Adequacy.StochasticPetriSuperviseDemonic
import SuFunctor.Adequacy.DelayLine
import SuFunctor.Adequacy.Bag
import SuFunctor.Adequacy.SemanticUniverseWiring
import SuFunctor.Adequacy.BagWiring
import SuFunctor.Adequacy.ProbProg
import SuFunctor.Adequacy.Ode
import SuFunctor.Adequacy.Rode
import SuFunctor.Adequacy.MarginalGlue
import SuFunctor.Adequacy.Funnel
import SuFunctor.Universe.RadialUniverse
import SuFunctor.Universe.ParabolicOrder
import SuFunctor.Adequacy.HeatTorus
import SuFunctor.Adequacy.HeatTorusInit
import SuFunctor.Adequacy.SolutionSetMesh
import SuFunctor.Adequacy.Pde
import SuFunctor.Adequacy.PdeRows
import SuFunctor.Adequacy.CheckerCarrier
import SuFunctor.Adequacy.CheckerAcceptance
import SuFunctor.Adequacy.RecordSpace
import SuFunctor.Adequacy.DtmcGenerator
import SuFunctor.Adequacy.DtmcAbsorb
import SuFunctor.Adequacy.DtmcAliveTail
import SuFunctor.Adequacy.DtmcContraction
import SuFunctor.Adequacy.DtmcTemplate
import SuFunctor.Adequacy.DtmcProductProfile
import SuFunctor.Adequacy.SpecBehavioral
import SuFunctor.Adequacy.SpecPathLens
import SuFunctor.Adequacy.SpecStreettFormers
import SuFunctor.Adequacy.QuantumNet
import SuFunctor.Adequacy.QuantumContainment
import SuFunctor.Adequacy.QuantumCompression
import SuFunctor.Universe.SpecRewrite
import SuFunctor.Decapodes.Schema
import SuFunctor.Decapodes.Lowering
import SuFunctor.Decapodes.HeatCycle
import SuFunctor.SpatialPlates.Body
import SuFunctor.SpatialPlates.StokesRows
import SuFunctor.SpatialPlates.MeshLowering
import SuFunctor.SpatialPlates.WaveAction
import SuFunctor.Universe.General.EnvelopeCoherent
import SuFunctor.Universe.General.SmoothRepresentation
import SuFunctor.Universe.General.EnvelopeIdentification
import SuFunctor.Universe.General.EnvelopeWitness
import SuFunctor.Site.Tangency
import SuFunctor.Site.TangencyFam
import SuFunctor.Site.TangencyJet
import SuFunctor.Site.TangencyJetTie
import SuFunctor.QtslSem.BLComponents
import SuFunctor.QtslSem.Fixture
import SuFunctor.QtslSem.SpecJudg
import SuFunctor.QtslSem.BLFactoring
import SuFunctor.QtslSem.BLMulti
import SuFunctor.QtslSem.AliasSmallGain
import SuFunctor.QtslSem.AliasStructural
import SuFunctor.QtslSem.AliasPathSugar
import SuFunctor.QtslSem.AliasStreettDegenerate
import SuFunctor.QtslSem.AliasLatticeInv
import SuFunctor.QtslSem.AliasTaylorRootEval
import SuFunctor.QtslSem.Decode.Pins
import SuFunctor.QtslSem.Decode.Rows
import SuFunctor.QtslSem.Decode.Ground
import SuFunctor.QtslSem.Decode.Present
import SuFunctor.QtslSem.Decode.Binding
import SuFunctor.QtslSem.Decode.Fixture
import SuFunctor.QtslSem.Decode.BLMultiSeam
import SuFunctor.QtslSem.Decode.Acceptance
import SuFunctor.QtslSem.Decode.AliasAcceptance
import SuFunctor.QtslSem.Decode.CoverageProbes
import SuFunctor.QtslSem.Decode.Warrant
import SuFunctor.QtslSem.Decode.WarrantDeep
import SuFunctor.QtslSem.Decode.ReceiptWarrantUnit
import SuFunctor.QtslSem.Decode.RowShapeProbes

/-! # The semantic universe

This package constructs the semantic universe of the specification
logic: the lower-semicontinuous penalty universe over subprobability
carriers with its judgment, chart, and generation strata
(`SuFunctor.Universe`); the hyperspace presentation of spec classes as
locally closed crescents, through the Vietoris and Fell topologies with
their descent, collapse, and capacity theorems; the composition tier —
the spec-class decoration functor over the interfaces-and-wirings base
(`SuFunctor.Plain`) and its sheaf upgrade, where the temporal site
enters through the decoration (`SuFunctor.Site`); the judgment syntax
of the certificate calculus and its virtual presentation
(`SuFunctor.Judgment`, `SuFunctor.Virtual`); and the adequacy squares
tying classical semantic objects to the credal stratum
(`SuFunctor.Adequacy`).

A front-end tier (`SuFunctor.Decapodes`) mechanizes the discrete tier
of the Decapodes diagrammatic-PDE language: the Decapode schema as
data (a typed directed hypergraph over a monoidal signature, stored
as a relational instance), discrete interpretations into cochain
spaces with polynomial operator maps, and the lowering-adequacy
theorem — a discretized Decapode's solution set is exactly the graph
of its polynomial drift rows, the ODE model class's premise shape —
with a worked heat-on-the-torus receipt on the uniform cyclic mesh
(verbatim second-difference stencil, exact summation-by-parts
dissipation, presentation invariance).

An earlier semantic tier — double functors from the proof calculus
into per-element constraints on subprobability mass functions — is
retired and archived, buildable, in the sibling package
`su-functor-legacy`; see the retirement note at the end of the module
map.

Module map:

* `SuFunctor.Judgment` — the graded judgment syntax; composition as
  formal conjunction (loose arrows are finite lists of judgments,
  composing freely).
* `SuFunctor.Target` — subprobability mass functions and the thin
  double category of per-element semantic constraints.
* `SuFunctor.Universe.Carrier` — the subprobability carrier
  `Δ_{≤1}(V)` as a compact convex set, penalty functionals, walls;
  citizenship is lower semicontinuity, and nothing else.
* `SuFunctor.Universe.Closure` — the operations table of the lsc
  universe: which connectives preserve citizenship.
* `SuFunctor.Universe.Judgment` — the pointwise-order judgment on the
  subprobability carrier and its graded obligations.
* `SuFunctor.Universe.ConvexChart` — convexity as a certification
  chart rather than a citizenship axiom: Fenchel–Moreau biconjugation
  at finite `V`, with the non-convex citizens kept.
* `SuFunctor.Universe.Tents` — degree-2 menus (tents) recover every
  lsc citizen: the degree axis prices certificates, never ontology.
* `SuFunctor.Universe.Witnesses` — exact witnesses for the closure
  table's refusals.
* `SuFunctor.Universe.ProbCarrier` — the flat carrier `Δ(V)`:
  probability distributions, scaled indicators, walls.
* `SuFunctor.Universe.Riesz` — the finite-outcome Riesz–Markov–
  Kakutani presentation: probability states as positive normalized
  functionals on gambles.
* `SuFunctor.Universe.CoupledJudgment` — the coupled satisfaction
  judgment: ∀-flavored safety, ∃-flavored liveness dips, ex-falso
  inversion, the con theorem, the compiled refinement order, diamond
  splitting, and decidability on affine rows.
* `SuFunctor.Universe.Generation` — every flat-carrier citizen is a
  countable sup of finite mins of rational threshold rows.
* `SuFunctor.Universe.Points` — the definability refutations: no
  finite coupled DNF pins a proper system (the bump lemma), and upper
  opens are not spec classes.
* `SuFunctor.Universe.Fragments` — the finite syntax's boundary,
  twice: the rectangle (disjoined safety collection ∧ conjoined
  liveness collection) cannot express a coupled disjunction, and the
  at-most-one-realizable class is closed in every admissible topology
  yet is no finite disjunction's model class — closed does not imply
  judgment-definable.
* `SuFunctor.Universe.VietorisDictionary` — the radial compile:
  grades, bodies, the judgment as containment-and-escape, and the
  `(min, +) → (∪, ⊙)` algebra.
* `SuFunctor.Universe.VietorisStratum` — the dictionary's topology:
  bodies closed/compact iff citizen, the radial locus closed in the
  hyperspace, spec classes as locally closed hit-and-miss crescents,
  and the graded atoms lsc through opposite Vietoris faces.
* `SuFunctor.Universe.ImageChar` — the image characterization: the
  compile is a bijection from citizens onto the nonempty closed
  radial sets, with the attained ray gauge as its inverse.
* `SuFunctor.Universe.ThinningAbsorption` — rate imprecision as
  stay-channel imprecision: the Poisson-thinning chart into the
  extended outcome space is mass-one and generator-lossless, absorbed
  families land (radially embedded) in the classical Cozman corner of
  the credal poset, and the family is recovered as the full-mass
  slice; with the endpoint probe and the coupling divergence witness
  for joint-body conventions.
* `SuFunctor.Universe.DemonicPortCitizenship` — the citizenship lemma
  at the imprecise tier's composite shape: demonic-port images of
  nonempty compact regions under maps continuous on them land, radially
  embedded, in the credal-body class — no convexity claimed, and a
  quadratic witness shows none is available; with the piecewise and
  polynomial faces, the exact-slice/never-raw packaging honesty pair,
  and convexity-free landings for absorbed thinning families.
* `SuFunctor.Universe.IdealPoint` — systems are ideal points: the
  body of `σ` is pinned among radial sets by one miss-face and the
  escape demands of the citizens `σ` dips under, so the singleton
  embedding of systems into spec classes is a directed infinitary
  crescent — spec-shaped, one level of infinitude above
  judgment-definability.
* `SuFunctor.Universe.Sector` — the sector lemma: on the radial locus
  the escape faces of citizens generate the whole lower Vietoris, by
  band interpolation and radial descent.
* `SuFunctor.Universe.Hypograph` — the hypograph homeomorphism: the
  Vietoris topology on the radial locus is the hypo-topology on grade
  functions, via the radial map and the polar lift.
* `SuFunctor.Universe.TransposedGeneration` — the generation theorem
  one level up: every Vietoris-lsc functional on the hyperspace is a
  countable sup of finite mins of miss-graded and hit-graded atoms.
* `SuFunctor.Universe.RecordLens` — the record lens at the finitary
  stratum: graphs con-coupled with occupation measures, the lens
  compact, the touch-wall and dwell-wall species citizens of opposite
  faces, separating exactly on zero-dwell visits.
* `SuFunctor.Universe.RecordLensContinuum` — the record lens at the
  continuum stratum: compact metric stages, hyperspace graphs, narrow
  occupation measures; con closed by one upper-face and one
  lower-face demand, the lens compact by Prokhorov, and the wall
  species citizens under the open-bad-region polarity condition.
* `SuFunctor.Universe.FellTopology` — the Fell topology: hyperspace
  vocabulary at the noncompact stratum.  Hit classes of opens plus
  miss classes of compacts; the closed-set hyperspace compact over
  every ambient (Alexander) and Hausdorff over locally compact
  ambients; the citizen classes with their polarities; the escape
  specimen (`{⊥}` open iff the ambient is compact); the collapse to
  Vietoris on compact Hausdorff ambients.
* `SuFunctor.Universe.FellOnePoint` — the one-point collapse:
  adjoining `∞` is a homeomorphism `CL(Y) ≅ {B ∈ CL(Y⁺) : ∞ ∈ B}`
  onto a closed slice of the compactification's hyperspace,
  stratum-general with Fell on both sides; on (weakly) locally
  compact Hausdorff ambients the upstairs topology is Vietoris and
  the citizens are the compacts, so every compact-case hyperspace
  theorem is objectwise-citable at the noncompact stratum through
  it.
* `SuFunctor.Universe.RecordLensFell` — the record lens off the
  compact pin: closed Fell graphs con-coupled with narrow laws on
  locally compact second-countable completely-pseudo-metrizable
  ambients; con closed with tightness and a compact interpolant
  replacing the compact-stratum regularity-and-thickening pair;
  compactness over tight families; the wall species and zero-dwell
  separation, stratum-general.
* `SuFunctor.Plain.Penalty` — the scalar stock of the spec-class
  decoration tier: finitely supported subprobability joints, their
  pushforward, and penalty functionals with contravariant transport —
  the exact, measure-free stratum the class tiers are built over.
* `SuFunctor.Plain.SpecFunctor` — the spec-class decoration functor
  over the interfaces-and-wirings base: classes of penalty functionals
  as fibres, class-level pushforward-then-add as compositor, proved a
  span-valued lax double functor; the plain double Grothendieck total
  (`SpecTotal`) with its strict projection.
* `SuFunctor.Plain.Battery` — the acceptance battery at the class
  stratum: the retired obligations transposed to classes, positive
  twins and preregistered mutants each refuted by an explicit witness.
* `SuFunctor.Plain.Comparison` — the plain total against the virtual
  machinery: the discrete double opfibration property of the
  projection, instantiated.
* `SuFunctor.Plain.CheckerFace` — the certificate calculus's verdict
  as the possibilistic face at the exact stratum: Boolean upper
  probability over the credal compile of the premise-and-admissibility
  cylinder, `Sequent.semanticallyValid` iff the conclusion complement's
  upper probability vanishes, with the *ex falso* corner named.
* `SuFunctor.Plain.MeasJoint` — the general stratum of the scalar
  stock: subprobability Borel measures over arbitrary measurable
  carriers, pushforward functorial along measurable maps and weakly
  continuous along continuous ones (the functor part of the Giry
  monad), penalty transport, the base-free coherence cores of the
  composite-penalty calculus, lower semicontinuity as the standing
  membership hypothesis with its closure calculus and compact
  attainment, and compact support as a transport-closed subclass.
* `SuFunctor.Plain.GeneralFunctor` — the decoration functor's tight
  tier at the general stratum, over measurable carriers (the base
  whose morphism datum — measurability — is what the functor laws
  consume), with the acceptance battery transposed row by row,
  refutation pins included.
* `SuFunctor.Plain.GeneralSeam` — the upward seam: every finitely
  supported joint is a subprobability Borel measure (weighted point
  masses), the identification respects mass, zero, pushforward, and
  penalty transport, and the finite decoration functor is the
  restriction of the general one along it.
* `SuFunctor.Site.WindowPenalty` — window carriers: trajectories over
  a window family, the penalty calculus over them, and the two
  transport directions of a site-indexed fibre assignment.
* `SuFunctor.Site.SiteFunctor` — the sheaf upgrade of the decoration
  tier: window-indexed persistent families of penalty classes as
  fibres over the unchanged wiring base — the site dimension entering
  through the decoration, never through the base — with its plain
  total and strict projection.
* `SuFunctor.Site.ClassDescent` — constructible fibre classes over the
  window system, consuming the landed Fell descent theorem.
* `SuFunctor.Site.Battery` — the acceptance battery re-run at the site
  stratum, componentwise.
* `SuFunctor.Site.MatchingFork` — the site dimension's boundary:
  persistence survives the compositor, strict matching provably does
  not.
* `SuFunctor.Virtual` — the virtual presentation of the source: rule
  families with premise *lists*, the multicategorical derivation
  calculus (nullary proof-object import, identities, splicing), and the
  single-object virtual double category it presents — no loose
  composition, hence none of the refuted structural obligations.
* `SuFunctor.VirtualComparison` — the free promotion of the virtual
  presentation is the formal-conjunction (list) double category:
  strings are lists, concatenation is loose composition, and promoted
  cells are blockwise derivability (`ListDeriv`).
* `SuFunctor.HypernetInclusion` — the possibilistic inclusion of
  hypernets into the semantic universe: the transformation θ sending a
  typed wiring diagram to its austere possibilistic coupling — the
  singleton presentation whose floor is the wall of its
  admissible-valuation region and whose liveness family is the bare
  properness demand — with the unit, concatenation, and renaming
  coherence laws each proved as an exact equality of presentations,
  and the kernel of θ on decorations characterized extensionally.
* `SuFunctor.HypernetComposition` — the composition calculus those
  laws generate, at the content-addressed stratum: strict
  associativity and units for aligned composition (no coherence
  tower), triple-composition normal forms (the θ-image lies in the
  strict locus of the universe's laxity), substitutability
  (composition respects extensional equivalence of components),
  outward propagation of infeasibility with the bottom-credal-body
  reading, the minimal shared-wire witness that feasibility does not
  compose, and the naturality of renaming against the compositor —
  definitional at the state level, an exact hexagon on θ-images.
* `SuFunctor.HypernetDouble` — the packaged inclusion: the pseudo
  double category of open hypernets at the content-addressed stratum
  (rosters, inclusions, aligned cospans decorated with wiring
  diagrams), the possibilistic coupling as a tight transformation over
  the state-family base change, and the inclusion into the semantic
  universe as a lax double functor over that base change — preserving
  the canonical opcartesian lifts on the nose, with compositor
  laxators invertible exactly on the seam-disjoint locus.
* `SuFunctor.HypernetWf` — the well-formed fragment of the double
  category of open hypernets: linearity, single static assignment, and
  the interface discipline as a predicate on decorated loose arrows,
  containing the loose identities and closed under loose composition on
  the seam-disjoint locus — each closure clause pulled back through an
  adapter from the gluing theorem of the composition layer, with the
  adapter intertwining composition and units on the nose.
* `SuFunctor.HypernetElaboration` — the semantic half of the
  single-genus rule: a view symbol is nothing over and above its
  elaboration.  Since a view and its expansion live over different
  apexes, the statement is a marginalization — θ of the view is the
  min-plus direct image of θ of the expansion along boundary
  restriction (`theta_elab`, witnessed at the canonical
  packaged-polynomial instance) — resting on the exact wall law that
  the direct image of a region's wall is the wall of its image
  (`Pen.push_possWall`).
* `SuFunctor.Stochastic.NoiseSemantics` — the probabilistic tier at
  finite outcome: the uniform reference measure on the noise cube,
  pushforward denotations landing in the flat carrier (normalization a
  theorem, discard marginalization), the copy-vs-resample separation
  witness (equal marginals, distinct joints), and the null-boundary
  singleton lemma with its threshold-cell instance.
* `SuFunctor.Stochastic.NoiseKleisli` — Kleisli functoriality of the
  noise-port semantics: the finite-carrier Kleisli composition on the
  flat carrier (point masses the units, pushforward the deterministic
  special case), disjoint port blocks read as independence, the
  functoriality law for sequential composites with disjoint rosters,
  and the shared-roster failure witnessed by the copy-vs-resample
  separation.
* `SuFunctor.Stochastic.JumpMeasure` — the measure-weighted tier: six
  generators over a finite state space graded by rational intensity
  majorants, elaboration to the thinning normal form (mass-one kernels
  into the next/stay/cemetery alphabet) with soundness and exact mass
  accounting, the dilation and phantom-jump moves of the thinning
  quotient, module laws for scaling, and interleaving with the
  generator Leibniz rule.
* `SuFunctor.Stochastic.JumpAlgebra` — the thinning-form composite
  algebra: superposition, scaling, coordinate extension, and
  interleaving on normal forms with rates as the grading, their
  generator laws (addition, the module action, the Leibniz rule with
  the killing channel transported), elaboration as the graded
  homomorphism onto them (definitional on the module structure,
  generator-level for interleaving), and the kill-washing separation
  showing the cemetery channel is content, not plumbing.
* `SuFunctor.Stochastic.JumpDiffusionThinning` — the multi-leg
  jump-diffusion jump structure recovered over the tagged alphabet:
  the deficit-to-cemetery rewrite (weight sum one unconditionally,
  sound by the landed transfer decomposition) and the full generator
  recovery over mass-one tagged mixtures.
* `SuFunctor.WiringModes` — the wiring modes against the semantic
  universe: share rows denote identification patterns, with
  row-preserving renames as cells and the certificate transport
  natural against the compositor (packaged as a literal natural
  transformation); parameter setting factors through sharing by
  `rfl` (direction premises are formation-refusal data with no
  semantic carrier), with the assume–guarantee slack arithmetic
  proved additive; mode switching gets its statics (location wire,
  per-location transports natural in component renames) and
  deliberately nothing more at this stratum.
* `SuFunctor.BagFormer` — the bag former's denotational layer: the
  bag interface is the switch composite over the token-power roster
  definitionally (`bagObj_eq_switchObj`, by `rfl` at universe zero);
  the exchange quotient enters as a group action by wire renames
  (count wire fixed, token inclusions permuted, component renames
  equivariant), with exchange-invariance of DNF presentations closed
  under the composite's transports — the aggregate-observable
  interface forced by the quotient, as a theorem; the multiset
  denotation of mode-`n` states is a complete exchange invariant
  (`powBag_perm` + `powBag_eq_iff`: states modulo exchange are
  `Sym^n` of the state space, no order demanded); and the monad
  structure's static shadows (`toBag_one` singleton, `powBag_flatten`
  bind) tie the interface stratum to the value-stratum monad laws of
  `DoubleCat.BagMonad`.
* `SuFunctor.TokenArcs` — the arc-level compiles of the
  token-population (stochastic Petri / SDCPN) reconstruction:
  ordinary arcs' one static identity (`powBag_drop` — the bag is the
  selected token cons the remainder; consume and produce are its two
  readings) with well-definedness on the exchange quotient by cons
  cancellation; read (enabling) arcs as parameter setting on the
  nose (`readRows_pat_iff`, `readSetRows`), their selection family an
  orbit of the exchange action connected by cells; count guards
  exchange-invariant via the count wire; inhibitor arcs excluded by
  design with the monotonicity mechanism named; supervisory species
  (rates, forcing, cascades) deliberately left to the generator
  stratum.
* `SuFunctor.TokenGame` — the statics adequacy square for stochastic
  Petri frames over bag composites, whole: the marking readout of the
  compiled net roster is surjective and a complete exchange invariant
  (markings are compiled states modulo per-place exchange, one shape
  at a time); the community token game corresponds to compiled firing
  witnesses in pattern vocabulary (`step_iff_fireWitness`, through
  the split denotation `powBag_split` and the parameter-setting
  denotation); monotone enabledness proved as the inhibitor
  exclusion's warrant (`enabled_mono`); the init face and the
  race-aggregation face at their statics strata.
* `SuFunctor.Adequacy.StochasticPetri` — the delay-race face of the
  stochastic-Petri square at the finite time-abstract stratum:
  bounded uncoloured nets compile to off-diagonal race-rate rows in
  the unordered convention, the compile-commutes triangle *is* the
  arc-multiplicity dictionary theorem (`raceCount_eq_dict`, ordered
  census = `∏ (demand)!` times unordered count), and the square is
  the continuous-time square instantiated at the community race
  chain — engine reuse through the dictionary triangle.
* `SuFunctor.Adequacy.StochasticPetriCascade` — the immediate/cascade
  face: nets with immediate transitions compile to two-sorted Markov
  automata (tangible markings Markovian, vanishing markings
  instantaneous — the community's state-space exclusion as the rate
  field's domain type), the cascade is the automaton square's
  absorbing closure, cascade termination is a rank certificate
  (`CascadeRank`), conflict resolution is scheduler-generic with the
  uniform single-firing scheduler as the community instance, and the
  square is `ma_adequacy` through the dictionary triangle one storey
  up — five-storey engine reuse, zero new inductions.
* `SuFunctor.Adequacy.StochasticPetriColoured` — the coloured
  formation (`FinCSPN`: per-place finite colour boxes, markings
  counted per colour class, colour-dependent rates, guards as
  per-vector cylinders, Dirac firing measures) and its delay-race
  face: the coloured ordered census factors through the
  per-colour-class multiplicity dictionary (`raceCount_eq_dict`),
  the compile triangle is that dictionary rowwise, the square is the
  continuous-time square at the coloured race chain, and the
  `Unit`-colour degeneracy theorems show the formation contains the
  uncoloured fragment on the nose.
* `SuFunctor.Adequacy.StochasticPetriColouredCascade` — the coloured
  immediate/cascade face: immediate transitions carry guard
  cylinders and Dirac firing measures, the compiled automaton's
  actions are (transition, colour-vector) *pairs*, vanishing is a
  coloured judgment (a red token may vanish where a blue one rests),
  cascade ranks are colour censuses, and the square is `ma_adequacy`
  through the coloured dictionary triangle — the left square the
  coloured flattening triangle consumes, statement shape unchanged.
* `SuFunctor.Adequacy.StochasticPetriColouredDemonic` — the coloured
  demonic and angelic faces: the enabling-respecting arena over
  (transition, colour-vector) pairs — the demon selects tokens, not
  just transitions — with the set-valued square, the credal-slice
  reconciliation, verdicts at both polarities, the membership lemma
  feeding both directed transfers, and the double obstruction
  control (disabled pairs by supply and by guard each refute the
  branch-level certificate at a singleton transition roster; the
  recolouring net refutes every cascade rank at once).
* `SuFunctor.Adequacy.StochasticPetriSetFiring` — the set-firing
  face: simultaneous composite firings of non-conflicting immediates
  (the founding formalism's rules R1/R3), driven by one value
  identity — an enabled chain is exact, so its result is pinned by
  the firing multiset alone (`chainFire_val`); order-invariance and
  the pairwise diamond with no permutation induction, the
  simultaneous composite equal to every enabled chain under joint
  supply, the reservation precondition (`JointReservation`), the
  intermediate-scope condition discharged by capacity headroom, and
  refutation controls showing each hypothesis load-bearing (a
  supplied-locus divergence, a mid-chain capacity block, a
  read/consume conflict).
* `SuFunctor.Adequacy.StochasticPetriFlatten` — the flattening
  premises and the commuting-triangle instance: the flattening's
  definedness premises as certificate-shaped rows at the uncoloured
  grain (initial tangibility, decidable; the invariant token bound in
  the witness-vector idiom, with step soundness, reachability
  closure, an intrinsic capacity-free per-place bound, and a
  token-creating refusal control; cascade termination consumed from
  the landed rank certificate), dictionary controls past arity 2, the
  triangle statement skeleton (`flatten_triangle_of_agree`: a flat
  presentation on an abstract mode carrier agreeing with the
  scheduler-closed net denotes an isomorphic constraint — an
  invertible globular cell between two house compiles, no process
  constructed), its demonic directed sibling (the membership lemma as
  a directed cell), and the drain-net instance: hand-written
  flattening data on `Fin 3` checked entry-by-entry against the
  compiled closure, the invertible cell, and the wired positive face.
* `SuFunctor.Adequacy.StochasticPetriAngelic` — the angelic
  (existential-over-schedulers) face, and the square assembled: the
  angelic verdict operator (`SatAngelic` — the ∃-dual of `SatCredal`,
  read on the radially maximal slice, with the un-sliced degeneracy
  mechanized: the zero model witnesses every zero-threshold
  upper-bound atom), the equal-mass transfer (the angelic verdict on
  a union of rays is existential quantification over the family), the
  net-level feeding equivalence over the enabling-respecting arena,
  the two directed verdict transfers from one membership lemma
  (universal claims restrict to every member; claims on a member are
  angelic witnesses — flatten-facing forms included), the angelic
  directed cell into the slice object, the wired verdict, and the
  law-level plurality controls: the uniform and always-discard
  members' closed path laws genuinely differ at horizon one (the
  demonic module's named open computation, resolved), and the same
  pair splits the verdict polarities on the shipped conflict net.
* `SuFunctor.Adequacy.Funnel` — the funnel pattern as a
  certificate-layer conjunction with shared subject: the honest sort
  (raw parts with two region citations; assembly refuses unless they
  are one reference and the budget clears the sign gate), the positive
  same-subject composite certificate
  (`funnel_coupledSat_of_parts` — the landed composite-certificate
  theorem at identity transports), the monotone-conjunction lawfulness
  package in place of the refused unitality, the tower-citation edge
  as an equation (`funnel_gate_shared`), the demanded-dip-family
  refusal and the presentations fence at the pattern's sort, and the
  compositor refutation re-stated (`funnelDecl_not_system_former`).
* `SuFunctor.Adequacy.Bag` — the bag former's exchange-quotient
  transport (the E1 cell of its adequacy square): the sorted-
  representative section of `B^n → Sym B n` is measurable under the
  quotient σ-algebra, from only a linear order with measurable order
  graph — each sorted coordinate is an order statistic, a finite
  min-of-maxes lattice term (`sortTuple_apply_eq_inf_sup`), so no
  selection theorem and no choice on ties; the quotient kernel of a
  canonicalization-invariant chain closes the commuting square at
  every finite horizon by kernel-category algebra
  (`quotKernel_comp_eq`, `iter_intertwine`), section-independently
  (`comap_section_congr`); assembled on the shape-indexed bag carrier
  as `bag_transport`, with exchange-invariance and
  canonicalization-invariance interderivable (`invariance_iff_perm`),
  and the order-graph hypothesis discharged for `ℝ` and for
  lexicographic real colour vectors (`measurableSet_le_lex`).
* `SuFunctor.Adequacy.StochasticPetriSupervise` — supervision as
  control through enablement, with the formalism's own enabling
  arcs: the gating lemmas read off the landed faces (a closed gate
  zeroes the ordered census; a weight-1 gate place is a
  multiplicative census factor, whence ℕ-graded throttling; `iread`
  gates the tangible/vanishing classification; plant firings fix
  gate coordinates — read-no-consume is the zero-order hold), the
  `Supervise` package census (`ArcSeparation`: plant touches policy
  places through read arcs only, both directions checked; policy
  updates carry no arcs on plant places), the Boolean gate
  discipline, and micro-instance controls including a cascade whose
  first step is the policy's own wake and the landed cascade square
  applied to the supervised composite as an instance.
* `SuFunctor.Adequacy.StochasticPetriSuperviseDemonic` — the
  `Supervise` pattern's adequacy faces: the package as data
  (`GatePlant`/`Occupant`/`assemble`, with the census discharged
  once by the expansion lemma), the fixed-policy square as a
  one-line instance of the cascade square (the collapse), and the
  demonic gate-envelope — `EnvelopeUnion` over the certified policy
  seat, on the common marking space through the record-space
  pushforward, with the equal-mass slice, uniform-over-the-seat
  verdicts at both polarities, roster monotonicity, and deliberate
  idling seated as a member (the family-level liveness refusal).
* `SuFunctor.Adequacy.Inclusions` — the shared library of adequacy
  squares: inclusions of classical semantic objects into the credal
  stratum (singleton-credal, point-mass), formal conjunctions of
  constraints as loose-arrow diagrams, and the packaging of pointwise
  equivalences as invertible cells.
* `SuFunctor.Adequacy.Dtmc` — the first adequacy square: the compiled
  row grain of a finite discrete-time Markov chain denotes, in the
  credal stratum, exactly the singleton inclusion of its classical
  finite-horizon path law; with the connector tying the exact-rational
  law to the standard monadic construction.
* `SuFunctor.Adequacy.Pgm` — the adequacy square off the time-line:
  the compiled conditional-table wires of a finite Bayesian
  network denote, in the credal stratum, exactly the singleton
  inclusion of its classical chain-rule joint; with the connector
  tying the exact-rational law to ancestral sampling (iterated
  `PMF.bind` along the topological order).
* `SuFunctor.Adequacy.Envelope` — the envelope stratum: the credal
  presentation's precise face (the closed ray `[0,1]·μ`) and the
  constraint stratum's exact singleton inclusion agree on the radially
  maximal slice, which is what the verdict operators read; with the
  kind-selected credal satisfaction (lower reads the slice, upper the
  whole set) and the refutations that force the split.
* `SuFunctor.Adequacy.Mdp` — the fixed-policy MDP square: action-keyed
  outcome rows closed through memoryless-randomized policy rows denote
  exactly the singleton inclusion of Puterman's fixed-policy trajectory
  law — the chain square instantiated at the closed-loop chain, with
  the policy-selection connector (`PMF.bind`) beside it.
* `SuFunctor.Adequacy.CtmcJumpChain` — the continuous-time square at
  its jump-chain face: off-diagonal rate rows (diagonal entries
  unrepresentable by the key's type), closed to chain rows through the
  Norris jump-step normalizer, denote exactly the singleton inclusion
  of the embedded jump chain's path law — the chain square
  instantiated at the jump chain, with the rate-factorization identity
  and the diagonal-blindness receipts beside it; the exponential
  time-law stratum is deliberately separate.
* `SuFunctor.Adequacy.MarkovAutomaton` — the Markov-automaton square
  at its fixed-scheduler face: two-sorted automaton rows (timed rows
  at instantaneous states and diagonal rate entries both
  unrepresentable by type), scheduler rows in the decision square's
  policy grain, closed by a rank-certified absorbing computation to
  chain-grain rate rows, denote exactly the singleton inclusion of the
  closed chain's jump-chain path law — three-storey engine reuse, with
  the acyclic-absorption package, the rate-factorization spelling
  agreement, and the self-loop thinning identity beside it.
* `SuFunctor.Adequacy.EnvelopeUnion` — the envelope stratum,
  set-valued: the credal presentation of a *family* of laws is the
  union of its members' rays, and for an equal-mass family its
  radially maximal slice is exactly the family — with the verdict
  transfer (lower through the slice, upper through down-closure), the
  boundary cases mechanized, and the unequal-mass fixture pair
  witnessing that the mass hypothesis is not decorative.
* `SuFunctor.Adequacy.MdpDemonic` — the demonic MDP square, the first
  genuinely imprecise one: the policy-free compiled decision former
  under an existentially quantified scheduler mechanism denotes
  exactly the *set-valued* inclusion of the demonic law-set (all
  memoryless randomized policies); the credal presentation reconciles
  through the slice at mass one, and the kind-selected verdicts reduce
  to the literature's uniform-over-policies bounds at both polarities.
* `SuFunctor.Adequacy.MaDemonic` — the demonic Markov-automaton
  square, the set-valued face at continuous time: the scheduler-free
  compiled automaton rows under an existentially quantified
  scheduler-row mechanism, at the working fuel of a branch-level Zeno
  certificate (one rank serving every adversary), denote exactly the
  set-valued inclusion of the demonic law-set; rank-irrelevance makes
  the demonic set a property of the automaton alone, the
  certified-family stratum carries the general (partially-Zeno)
  object, and the verdicts reduce to uniform-over-scheduler bounds at
  both polarities through the equal-mass slice.
* `SuFunctor.Adequacy.QuantumNet` — the quantum adequacy square, both
  faces, at matrix grade: the textbook corner consumes the landed
  locally covariant kinematic fragment (Brunetti–Fredenhagen–Verch
  Definition 2.1) verbatim; the carrier is the record space, the left
  edge the Born/Gell-Mann–Hartle record law (connector definitional,
  factoring through the state-presheaf fiber); the credal face is the
  first square whose imprecision is the community's own theorem —
  no-preferred-states forces a set-valued state object — with the
  slice, both verdict transfers, convexity under mixture-closure (and
  its negative witness), and the incomplete-family subprobability law
  exercising the target stratum's native partiality at last.
* `SuFunctor.Adequacy.DelayLine` — the first square with a spatially
  extended cell: the ideal delay line (transport on a segment of
  length `c·τ`), wired to an ODE cell through an initial load, an
  inflow trace, and an outflow tap, has trajectories exactly the
  classical solutions of the delay differential equation
  `ẏ(t) = f(y(t), y(t−τ))` — delay equations enter as a *wiring
  pattern*, the history segment being the field on the spatial cell
  read along characteristics.  The left edge is the method of
  characteristics (one-variable mean value theorem, total today), so
  the square is two-sided at the possibilistic stratum, with the
  per-solution Dirac face beside the set-valued inclusion.
* `SuFunctor.Adequacy.SemanticUniverseWiring` — the squares wired to
  the semantic universe: laws enter the exact-stratum judgment as
  ideal points (singleton walls, across the injective rational-to-real
  scalar seam), compiled constraint diagrams present as
  single-disjunct coupled DNFs (floors the walls of the conjunctions,
  liveness exactly the properness demand), and one judgment bridge
  reads every square's feeding lemma at the fibre's own satisfaction:
  membership of the law's ideal point in the compiled presentation's
  model class is equivalent to the law being the classical semantics —
  chain, graphical model, fixed-policy decision process, and the
  demonic law-set at the set stratum (the one-atom scheduler
  projection); the credal readings are recovered through the envelope
  stratum's slice reconciliations, and the ray-vs-singleton choice at
  the judgment is fenced by an explicit failure witness.
* `SuFunctor.Adequacy.BagWiring` — the bag square at the judgment: the
  one-step generating cell of the exchange-quotient transport,
  re-stated at the exact stratum (the `SubPMF` faces of the one-step
  commuting square and its section-independence, consuming the
  transport core's quotient/section statics), and wired in the
  demonic corners' one-atom idiom — `su_bag_adequacy`: the ideal
  point of a collective law models the section-compiled presentation
  at an ordered state's class exactly when the law is the ordered
  dynamics' direct collective reading, so token order and the
  canonical-representative bookkeeping are both invisible at the
  judgment; exchange orbits share one collective reading
  (verdict-invariance stated at the diagram level), every collective
  law is a reading (the canonical section lifts), and the
  finite-horizon closure stays where it is mechanized, at the measure
  stratum's `bag_transport`.
* `SuFunctor.Adequacy.ProbProg` — the probabilistic-programs square
  at the former's grain: a program is a start stage and a loop body,
  each a noise-port hypernet stage, and the unrolled program text —
  one deterministic map on one summed-roster cube — denotes the
  kernel-local Kleisli iterate of the stage denotations
  (`noiseDenot_progTraj`, the Kleisli functoriality law folded to the
  former level, unconditional at the measure stratum); the profile
  determines the path distribution (`pathDist_profile` — a model type
  is a profile, not a tag); and for a program presenting a classical
  chain through the exact-rational face of its stage kernels
  (`Presents`, the stratum boundary stated rather than smoothed), the
  judgment on the compiled outcome-row presentation pins exactly the
  text's denotation (`su_pprog_adequacy`), with the fair-coin
  specimen discharging every hypothesis concretely.
* `SuFunctor.Adequacy.Ode` — the adequacy square for the autonomous
  initial-value problem, the drift-only frame every continuous plant
  specializes: compiled forward rows (initial row, record-class row,
  drift rows) against the community's integral-curve concept, tied by
  the fundamental theorem of calculus in both directions; the pinning
  theorems derive determinism from declared-domain Lipschitz
  hypotheses through the mechanized Grönwall interface, whose
  hypotheses are the forward rows verbatim; the delay-line ODE-cell
  clause and the demonic initial box are one-line specializations of
  the same seam, and the wiring to the semantic universe rides the
  generic transport layer with the possibilistic contrast (the zero
  law models every compiled presentation) stated rather than
  smoothed.
* `SuFunctor.Adequacy.Rode` — the adequacy square for random
  differential equations, drift plus a boxed parameter axis: the
  per-draw connector, square, and pinning theorems are one-line
  specializations of the ODE seam at the drawn drift (the community's
  pathwise solution concept made definitional), and the parameter-box
  face denotes the *union* over the box of per-draw solution sets —
  the possibilistic body of the frame, deliberately the opposite
  polarity from the uniform-over-the-box verdict, which is
  judgment-level; the demonic rectangle (parameter box × initial box)
  composes with the ODE square's union machinery verbatim, and the
  wiring rides the same transport layer with the zero-law contrast
  holding at every box, the empty one included.
* `SuFunctor.Adequacy.CheckerCarrier` — the checker carrier: the
  certificate calculus's verdict tied to the semantic universe's
  fibres at its own wire object.  The face module's possibilistic wall
  is the wiring layer's wall penalty of the credal compile (one
  equation); between wall systems the coupled judgment is the
  behavioural superset test, so the verdict is membership of the
  cylinder's wall in the model class of a single-disjunct presentation
  whose floor is the conclusion's wall; and a hypernet's valuations
  embed injectively into the state space of its wire object (typed
  wires over the sigma of tensor values) with image exactly the
  well-typed states, the face calculus transporting along any
  injection of carriers at every level of the upper probability — so
  the verdict is a judgment in the fibre over the hypernet's wire
  object, on the nose.
* `SuFunctor.Adequacy.CheckerAcceptance` — acceptance as a
  semantic-universe theorem: the reflection route's sealed-byte
  acceptance composed with the checker face and the checker carrier.
  One theorem per altitude, one line each: an accepted claim's
  sequent read as the vanishing upper probability at its own
  valuation carrier, as membership of the cylinder's wall in the
  model class of the sequent's presentation, as the face at the wire
  object's record space, and as a judgment in the semantic universe's
  fibre over the hypernet's wire object — certificate bytes in, a
  fibre citizenship out.
* `SuFunctor.Adequacy.RecordSpace` — the record spaces of the compiled
  systems: the wire objects the wiring layer's per-carrier boundary
  named and left unconstructed.  The trajectory interface has the
  horizon-`k` trajectory space as its state space definitionally, so
  the chain and decision-process squares re-instantiate by
  substitution as citizens of the fibre over their own wire object,
  with horizon inclusions as tight arrows and prefix-reading as their
  restriction; the assignment interface identifies joint assignments
  with its well-typed states (the erasure pattern at the dependent
  carrier), and the graphical-model square transports along the
  embedding within the wiring's own genre, by pushforward of laws and
  per-element constraints through the same generic judgment bridge.
* `SuFunctor.Adequacy.DtmcGenerator` — the one-step generator form of
  the DTMC row grain: the recompute contraction (transfer minus
  identity) over the stored outcome rows, the discrete segment-Dynkin
  identity making computed generator rows theorem-grade drift
  premises, its supermartingale consumption, and the bottom fixtures —
  the zero law (infeasibility's denotation, the bottom body, never the
  empty set) satisfies every down-closed safety floor and refutes
  every positive-threshold liveness demand when the demand rides the
  wall of its negation, with the polarity-control theorem deriving the
  wrong verdict from the un-negated spelling on purpose (why verdict
  schemas carry polarity explicitly).
* `SuFunctor.Adequacy.DtmcAbsorb` — absorption brackets for the DTMC
  row grain: the forward measure evolution (exact-rational mass
  vectors under the transition matrix) with its duality bridge to the
  path law's endpoint expectations; monotone absorption (mass on a
  set of absorbing states never decreases); the conservation bracket
  pinning every later class mass inside the horizon-`T` window; the
  correlated-ratio bracket carrying the bounds through normalization
  (conditional measures of compiled probabilistic programs); the
  composed claim shape the certificate species checks; and the
  transfer-contraction induction whose `c = 1` case subsumes the
  generator form's supermartingale consumption.
* `SuFunctor.Adequacy.DtmcAliveTail` — the alive-mass tail of a
  regional transfer contraction: with a closed complement (no stored
  row re-enters the region) and a unit floor on the certificate
  component, the bare mass remaining on the region decays
  geometrically — the stored-row form of a hitting-time tail bound;
  both added hypotheses carried with kernel-checked countermodels as
  standing mutant teeth.
* `SuFunctor.Adequacy.DtmcContraction` — weighted transfer contraction
  for the discrete row grain: the forward evolution generalized from
  stochastic kernels to arbitrary nonnegative weight matrices
  (score-carrying and sub-probability row sets as instances of one
  induction), the contraction core with its score face and its
  subsumption instance re-deriving the stochastic core (chaining
  through the `c = 1` face to the incumbent generator-form
  consumption, so certificates admitted under the incumbent stay
  valid under the strengthening), the regional packaging (contraction
  on a region plus no-re-entry, via the region-supported observable),
  exit domination, and the geometric and arithmetico-geometric tail
  assemblies bounding total and time-weighted exit weight past any
  horizon.
* `SuFunctor.Adequacy.DtmcTemplate` — geometric templates collapse to
  one inequality: under `V(n) = M·γⁿ` with integer offsets, the
  per-state contraction inequalities of an offset-invariant row
  family hold at every template instance as soon as one collapsed
  exact-rational inequality holds — unbounded-counter regions become
  finitely checkable.
* `SuFunctor.Adequacy.DtmcProductProfile` — product-profile templates
  collapse to finitely many inequalities: the d-dimensional face of
  the template collapse, for the uniform-axis ±1 walk on `Fin d → ℕ`
  with monus at zero and absorption at the origin.  Under the product
  weight `V x = ∏ i, u (x i)` — per-coordinate ramp profile, then a
  constant geometric ratio — the alive one-step transfer factorizes
  through per-coordinate transfer ratios, the ratios stabilize past
  the ramp, and the finitely many class inequalities
  `(d−k)·rMax + k·rInf ≤ d·c` discharge the contraction at every
  state owning a geometric-regime coordinate.  The window-vocabulary
  corollary carries the load-bearing reach side condition
  `profile length ≤ box + 1`, whose necessity is witnessed on a
  concrete admissible ramp profile.
* `SuFunctor.Adequacy.MarginalGlue` — the marginal-glue obstruction:
  Vorob'ev's pairwise-consistent-but-jointly-unrealizable family of
  pair laws over a cyclic three-site cover, mechanized over the
  subprobability stock (no joint exists, mass-losing joints included),
  with the tier separation (records glue where laws do not), the
  controls (dropping or unfrustrating one edge restores gluability),
  and the credal absorption: the inconsistent family's lawful
  denotation is the bottom credal object, whose vacuous lower verdict
  is kept explicitly distinct from satisfaction-as-consistency.
* `SuFunctor.Universe.RadialUniverse` — the radial universe: the
  semantic universe as the radial stock, at both strata.  At the
  general carrier, the penalty↔body dictionary packaged as the
  definitional isomorphism (`compileEquiv`), hard violation compiling
  to the bottom body `{0}` (never the empty set), and the pinning
  singleton excluded by type.  At the exact stratum, the membership
  characterization (a constraint wall is radial iff the constraint is
  down-closed), constraints entering as radial walls on their credal
  completions, laws entering as their down-cones (one door:
  `rwall_singletonC`), universal properness (no radial wall excludes
  the bottom law), the judgment bridge ray-shaped, and the
  contradictory-equality composite (`x = y`, `x = false`, `y = true`
  almost surely) denoting exactly the bottom law's entry — with the
  pinning floor's non-membership replacing the fence.
* `SuFunctor.Universe.ParabolicOrder` — the cylinder column's stage
  order (the degenerate causal order of the parabolic spacetime site):
  infinite propagation speed as a theorem, simultaneity slices as
  antichains, chains as worldlines, and the order-tier half of the
  specialization theorem — the temporal site is the one-spatial-cell
  case (`CylPt PUnit ≃o ℝ`).
* `SuFunctor.Adequacy.HeatTorus` — heat on the torus over the cyclic
  three-arc mesh: the first cover-tier square.  Cell rows are pointwise
  and germ-determined (locality is the engine — no parabolic theory
  anywhere); the ring-closing wall carries the mesh's holonomy
  obligation, refusing non-descending families (the linear field) that
  every per-cell and pairwise-chain check passes; the cyclic glue is a
  theorem (`heat_mesh_glues`), so the adequacy square is two-sided at
  the pointwise-record stratum, and the contrast with the frustrated
  Vorob'ev ring — satisfiable against bottom at the credal stratum —
  is stated as theorems, the two cyclic covers side by side.
* `SuFunctor.Adequacy.HeatTorusInit` — the initial condition as an
  exposed port on the heat torus: the initial face as a boundary trace
  along the window's own filter, three port atoms extending the mesh's
  six, the ported square still two-sided at the record stratum, the
  corner-condition pattern one cover-rung up (the datum's holonomy
  identity is derived, never assumed), and the con discharge
  deliberately *conditional* on `PortFeed` — feeding the port for
  general data is the heat semigroup, cited at the enclosure stratum
  exactly as the DTMC square cites Ionescu–Tulcea; equilibria and one
  honest Fourier mode feed it constructively.
* `SuFunctor.Adequacy.SolutionSetMesh` — the solution-set mesh: the
  first consumer of the equalizer descent (`FellDescentEqualizer`) in
  anger.  Descent of closed record loci at the ring cover is exact
  (`meshDescent`); what fails at the set stratum is citizenship
  transport: the ℤ-orbit linear tube passes every wall — equalizer
  compatibility and the tube-level wrap wall — is even a chart tube,
  and is no torus tube (`setStratum_holonomy`): the branch pairing
  around the ring is the missing, wall-inexpressible datum, so
  torus-tube-hood is not of local character over the cyclic cover
  (`not_isLocalLocusEq_torusTube`), the compiled square is one-sided
  (`tubeAtoms_not_classical`), con is free via the top tube (maximal
  imprecision is always lawful), labelled ensembles glue elementwise,
  and the record-tier shadow of the failure is an integer cocycle
  frustration, ⊥-forcing under the enclosure compositor
  (`orbit_enclosure_forces_zero`).
* `SuFunctor.Adequacy.Pde` — the PDE adequacy square at the level of
  the frame: the cyclic-mesh square proven once over the interface of
  a local solution concept (`LocalRows` — germ locality + spatial
  homogeneity; the heat module's engine, factored), the jet grain of
  the formation rule (`PdeMechanism` — per-component drift polynomials
  over declared jet variables) discharging the interface by theorem
  (`PdeAt.congr`, `PdeAt.comp_sub_const`), the frame square
  (`pde_adequacy`) with heat re-derived as its specialization
  (`heat_adequacy_of_mesh`, atoms tied by `rfl`) and viscous Burgers /
  Fisher–KPP / a cross-coupled pair as one-line corollaries;
  consistency equilibrium-conditional
  (`pdeAtoms_consistent_of_equilibrium`, with `1/2` provably no KPP
  equilibrium); solution-concept rungs as named obligations
  (`PdeRung`, `rung_adequacy`, the one-directional transfer cell
  `pde_rung_transfer`); the semantic-universe wiring in-module
  (`su_pde_adequacy`).
* `SuFunctor.Adequacy.PdeRows` — declared-data presentations of the
  PDE/SPDE formation rule: the sparse row form (`PdeRowSpec` — state
  variables, jet declarations, exponent-tuple drift rows over the
  positional index space `state ++ jets`) with the **compile edge**
  into the mechanism (`PdeRowSpec.toMechanism`); heat / Burgers /
  Fisher–KPP / the coupled pair re-derived from declared rows as
  polynomial identities (`heatRowSpec_toMechanism` …), the heat rows
  tied pointwise (`heatAt_iff_rowsAt`) and the squares specialized
  (`heat_rows_adequacy`, `su_pde_rows_adequacy`); the noise-spectrum
  declaration (drivers over the orthonormal Fourier basis + a
  **required** three-form tail) with derived covariance data —
  explicit trace by Parseval (grouped per element, `sin 0` massless),
  the q-table diagonal, trace = summed diagonal
  (`explicitTrace_eq_sum_qDiag`), the total-or-refusing plain-trace
  seam (`plainTrace_divergent_none` structural), and the certified
  stochastic-heat spectrum's constants recomputed by theorem
  (`heatSpectrum_trace`, `heat_floor_exact`).

## Retired tier

The original calculus-side semantic tier — the thin presentation of
the derivation calculus (`Source`), the semantic double functor
`semFunctor` into per-element constraints on subprobability mass
functions with its soundness statement (`Functor`), the per-rule
square families (`Squares`), the graded reading (`Bridge`), threshold
polarity over mass functions (`Threshold`), the regression-pin modules
(`Refute`, `ThresholdRefute`), the virtual-route semantic functor
(`VirtualFunctor`), and the route-agreement transpose (`Transpose`) —
is archived, buildable, in the sibling package `su-functor-legacy`
(namespace prefix `SuFunctorLegacy`).  This package deliberately does
not depend on it: a result that still refers to the retired tier fails
this package's build, which is the call to restate it over the
class-valued fibres of the current construction.
-/
