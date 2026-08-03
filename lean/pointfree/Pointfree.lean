import Pointfree.Valuation.Basic
import Pointfree.Valuation.Promotion
import Pointfree.Valuation.Topology
import Pointfree.Valuation.Bridge
import Pointfree.Valuation.Functor
import Pointfree.Valuation.BridgeFunctor
import Pointfree.Prevision.Basic
import Pointfree.MeasureAlgebra.Basic
import Pointfree.Measure.SubProbability
import Pointfree.Valuation.BridgeContinuity
import Pointfree.Valuation.EscapeWitness
import Pointfree.Measure.DaggerChart
import Pointfree.Frame.Presentation
import Pointfree.Frame.HyperspacePresentation
import Pointfree.Valuation.Determination
import Pointfree.Valuation.SpatialDetermination

/-! # Point-free stochastics

Valuations on frames and the tower above them, built for consumption by
the semantic-universe development:

* `Pointfree.Valuation.Basic` — valuations (strict, monotone, modular
  maps `L → ℝ≥0∞` on a frame), Scott continuity as a mixin, pushforward
  along frame homomorphisms, Dirac valuations of frame points, and the
  subprobability/probability carriers.
* `Pointfree.Valuation.Promotion` — the dagger chart: subprobability
  valuations on `L` are exactly probability valuations on `L × Prop`,
  by pure modular algebra; Scott continuity transports both ways.
* `Pointfree.Valuation.Topology` — the lower (Scott) topology on the
  probability face, the narrow topology on the subprobability carrier,
  and the identity that forces the latter: the narrow topology is the
  pulled-back lower topology of the promoted carrier.  Evaluation is
  lower semicontinuous by construction; mass is upper semicontinuous;
  liveness walls are closed.
* `Pointfree.Valuation.Bridge` — Borel measures restrict to valuations
  (modularity = `measure_union_add_inter`); on second-countable spaces
  the restriction is Scott continuous (τ-additivity); the bridge is
  natural in continuous maps, and Dirac restricts to Dirac.
* `Pointfree.Measure.DaggerChart` — the measure-level dagger chart:
  subprobability measures on `X` are homeomorphic (weak topologies) to
  probability measures on `X ⊕ Unit`; the Prokhorov compactness
  dividend for the subprobability carrier by two independent routes;
  Lévy–Prokhorov metrizability transported along the chart.
* `Pointfree.Valuation.Functor` — pushforward is functorial, preserves
  mass, restricts continuously to both carriers, and is natural in the
  Dirac unit: the presheaf structure of the valuation storey, stated
  once over frame homomorphisms.
* `Pointfree.Valuation.BridgeFunctor` — the continuous-map face: the
  covariant pushforward `SubProb.push`, the unit square over any
  continuous map, and the bridge as a natural transformation — the
  point-set Dirac square re-derived as the image of the bridge.
* `Pointfree.Prevision.Basic` — gambles in sublevel presentation, the
  Choquet pairing and its naturality, previsions, the superlinear
  class and its closure under lower envelopes, prevision bodies.
* `Pointfree.MeasureAlgebra.Basic` — the null-quotient face: measurable
  sets modulo almost-everywhere equality, the descended mass with
  strict positivity by construction, and the bridge on the quotient
  side — the open-class map is order-continuous exactly by
  τ-additivity.
* `Pointfree.Measure.SubProbability`, `Pointfree.Valuation.BridgeContinuity`,
  `Pointfree.Valuation.EscapeWitness` — the classical subprobability
  carrier with its weak topology, continuity of the bridge into the
  narrow topology, and the point-free escape witness.
* `Pointfree.Frame.Presentation` — frames presented by generators and
  relations: the free frame on a meet-semilattice of generators (its
  lower-set lattice), the least nucleus forcing a relation set, the
  presented frame as the nucleus's range, and the free interface —
  generator meets, top, join-generation, `hom_ext`.
* `Pointfree.Frame.HyperspacePresentation` — the hyperspace locale of
  hit-and-miss observations, presented: formal ∇-data over a base
  geometry, the Fell/Vietoris relation families, and the localic
  Choquet–Matheron determination theorem — Scott-continuous valuations
  with finite generator values are determined by (and distinct ones
  separated at) the ∇-generators.  No points, no countability.
* `Pointfree.Valuation.Determination` — the determination engine,
  frame-generally: modularity propagates generator agreement through
  finite joins (inclusion–exclusion with sharp finiteness — finite
  generator values, not finite mass), Scott continuity closes directed
  joins.
* `Pointfree.Valuation.SpatialDetermination` — the same theorem at the
  frame of opens of any space (a meet-closed topological basis
  determines), and the measure-level tie through the bridge:
  τ-additive restrictions of Borel measures agreeing on a basis agree
  on every open.
-/
