import Pointfree.Valuation.Functor
import Pointfree.Valuation.Bridge

/-! # The bridge is a natural transformation of functors

The continuous-map face of `Pointfree.Valuation.Functor`: precomposing
the frame-level pushforward with `Opens.comap` gives the covariant
pushforward `SubProb.push` along a continuous map, and the two squares
that make the valuation storey a lawful layer over any base of spaces
both commute:

* the **unit square** (`SubProb.push_dirac`): pushforward of the Dirac
  at a point is the Dirac at the image point — proved once, over an
  arbitrary continuous map, at the frame level; every per-site shadow
  of it (pushforward of a Dirac measure along a clip or a transport
  map) is a substitution instance;
* the **bridge square** (`MeasureTheory.Measure.toSubProb_map`):
  restricting a pushforward measure to opens is transporting the
  restriction — `Measure.toValuation` is a natural transformation from
  the Borel-measure functor to the valuation functor.

Combining the two with the Dirac bridge collapses the classical
Dirac-naturality square into its point-free image
(`MeasureTheory.Measure.dirac_map_toValuation`): the valuation
restriction of `(Measure.dirac x).map f` is the point-free Dirac of the
transported frame point, with no measurability bookkeeping surviving
into the statement's right-hand side.  Scott continuity rides along
(`MeasureTheory.Measure.push_toSubProb_isScottContinuous`), with second
countability of the *source* as the honest hypothesis, exactly as in
the bridge module.
-/

namespace Pointfree

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace SubProb

/-- Covariant pushforward of subprobability valuations on opens, along
a continuous map: precomposition with the inverse-image frame
homomorphism. -/
def push (f : C(X, Y)) : SubProb (Opens X) → SubProb (Opens Y) :=
  SubProb.map (Opens.comap f)

@[simp] theorem push_apply (f : C(X, Y)) (μ : SubProb (Opens X)) (U : Opens Y) :
    push f μ U = μ (Opens.comap f U) := rfl

@[simp] theorem push_id :
    (push (ContinuousMap.id X) : SubProb (Opens X) → SubProb (Opens X)) = id := by
  funext μ
  show SubProb.map (Opens.comap (ContinuousMap.id X)) μ = μ
  rw [Opens.comap_id, SubProb.map_id]

theorem push_comp (g : C(Y, Z)) (f : C(X, Y)) (μ : SubProb (Opens X)) :
    push (g.comp f) μ = push g (push f μ) := by
  show SubProb.map (Opens.comap (g.comp f)) μ
      = SubProb.map (Opens.comap g) (SubProb.map (Opens.comap f) μ)
  rw [Opens.comap_comp, SubProb.map_comp]

/-- Pushforward along a continuous map is continuous for the narrow
topologies. -/
theorem continuous_push (f : C(X, Y)) : Continuous (push f) :=
  SubProb.continuous_map (Opens.comap f)

end SubProb

/-- Frame points transport covariantly along continuous maps: the point
of `x` precomposed with inverse images is the point of `f x`. -/
theorem pointHom_comap (f : C(X, Y)) (x : X) :
    (pointHom x).comp (Opens.comap f) = pointHom (f x) := by
  refine FrameHom.ext fun U => ?_
  show ((x ∈ Opens.comap f U) = (f x ∈ U))
  apply propext
  rw [← SetLike.mem_coe, Opens.coe_comap]
  exact Iff.rfl

/-- **The unit square, point-free**: pushforward of the Dirac at a
point is the Dirac at the image point — for an arbitrary continuous
map, by substitution at the frame level.  Site-indexed shadows of this
square (Dirac naturality along clips, restrictions, transports) are
instances. -/
theorem SubProb.push_dirac (f : C(X, Y)) (x : X) :
    SubProb.push f (SubProb.dirac (pointHom x)) = SubProb.dirac (pointHom (f x)) := by
  rw [SubProb.push, SubProb.map_dirac, pointHom_comap]

variable [MeasurableSpace X] [OpensMeasurableSpace X]
variable [MeasurableSpace Y] [BorelSpace Y]

/-- Pushforward preserves the subprobability bound on total mass. -/
theorem _root_.MeasureTheory.Measure.map_univ_le_one (μ : Measure X) {f : X → Y}
    (hf : Continuous f) (h : μ Set.univ ≤ 1) : μ.map f Set.univ ≤ 1 := by
  rw [Measure.map_apply hf.measurable MeasurableSet.univ, Set.preimage_univ]
  exact h

/-- **The bridge square on carriers**: restricting a pushforward
measure to opens is pushing the restriction forward —
`Measure.toSubProb` is natural in continuous maps. -/
theorem _root_.MeasureTheory.Measure.toSubProb_map (μ : Measure X) {f : X → Y}
    (hf : Continuous f) (h : μ Set.univ ≤ 1) :
    (μ.map f).toSubProb (μ.map_univ_le_one hf h)
      = SubProb.push ⟨f, hf⟩ (μ.toSubProb h) := by
  ext U
  exact DFunLike.congr_fun (μ.toValuation_map hf) U

/-- **The point-set Dirac square, re-derived as the image of the
bridge**: the valuation restriction of a pushforward Dirac measure is
the point-free Dirac of the transported frame point.  This is the
general statement whose instance at a hyperspace clip map is the
mechanized shadow of the valuation layer's unit square; the point-free
right-hand side carries no measurability data. -/
theorem _root_.MeasureTheory.Measure.dirac_map_toValuation {f : X → Y}
    (hf : Continuous f) (x : X) :
    ((Measure.dirac x).map f).toValuation = Valuation.dirac (pointHom (f x)) := by
  rw [(Measure.dirac x).toValuation_map hf, dirac_toValuation,
    Valuation.map_dirac, pointHom_comap]
  simp only [ContinuousMap.coe_mk]

/-- The two classical routes around the Dirac square have equal
valuation images: push-then-restrict agrees with restrict-at-the-image.
(The measure-level equality is `Measure.map_dirac'`; this is its
point-free shadow, obtained without invoking it.) -/
theorem _root_.MeasureTheory.Measure.map_dirac_toValuation_eq {f : X → Y}
    (hf : Continuous f) (x : X) :
    ((Measure.dirac x).map f).toValuation = (Measure.dirac (f x)).toValuation := by
  rw [Measure.dirac_map_toValuation hf, dirac_toValuation]

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **Scott continuity rides the bridge and transports along
pushforward**: on a second-countable source, the pushforward of a
restricted measure is a Scott-continuous subprobability valuation.
Second countability of the *source* is the honest hypothesis — it is
where τ-additivity enters (Fremlin 414O), and the transported valuation
inherits continuity through `IsScottContinuous.map`, not from the
target. -/
theorem _root_.MeasureTheory.Measure.push_toSubProb_isScottContinuous
    [SecondCountableTopology X] (μ : Measure X) {f : X → Y}
    (hf : Continuous f) (h : μ Set.univ ≤ 1) :
    (SubProb.push ⟨f, hf⟩ (μ.toSubProb h)).toValuation.IsScottContinuous :=
  μ.toValuation_isScottContinuous.map (Opens.comap ⟨f, hf⟩)

end Pointfree
