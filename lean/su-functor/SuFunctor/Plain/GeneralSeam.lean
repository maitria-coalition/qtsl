import Mathlib.MeasureTheory.Measure.Dirac
import SuFunctor.Plain.MeasJoint

/-! # The seam: the finite stratum is a sub-instance of the general one

`SuFunctor.Plain.Seam` identifies the exact stratum's joints with the
judgment tier's distributions over a finite carrier.  This module runs
the other seam, upward in generality: every finitely supported joint
*is* a subprobability Borel measure — the weighted sum of point masses
on its support — and the identification respects the whole calculus:

* `Joint.toMeas` — the embedding, `μ ↦ ∑ᵢ μ.wt i • δᵢ`, with the mass
  correspondence (`toMeas_mass`), the zero joint to the zero measure
  (`toMeas_zero`), and injectivity over carriers with measurable
  singletons (`toMeas_injective`: evaluation at singletons recovers
  the weights);
* `toMeas_push` — **the restriction theorem**: pushforward at the
  finite stratum is the restriction of measure-theoretic pushforward
  along the embedding, for measurable carrier maps;
* `pull_toMeas` / `image_pull_toMeas` — the penalty-level and
  class-level corollaries: transporting a general-stratum penalty
  (class) and then restricting along the seam is restricting and then
  transporting at the finite stratum — the finite decoration functor
  is the restriction of the general one along the seam.

Together with `SuFunctor.Plain.Seam` this makes the two mechanized
strata of the composition tier two presentations of one object *and*
nested: exact ⊆ general, with the judgment tier's finite carrier the
common ground floor.
-/

namespace SuFunctor

namespace Plain

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

namespace Joint

/-- The measure of a finitely supported joint: the weighted sum of
point masses on its support. -/
def measSum (μ : Joint X) : Measure X :=
  μ.wt.sum fun i w => ((w : ℝ≥0∞) • Measure.dirac i : Measure X)

theorem measSum_apply (μ : Joint X) {s : Set X} (hs : MeasurableSet s) :
    measSum μ s =
      ∑ i ∈ μ.wt.support, (μ.wt i : ℝ≥0∞) * s.indicator 1 i := by
  classical
  simp only [measSum, Finsupp.sum]
  rw [Measure.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' i hs]

theorem measSum_univ (μ : Joint X) :
    measSum μ Set.univ = ((μ.wt.sum fun _ v => v : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [measSum_apply μ MeasurableSet.univ]
  simp only [Finsupp.sum]
  rw [ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Set.indicator_of_mem (Set.mem_univ i), Pi.one_apply, mul_one]

instance (μ : Joint X) : IsFiniteMeasure (measSum μ) :=
  ⟨by rw [measSum_univ]; exact ENNReal.coe_lt_top⟩

/-- **The seam embedding**: a finitely supported joint, read as a
subprobability Borel measure — the weighted sum of point masses on its
support. -/
def toMeas (μ : Joint X) : MeasJoint X :=
  ⟨⟨measSum μ, inferInstance⟩, by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, ENNReal.coe_one]
    show measSum μ Set.univ ≤ 1
    rw [measSum_univ]
    exact_mod_cast μ.mass_le_one⟩

@[simp] theorem toMeas_toMeasure (μ : Joint X) :
    ((toMeas μ).1 : Measure X) = measSum μ := rfl

/-- **Mass correspondence**: the measure-theoretic mass of the image is
the finsupp mass of the source. -/
theorem toMeas_mass (μ : Joint X) :
    (toMeas μ).1.mass = μ.wt.sum fun _ v => v := by
  rw [← ENNReal.coe_inj, FiniteMeasure.ennreal_mass, toMeas_toMeasure,
    measSum_univ]

/-- Zero goes to zero: total mass loss is the same point in both
presentations. -/
theorem toMeas_zero : toMeas (Joint.zero X) = MeasJoint.zero X := by
  refine MeasJoint.ext' ?_
  simp [measSum]

/-- Evaluation at a measurable singleton recovers the weight. -/
theorem toMeas_singleton [MeasurableSingletonClass X] (μ : Joint X)
    (i : X) : ((toMeas μ).1 : Measure X) {i} = (μ.wt i : ℝ≥0∞) := by
  classical
  rw [toMeas_toMeasure, measSum_apply μ (measurableSet_singleton i)]
  by_cases hi : i ∈ μ.wt.support
  · rw [Finset.sum_eq_single i
      (fun j _ hne => by
        rw [Set.indicator_of_notMem (by simpa using hne), mul_zero])
      (fun h => absurd hi h)]
    rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl), Pi.one_apply,
      mul_one]
  · rw [Finsupp.notMem_support_iff.mp hi, ENNReal.coe_zero]
    exact Finset.sum_eq_zero fun j hj => by
      rcases eq_or_ne j i with rfl | hne
      · exact absurd hj hi
      · rw [Set.indicator_of_notMem (by simpa using hne), mul_zero]

/-- **Injectivity**: over a carrier with measurable singletons, the
seam embedding loses nothing. -/
theorem toMeas_injective [MeasurableSingletonClass X] :
    Function.Injective (toMeas : Joint X → MeasJoint X) := by
  intro μ ν h
  refine Joint.ext (Finsupp.ext fun i => ?_)
  have h' := congrArg (fun m : MeasJoint X => (m.1 : Measure X) {i}) h
  rw [toMeas_singleton, toMeas_singleton] at h'
  exact_mod_cast h'

/-- **The restriction theorem**: pushforward at the finite stratum is
measure-theoretic pushforward restricted along the seam — for
measurable carrier maps, the square of `Joint.push`, `MeasJoint.push`,
and the two embeddings commutes. -/
theorem toMeas_push (h : X → Y) (hm : Measurable h) (μ : Joint X) :
    toMeas (μ.push h) = (toMeas μ).push h := by
  refine MeasJoint.ext' ?_
  rw [MeasJoint.push_toMeasure, toMeas_toMeasure, toMeas_toMeasure]
  show measSum (μ.push h) = (measSum μ).map h
  simp only [measSum, Joint.push_wt]
  rw [Finsupp.sum_mapDomain_index
    (fun b => by rw [ENNReal.coe_zero, zero_smul])
    (fun b w₁ w₂ => by rw [ENNReal.coe_add, add_smul])]
  rw [← Measure.mapₗ_apply_of_measurable hm]
  simp only [Finsupp.sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Measure.mapₗ_apply_of_measurable hm, Measure.map_smul,
      Measure.map_dirac' hm]

/-- **Penalty restriction**: transporting a general-stratum penalty and
restricting along the seam is restricting and then transporting at the
finite stratum. -/
theorem pull_toMeas (h : X → Y) (hm : Measurable h) (F : MeasPen Y) :
    (MeasPen.pull h F) ∘ toMeas = Pen.pull h (F ∘ toMeas) := by
  funext μ
  simp only [Function.comp_apply, MeasPen.pull_apply, Pen.pull_apply]
  exact (congrArg F (toMeas_push h hm μ)).symm

/-- **Class restriction**: the finite decoration functor's tight
transport is the restriction of the general one along the seam, at the
level of spec classes. -/
theorem image_pull_toMeas (h : X → Y) (hm : Measurable h)
    (𝒮 : Set (MeasPen Y)) :
    (fun F => F ∘ toMeas) '' (MeasPen.pull h '' 𝒮) =
      Pen.pull h '' ((fun F => F ∘ toMeas) '' 𝒮) := by
  rw [← Set.image_comp, ← Set.image_comp]
  exact congrArg (· '' 𝒮) (funext fun F => pull_toMeas h hm F)

end Joint

end

end Plain

end SuFunctor
