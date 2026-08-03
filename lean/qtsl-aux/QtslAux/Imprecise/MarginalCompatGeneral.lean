import QtslAux.Imprecise.MarginalCompat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Marginal compatibility penalties, general form

This module restates the additive/sup penalty calculus of
`QtslAux.Imprecise.MarginalCompat` for an arbitrary type `J` of joint
models and arbitrary types `Mi i` of marginal models, so that only the marginal
maps `m : ∀ i, J → Mi i` matter.

* `compositePenaltyG`, `supPenaltyG`, `compositePenaltyWG`: the additive, sup,
  and weighted aggregations of the per-marginal penalties `f i (m i ν)`, valued
  in `ENNRat`.
* Domination and sublevel results mirror the finite-PMF case:
  `penalty_marginal_dominationG`, `sum_dominates_supG`, `supPenaltyG_le_iff`,
  `sublevel_marginalG`, `sublevel_marginal_of_dominatesG`, and the indicator
  evaluation `compositePenaltyG_indicator`.
* `compositePenaltyG_eq_finite`: on finite PMF models the general composite
  penalty agrees definitionally with `compositePenalty`.
* The `ProbabilityMeasure` section instantiates the calculus with
  measure-theoretic marginals: `pmMarginal proj hproj i ν` is the pushforward
  of `ν : ProbabilityMeasure X` along a measurable projection, and
  `pmCompositePenalty` together with `pm_penalty_marginal_domination`,
  `pm_sublevel_marginal`, `pm_sum_dominates_sup`, and
  `pm_sublevel_marginal_of_dominates` transfers the domination and sublevel
  lemmas to this setting.
-/

namespace Qtsl.Imprecise

open Finset

section General

variable {ι : Type*} [Fintype ι] {J : Type*} {Mi : ι → Type*}

def compositePenaltyG (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat)
    (ν : J) : ENNRat :=
  ∑ i, f i (m i ν)

def supPenaltyG (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat)
    (ν : J) : ENNRat :=
  univ.sup fun i => f i (m i ν)

def compositePenaltyWG (c : ι → ENNRat) (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) : ENNRat :=
  ∑ i, c i * f i (m i ν)

@[simp] theorem compositePenaltyWG_one (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) :
    compositePenaltyWG (fun _ => 1) m f ν = compositePenaltyG m f ν := by
  unfold compositePenaltyWG compositePenaltyG
  simp

theorem penalty_marginal_dominationG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) (i : ι) :
    f i (m i ν) ≤ compositePenaltyG m f ν :=
  Finset.single_le_sum (f := fun j => f j (m j ν))
    (fun _ _ => ENNRat.zero_le' _) (mem_univ i)

theorem penalty_marginal_domination_twoG {A B : Type*}
    (f₁ : A → ENNRat) (f₂ : B → ENNRat)
    (ma : J → A) (mb : J → B) (ν : J) :
    f₁ (ma ν) ≤ f₁ (ma ν) + f₂ (mb ν) :=
  le_self_add

theorem sum_dominates_supG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) :
    supPenaltyG m f ν ≤ compositePenaltyG m f ν :=
  Finset.sup_le fun i _ => penalty_marginal_dominationG m f ν i

theorem supPenaltyG_le_iff (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) {F : ENNRat} :
    supPenaltyG m f ν ≤ F ↔ ∀ i, f i (m i ν) ≤ F := by
  unfold supPenaltyG
  simp [Finset.sup_le_iff]

theorem weighted_penalty_marginal_dominationG (c : ι → ENNRat)
    (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (ν : J) (i : ι) :
    c i * f i (m i ν) ≤ compositePenaltyWG c m f ν :=
  Finset.single_le_sum (f := fun j => c j * f j (m j ν))
    (fun _ _ => ENNRat.zero_le' _) (mem_univ i)

theorem weighted_penalty_marginal_dominationG_of_one_le (c : ι → ENNRat)
    (m : ∀ i, J → Mi i) (f : ∀ i, Mi i → ENNRat) (ν : J) (i : ι)
    (hc : 1 ≤ c i) :
    f i (m i ν) ≤ compositePenaltyWG c m f ν :=
  calc f i (m i ν) = 1 * f i (m i ν) := (one_mul _).symm
    _ ≤ c i * f i (m i ν) :=
        mul_le_mul_of_nonneg_right hc (ENNRat.zero_le' _)
    _ ≤ compositePenaltyWG c m f ν :=
        weighted_penalty_marginal_dominationG c m f ν i

theorem sublevel_marginalG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) (ν : J) (i : ι) {t : ENNRat}
    (h : compositePenaltyG m f ν ≤ t) : f i (m i ν) ≤ t :=
  (penalty_marginal_dominationG m f ν i).trans h

theorem sublevel_marginal_of_dominatesG (m : ∀ i, J → Mi i)
    (f : ∀ i, Mi i → ENNRat) {F : J → ENNRat} {ν : J}
    (hdom : supPenaltyG m f ν ≤ F ν) {t : ENNRat}
    (h : F ν ≤ t) (i : ι) : f i (m i ν) ≤ t :=
  ((supPenaltyG_le_iff m f ν).mp hdom i).trans h

theorem compositePenaltyG_indicator (m : ∀ i, J → Mi i)
    (P : ∀ i, Mi i → Prop) [∀ i p, Decidable (P i p)] (ν : J) :
    compositePenaltyG m (fun i p => if P i p then 0 else ⊤) ν
      = if ∀ i, P i (m i ν) then 0 else ⊤ := by
  unfold compositePenaltyG
  by_cases h : ∀ i, P i (m i ν)
  · rw [if_pos h]
    exact Finset.sum_eq_zero fun i _ => if_pos (h i)
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hle := Finset.single_le_sum
      (f := fun i => if P i (m i ν) then (0 : ENNRat) else ⊤)
      (fun i _ => ENNRat.zero_le' _) (mem_univ j)
    rw [if_neg hj] at hle
    exact top_le_iff.mp hle

theorem compositePenaltyG_eq_finite {X : Type*} [Fintype X]
    {Xi : ι → Type*} [∀ i, Fintype (Xi i)]
    (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) :
    compositePenaltyG m f ν = compositePenalty m f ν :=
  rfl

end General

section ProbabilityMeasure

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [MeasurableSpace X]
variable {Xi : ι → Type*} [∀ i, MeasurableSpace (Xi i)]

noncomputable def pmMarginal (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i)) (i : ι)
    (ν : ProbabilityMeasure X) : ProbabilityMeasure (Xi i) :=
  ν.map (f := proj i) (hproj i).aemeasurable

noncomputable def pmCompositePenalty (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat)
    (ν : ProbabilityMeasure X) : ENNRat :=
  compositePenaltyG (pmMarginal proj hproj) f ν

theorem pm_penalty_marginal_domination (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat)
    (ν : ProbabilityMeasure X) (i : ι) :
    f i (pmMarginal proj hproj i ν) ≤ pmCompositePenalty proj hproj f ν :=
  penalty_marginal_dominationG (pmMarginal proj hproj) f ν i

theorem pm_sublevel_marginal (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat)
    (ν : ProbabilityMeasure X) (i : ι) {t : ENNRat}
    (h : pmCompositePenalty proj hproj f ν ≤ t) :
    f i (pmMarginal proj hproj i ν) ≤ t :=
  sublevel_marginalG (pmMarginal proj hproj) f ν i h

theorem pm_sum_dominates_sup (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat)
    (ν : ProbabilityMeasure X) :
    supPenaltyG (pmMarginal proj hproj) f ν
      ≤ pmCompositePenalty proj hproj f ν :=
  sum_dominates_supG (pmMarginal proj hproj) f ν

theorem pm_sublevel_marginal_of_dominates (proj : ∀ i, X → Xi i)
    (hproj : ∀ i, Measurable (proj i))
    (f : ∀ i, ProbabilityMeasure (Xi i) → ENNRat)
    {F : ProbabilityMeasure X → ENNRat} {ν : ProbabilityMeasure X}
    (hdom : supPenaltyG (pmMarginal proj hproj) f ν ≤ F ν) {t : ENNRat}
    (h : F ν ≤ t) (i : ι) :
    f i (pmMarginal proj hproj i ν) ≤ t :=
  sublevel_marginal_of_dominatesG (pmMarginal proj hproj) f hdom h i

end ProbabilityMeasure

end Qtsl.Imprecise
