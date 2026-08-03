import QtslAux.Imprecise.Credal
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Order
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! # Marginal compatibility penalties over finite models

This module builds the penalty calculus used to express that a single joint
model must be simultaneously compatible with several marginal constraints.

* `FinPMF.map g p`: the pushforward of a finite PMF along `g : X → Y`, with the
  change-of-variables identity `FinPMF.exp_map`.
* `ENNRat`: the extended nonnegative rationals `WithTop ℚ≥0`, the value carrier
  for penalties.
* `compositePenalty m f ν = ∑ i, f i (m i ν)` and `supPenalty`: the additive and
  supremum aggregations of per-marginal penalties `f i` applied to the marginal
  models `m i ν`; `compositePenaltyW` is the weighted additive form.

The main results are domination and sublevel lemmas: each marginal penalty is
dominated by the composite (`penalty_marginal_domination` and the weighted
variants), the sup is dominated by the sum (`sum_dominates_sup`), and a bound on
the composite yields a bound on every marginal (`sublevel_marginal`,
`sublevel_marginal_of_dominates`). `compositePenalty_indicator` evaluates the
composite of `{0, ⊤}`-valued indicator penalties as the indicator of the
conjunction of the marginal predicates. The `Counterexamples` section shows the
hypotheses are sharp: `signed_relaxation_fails` (signed penalties break
domination) and `subunit_weight_fails` (weights below `1` break it).
-/

namespace Qtsl.Imprecise

open Finset
open scoped NNRat

abbrev ENNRat : Type := WithTop ℚ≥0

theorem ENNRat.zero_le' (a : ENNRat) : 0 ≤ a := zero_le

section Map

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

def FinPMF.map (g : X → Y) (p : FinPMF X) : FinPMF Y where
  prob := fun y => ∑ x ∈ univ.filter fun x => g x = y, p.prob x
  nonneg := fun _ => Finset.sum_nonneg fun x _ => p.nonneg x
  total := by
    rw [← p.total]
    exact Finset.sum_fiberwise univ g p.prob

theorem FinPMF.exp_map (g : X → Y) (p : FinPMF X) (h : Y → ℚ) :
    (p.map g).exp h = p.exp fun x => h (g x) := by
  unfold FinPMF.exp FinPMF.map
  calc ∑ y, (∑ x ∈ univ.filter fun x => g x = y, p.prob x) * h y
      = ∑ y, ∑ x ∈ univ.filter fun x => g x = y, p.prob x * h (g x) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x hx => by
          rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x, p.prob x * h (g x) :=
        Finset.sum_fiberwise univ g fun x => p.prob x * h (g x)

end Map

section Penalty

variable {ι : Type*} [Fintype ι] {X : Type*} [Fintype X]
variable {Xi : ι → Type*} [∀ i, Fintype (Xi i)]

def compositePenalty (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) : ENNRat :=
  ∑ i, f i (m i ν)

def supPenalty (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) : ENNRat :=
  univ.sup fun i => f i (m i ν)

def compositePenaltyW (c : ι → ENNRat) (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) : ENNRat :=
  ∑ i, c i * f i (m i ν)

@[simp] theorem compositePenaltyW_one (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) :
    compositePenaltyW (fun _ => 1) m f ν = compositePenalty m f ν := by
  unfold compositePenaltyW compositePenalty
  simp

theorem penalty_marginal_domination (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) (i : ι) :
    f i (m i ν) ≤ compositePenalty m f ν :=
  Finset.single_le_sum (f := fun j => f j (m j ν))
    (fun _ _ => ENNRat.zero_le' _) (mem_univ i)

theorem penalty_marginal_domination_two {A B : Type*} [Fintype A] [Fintype B]
    (f₁ : FinPMF A → ENNRat) (f₂ : FinPMF B → ENNRat)
    (ma : FinPMF X → FinPMF A) (mb : FinPMF X → FinPMF B) (ν : FinPMF X) :
    f₁ (ma ν) ≤ f₁ (ma ν) + f₂ (mb ν) :=
  le_self_add

theorem sum_dominates_sup (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) :
    supPenalty m f ν ≤ compositePenalty m f ν :=
  Finset.sup_le fun i _ => penalty_marginal_domination m f ν i

theorem supPenalty_le_iff (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) {F : ENNRat} :
    supPenalty m f ν ≤ F ↔ ∀ i, f i (m i ν) ≤ F := by
  unfold supPenalty
  simp [Finset.sup_le_iff]

theorem weighted_penalty_marginal_domination (c : ι → ENNRat)
    (m : ∀ i, FinPMF X → FinPMF (Xi i)) (f : ∀ i, FinPMF (Xi i) → ENNRat)
    (ν : FinPMF X) (i : ι) :
    c i * f i (m i ν) ≤ compositePenaltyW c m f ν :=
  Finset.single_le_sum (f := fun j => c j * f j (m j ν))
    (fun _ _ => ENNRat.zero_le' _) (mem_univ i)

theorem weighted_penalty_marginal_domination_of_one_le (c : ι → ENNRat)
    (m : ∀ i, FinPMF X → FinPMF (Xi i)) (f : ∀ i, FinPMF (Xi i) → ENNRat)
    (ν : FinPMF X) (i : ι) (hc : 1 ≤ c i) :
    f i (m i ν) ≤ compositePenaltyW c m f ν :=
  calc f i (m i ν) = 1 * f i (m i ν) := (one_mul _).symm
    _ ≤ c i * f i (m i ν) :=
        mul_le_mul_of_nonneg_right hc (ENNRat.zero_le' _)
    _ ≤ compositePenaltyW c m f ν :=
        weighted_penalty_marginal_domination c m f ν i

theorem sublevel_marginal (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) (ν : FinPMF X) (i : ι) {t : ENNRat}
    (h : compositePenalty m f ν ≤ t) : f i (m i ν) ≤ t :=
  (penalty_marginal_domination m f ν i).trans h

theorem sublevel_marginal_of_dominates (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ENNRat) {F : FinPMF X → ENNRat} {ν : FinPMF X}
    (hdom : supPenalty m f ν ≤ F ν) {t : ENNRat}
    (h : F ν ≤ t) (i : ι) : f i (m i ν) ≤ t :=
  ((supPenalty_le_iff m f ν).mp hdom i).trans h

theorem compositePenalty_indicator (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (P : ∀ i, FinPMF (Xi i) → Prop) [∀ i p, Decidable (P i p)]
    (ν : FinPMF X) :
    compositePenalty m (fun i p => if P i p then 0 else ⊤) ν
      = if ∀ i, P i (m i ν) then 0 else ⊤ := by
  unfold compositePenalty
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

end Penalty

section Counterexamples

variable {ι : Type*} [Fintype ι] {X : Type*} [Fintype X]
variable {Xi : ι → Type*} [∀ i, Fintype (Xi i)]

def compositePenaltyQ (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ℚ) (ν : FinPMF X) : ℚ :=
  ∑ i, f i (m i ν)

def compositePenaltyWQ (c : ι → ℚ) (m : ∀ i, FinPMF X → FinPMF (Xi i))
    (f : ∀ i, FinPMF (Xi i) → ℚ) (ν : FinPMF X) : ℚ :=
  ∑ i, c i * f i (m i ν)

def deltaOne : FinPMF (Fin 2) where
  prob := fun j => if j = 1 then 1 else 0
  nonneg := fun j => by by_cases hj : j = 1 <;> simp [hj]
  total := by simp

theorem signed_relaxation_fails :
    ∃ f : Fin 2 → FinPMF (Fin 2) → ℚ,
      ¬ ∀ (i : Fin 2) (ν : FinPMF (Fin 2)),
          f i ν ≤ compositePenaltyQ (Xi := fun _ => Fin 2)
            (fun _ ν => ν) f ν := by
  refine ⟨fun i p => if i = 0 then 2 * p.prob 1 else -(p.prob 1),
    fun hdom => ?_⟩
  have h := hdom 0 deltaOne
  norm_num [compositePenaltyQ, Fin.sum_univ_two, deltaOne] at h

theorem subunit_weight_fails :
    ∃ (c : Fin 1 → ℚ) (f : Fin 1 → FinPMF (Fin 2) → ℚ),
      (∀ i ν, 0 ≤ f i ν) ∧ (∀ i, 0 ≤ c i) ∧
      ¬ ∀ (i : Fin 1) (ν : FinPMF (Fin 2)),
          f i ν ≤ compositePenaltyWQ (Xi := fun _ => Fin 2) c
            (fun _ ν => ν) f ν := by
  refine ⟨fun _ => 1/2, fun _ p => 2 * p.prob 1,
    fun i ν => mul_nonneg (by norm_num) (ν.nonneg 1),
    fun _ => by norm_num, fun hdom => ?_⟩
  have h := hdom 0 deltaOne
  norm_num [compositePenaltyWQ, Fin.sum_univ_one, deltaOne] at h

end Counterexamples

end Qtsl.Imprecise
