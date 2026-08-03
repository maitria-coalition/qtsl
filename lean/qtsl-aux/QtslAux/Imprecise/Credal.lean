import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Finite credal sets and lower/upper expectations

This module develops finite-support imprecise probability with rational values.

* `FinPMF X`: a probability mass function on a finite type `X` with values in
  `ℚ` (fields `prob`, `nonneg`, `total`), with expectation `FinPMF.exp` and its
  algebraic laws (`exp_add`, `exp_smul`, `exp_neg`, `exp_const`, `exp_mono`,
  `exp_congr`).
* `lowerE M f` / `upperE M f`: the lower and upper expectations of `f : X → ℚ`
  over a credal set presented as a finite nonempty family `M : ι → FinPMF X`,
  defined as the minimum resp. maximum of the member expectations.

The main results are the coherence properties of these envelopes: attainment
(`exists_eq_lowerE`, `exists_eq_upperE`), superadditivity of `lowerE` and
subadditivity of `upperE` (`lowerE_superadd`, `upperE_subadd`), positive
homogeneity (`lowerE_smul`), monotonicity (`lowerE_mono`, `upperE_mono`),
evaluation on constants (`lowerE_const`, `upperE_const`), the order
`lowerE_le_upperE`, and the conjugacy `upperE_eq_neg_lowerE_neg`.
-/

namespace Qtsl.Imprecise

open Finset

structure FinPMF (X : Type*) [Fintype X] where

  prob : X → ℚ

  nonneg : ∀ x, 0 ≤ prob x

  total : ∑ x, prob x = 1

namespace FinPMF

variable {X : Type*} [Fintype X]

def exp (p : FinPMF X) (f : X → ℚ) : ℚ := ∑ x, p.prob x * f x

theorem exp_add (p : FinPMF X) (f g : X → ℚ) :
    p.exp (fun x => f x + g x) = p.exp f + p.exp g := by
  simp [exp, mul_add, Finset.sum_add_distrib]

theorem exp_smul (p : FinPMF X) (c : ℚ) (f : X → ℚ) :
    p.exp (fun x => c * f x) = c * p.exp f := by
  rw [exp, exp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _

theorem exp_neg (p : FinPMF X) (f : X → ℚ) :
    p.exp (fun x => -f x) = -p.exp f := by
  simp [exp]

theorem exp_const (p : FinPMF X) (c : ℚ) : p.exp (fun _ => c) = c := by
  rw [exp, ← Finset.sum_mul, p.total, one_mul]

theorem exp_mono (p : FinPMF X) {f g : X → ℚ} (h : ∀ x, f x ≤ g x) :
    p.exp f ≤ p.exp g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)

theorem exp_congr (p : FinPMF X) {f g : X → ℚ} (h : ∀ x, f x = g x) :
    p.exp f = p.exp g :=
  Finset.sum_congr rfl fun x _ => by rw [h x]

end FinPMF

section Credal

variable {X : Type*} [Fintype X] {ι : Type*} [Fintype ι] [Nonempty ι]

def lowerE (M : ι → FinPMF X) (f : X → ℚ) : ℚ :=
  univ.inf' univ_nonempty fun i => (M i).exp f

def upperE (M : ι → FinPMF X) (f : X → ℚ) : ℚ :=
  univ.sup' univ_nonempty fun i => (M i).exp f

theorem lowerE_le_exp (M : ι → FinPMF X) (f : X → ℚ) (i : ι) :
    lowerE M f ≤ (M i).exp f := by
  unfold lowerE
  exact Finset.inf'_le _ (mem_univ i)

theorem exp_le_upperE (M : ι → FinPMF X) (f : X → ℚ) (i : ι) :
    (M i).exp f ≤ upperE M f := by
  unfold upperE
  exact Finset.le_sup' (fun j => (M j).exp f) (mem_univ i)

theorem le_lowerE {M : ι → FinPMF X} {f : X → ℚ} {a : ℚ}
    (h : ∀ i, a ≤ (M i).exp f) : a ≤ lowerE M f := by
  unfold lowerE
  exact Finset.le_inf' _ _ fun i _ => h i

theorem upperE_le {M : ι → FinPMF X} {f : X → ℚ} {a : ℚ}
    (h : ∀ i, (M i).exp f ≤ a) : upperE M f ≤ a := by
  unfold upperE
  exact Finset.sup'_le _ _ fun i _ => h i

theorem exists_eq_lowerE (M : ι → FinPMF X) (f : X → ℚ) :
    ∃ i, lowerE M f = (M i).exp f := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' (univ_nonempty) fun i => (M i).exp f
  exact ⟨i, h⟩

theorem exists_eq_upperE (M : ι → FinPMF X) (f : X → ℚ) :
    ∃ i, upperE M f = (M i).exp f := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (univ_nonempty) fun i => (M i).exp f
  exact ⟨i, h⟩

theorem lowerE_congr {M : ι → FinPMF X} {f g : X → ℚ} (h : ∀ x, f x = g x) :
    lowerE M f = lowerE M g := by
  unfold lowerE
  exact Finset.inf'_congr _ rfl fun i _ => (M i).exp_congr h

theorem upperE_congr {M : ι → FinPMF X} {f g : X → ℚ} (h : ∀ x, f x = g x) :
    upperE M f = upperE M g := by
  unfold upperE
  exact Finset.sup'_congr _ rfl fun i _ => (M i).exp_congr h

theorem lowerE_superadd (M : ι → FinPMF X) (f g : X → ℚ) :
    lowerE M f + lowerE M g ≤ lowerE M (fun x => f x + g x) :=
  le_lowerE fun i => by
    rw [FinPMF.exp_add]
    exact add_le_add (lowerE_le_exp M f i) (lowerE_le_exp M g i)

theorem upperE_subadd (M : ι → FinPMF X) (f g : X → ℚ) :
    upperE M (fun x => f x + g x) ≤ upperE M f + upperE M g :=
  upperE_le fun i => by
    rw [FinPMF.exp_add]
    exact add_le_add (exp_le_upperE M f i) (exp_le_upperE M g i)

theorem lowerE_smul (M : ι → FinPMF X) {c : ℚ} (hc : 0 ≤ c) (f : X → ℚ) :
    lowerE M (fun x => c * f x) = c * lowerE M f := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_lowerE M f
    calc lowerE M (fun x => c * f x) ≤ (M i).exp (fun x => c * f x) :=
          lowerE_le_exp M _ i
      _ = c * (M i).exp f := (M i).exp_smul c f
      _ = c * lowerE M f := by rw [← hi]
  · refine le_lowerE fun i => ?_
    rw [(M i).exp_smul c f]
    exact mul_le_mul_of_nonneg_left (lowerE_le_exp M f i) hc

theorem inf_le_lowerE [Nonempty X] (M : ι → FinPMF X) (f : X → ℚ) :
    (univ.inf' univ_nonempty f) ≤ lowerE M f :=
  le_lowerE fun i =>
    calc univ.inf' univ_nonempty f
        = (M i).exp (fun _ => univ.inf' univ_nonempty f) :=
          ((M i).exp_const _).symm
      _ ≤ (M i).exp f := (M i).exp_mono fun x => Finset.inf'_le _ (mem_univ x)

theorem lowerE_const (M : ι → FinPMF X) (c : ℚ) :
    lowerE M (fun _ => c) = c := by
  obtain ⟨i, hi⟩ := exists_eq_lowerE M (fun _ => c)
  rw [hi, (M i).exp_const]

theorem upperE_const (M : ι → FinPMF X) (c : ℚ) :
    upperE M (fun _ => c) = c := by
  obtain ⟨i, hi⟩ := exists_eq_upperE M (fun _ => c)
  rw [hi, (M i).exp_const]

theorem lowerE_mono (M : ι → FinPMF X) {f g : X → ℚ} (h : ∀ x, f x ≤ g x) :
    lowerE M f ≤ lowerE M g := by
  obtain ⟨i, hi⟩ := exists_eq_lowerE M g
  rw [hi]
  exact (lowerE_le_exp M f i).trans ((M i).exp_mono h)

theorem upperE_mono (M : ι → FinPMF X) {f g : X → ℚ} (h : ∀ x, f x ≤ g x) :
    upperE M f ≤ upperE M g := by
  obtain ⟨i, hi⟩ := exists_eq_upperE M f
  rw [hi]
  exact ((M i).exp_mono h).trans (exp_le_upperE M g i)

theorem lowerE_le_upperE (M : ι → FinPMF X) (f : X → ℚ) :
    lowerE M f ≤ upperE M f :=
  (lowerE_le_exp M f (Classical.arbitrary ι)).trans
    (exp_le_upperE M f (Classical.arbitrary ι))

theorem upperE_eq_neg_lowerE_neg (M : ι → FinPMF X) (f : X → ℚ) :
    upperE M f = -lowerE M (fun x => -f x) := by
  apply le_antisymm
  · refine upperE_le fun i => ?_
    have h := lowerE_le_exp M (fun x => -f x) i
    rw [(M i).exp_neg] at h
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_lowerE M (fun x => -f x)
    rw [hi, (M i).exp_neg, neg_neg]
    exact exp_le_upperE M f i

end Credal

end Qtsl.Imprecise
