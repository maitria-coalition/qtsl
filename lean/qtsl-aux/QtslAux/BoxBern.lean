import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.MvPolynomial.Monad
import QtslAux.GridCx

/-! # Polynomial range enclosure from tensor Bernstein coefficients on a box

This module proves the fundamental enclosure property of the multivariate
Bernstein expansion: on an axis-aligned box, a polynomial is bounded between
the minimum and maximum of its Bernstein coefficients.

Main definitions:

* `tensorBern d α`: the tensor-product Bernstein basis polynomial of
  multidegree `d` and multi-index `α` over `ℚ`, a product of univariate
  Bernstein polynomials in each variable.
* `boxShift lo hi`: the algebra homomorphism substituting
  `X v ↦ lo v + (hi v - lo v) * X v`, pulling a polynomial on the box
  `[lo, hi]` back to the unit box.

Main results:

* `bernstein_eval_nonneg`, `sum_bernstein_eval`, `aeval_tensorBern_nonneg`,
  `sum_aeval_tensorBern`: the tensor Bernstein basis is a partition of unity
  with nonnegative values on the unit box.
* `enclosure_unit`: if `p = ∑ α, C (b α) * tensorBern d α` with
  `m ≤ b α ≤ M` for all `α`, then `m ≤ p(u) ≤ M` for every `u` in the unit
  box.
* `boxBern_enclosure`, `boxBern_enclosure_minmax`: the same enclosure on an
  arbitrary rational box `[lo, hi]`, obtained through `boxShift`; the min/max
  form takes `m` and `M` to be the extremal coefficients.
* `boxBern_nonpos`: nonpositive Bernstein coefficients certify `p ≤ 0` on
  the box — the certificate step used to discharge polynomial sign
  conditions.
-/

namespace Qtsl
namespace BoxBern

open MvPolynomial Finset

theorem bernstein_eval_nonneg (d i : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ (bernsteinPolynomial ℝ d i).eval x := by
  rw [bernsteinPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_natCast,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  have h2 : (0 : ℝ) ≤ 1 - x := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg h2 _)

theorem sum_bernstein_eval (d : ℕ) (x : ℝ) :
    ∑ i : Fin (d + 1), (bernsteinPolynomial ℝ d i).eval x = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (bernsteinPolynomial ℝ d k).eval x) (d + 1),
    ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

variable {n : ℕ}

noncomputable def tensorBern (d : Fin n → ℕ) (α : ∀ v, Fin (d v + 1)) :
    MvPolynomial (Fin n) ℚ :=
  ∏ v, Polynomial.aeval (X v) (bernsteinPolynomial ℚ (d v) (α v))

theorem aeval_tensorBern (d : Fin n → ℕ) (α : ∀ v, Fin (d v + 1))
    (u : Fin n → ℝ) :
    aeval u (tensorBern d α)
      = ∏ v, (bernsteinPolynomial ℝ (d v) (α v)).eval (u v) := by
  rw [tensorBern, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Polynomial.aeval_algHom_apply (aeval u) (X v)
      (bernsteinPolynomial ℚ (d v) (α v)),
    aeval_X, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    bernsteinPolynomial.map]

theorem aeval_tensorBern_nonneg (d : Fin n → ℕ) (α : ∀ v, Fin (d v + 1))
    {u : Fin n → ℝ} (hu : ∀ v, 0 ≤ u v ∧ u v ≤ 1) :
    0 ≤ aeval u (tensorBern d α) := by
  rw [aeval_tensorBern]
  exact Finset.prod_nonneg fun v _ =>
    bernstein_eval_nonneg (d v) (α v) (hu v).1 (hu v).2

theorem sum_aeval_tensorBern (d : Fin n → ℕ) (u : Fin n → ℝ) :
    ∑ α : ∀ v, Fin (d v + 1), aeval u (tensorBern d α) = 1 := by
  simp only [aeval_tensorBern]
  rw [← Fintype.prod_sum
    (f := fun v (i : Fin (d v + 1)) => (bernsteinPolynomial ℝ (d v) i).eval (u v))]
  exact Finset.prod_eq_one fun v _ => sum_bernstein_eval (d v) (u v)

theorem enclosure_unit (d : Fin n → ℕ) (b : (∀ v, Fin (d v + 1)) → ℚ)
    (p : MvPolynomial (Fin n) ℚ) (m M : ℚ)
    (hexp : p = ∑ α, C (b α) * tensorBern d α)
    (hm : ∀ α, m ≤ b α) (hM : ∀ α, b α ≤ M)
    (u : Fin n → ℝ) (hu : ∀ v, 0 ≤ u v ∧ u v ≤ 1) :
    (m : ℝ) ≤ aeval u p ∧ aeval u p ≤ (M : ℝ) := by
  have hw0 : ∀ α : ∀ v, Fin (d v + 1), 0 ≤ aeval u (tensorBern d α) :=
    fun α => aeval_tensorBern_nonneg d α hu
  have hw1 : ∑ α : ∀ v, Fin (d v + 1), aeval u (tensorBern d α) = 1 :=
    sum_aeval_tensorBern d u
  have hval : aeval u p
      = ∑ α, (b α : ℝ) * aeval u (tensorBern d α) := by
    rw [hexp, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul, aeval_C, eq_ratCast]
  rw [hval]
  constructor
  · calc (m : ℝ) = ∑ α : ∀ v, Fin (d v + 1),
          aeval u (tensorBern d α) * (m : ℝ) := by
          rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ ∑ α : ∀ v, Fin (d v + 1),
          aeval u (tensorBern d α) * (b α : ℝ) :=
          Finset.sum_le_sum fun α _ =>
            mul_le_mul_of_nonneg_left (by exact_mod_cast hm α) (hw0 α)
      _ = ∑ α, (b α : ℝ) * aeval u (tensorBern d α) :=
          Finset.sum_congr rfl fun α _ => mul_comm _ _
  · calc (∑ α, (b α : ℝ) * aeval u (tensorBern d α))
        = ∑ α : ∀ v, Fin (d v + 1),
          aeval u (tensorBern d α) * (b α : ℝ) :=
          Finset.sum_congr rfl fun α _ => mul_comm _ _
      _ ≤ ∑ α : ∀ v, Fin (d v + 1),
          aeval u (tensorBern d α) * (M : ℝ) :=
          Finset.sum_le_sum fun α _ =>
            mul_le_mul_of_nonneg_left (by exact_mod_cast hM α) (hw0 α)
      _ = (M : ℝ) := by rw [← Finset.sum_mul, hw1, one_mul]

noncomputable def boxShift (lo hi : Fin n → ℚ) :
    MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  bind₁ fun v => C (lo v) + (C (hi v) - C (lo v)) * X v

theorem aeval_boxShift (lo hi : Fin n → ℚ) (u : Fin n → ℝ)
    (N : MvPolynomial (Fin n) ℚ) :
    aeval u (boxShift lo hi N)
      = aeval (fun v => (lo v : ℝ) + ((hi v : ℝ) - (lo v : ℝ)) * u v) N := by
  have h := aeval_bind₁ (R := ℚ) u
    (fun v => C (lo v) + (C (hi v) - C (lo v)) * X v) N
  have hpt : (fun v => aeval u (C (lo v) + (C (hi v) - C (lo v)) * X v))
      = fun v => (lo v : ℝ) + ((hi v : ℝ) - (lo v : ℝ)) * u v := by
    funext v
    simp [eq_ratCast]
  rw [hpt] at h
  exact h

def ratBox (lo hi : Fin n → ℚ) : GridCx.Box n :=
  ⟨fun v => (lo v : ℝ), fun v => (hi v : ℝ)⟩

theorem exists_unit_scalar {a c x : ℝ} (h1 : a ≤ x) (h2 : x ≤ c) :
    ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ a + (c - a) * t = x := by
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    have hx : x = a := le_antisymm (h2.trans_eq heq.symm) h1
    rw [mul_zero, add_zero, hx]
  · refine ⟨(x - a) / (c - a), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr h1) (sub_pos.mpr hlt).le
    · rw [div_le_one (sub_pos.mpr hlt)]
      linarith
    · have hne : c - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have hcancel : (c - a) * ((x - a) / (c - a)) = x - a := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hne
      rw [hcancel]
      ring

theorem exists_unit_point (lo hi : Fin n → ℚ) {x : Fin n → ℝ}
    (hx : x ∈ (ratBox lo hi).set) :
    ∃ u : Fin n → ℝ, (∀ v, 0 ≤ u v ∧ u v ≤ 1) ∧
      ∀ v, (lo v : ℝ) + ((hi v : ℝ) - (lo v : ℝ)) * u v = x v := by
  have hx' : ∀ v, (lo v : ℝ) ≤ x v ∧ x v ≤ (hi v : ℝ) := hx
  have h : ∀ v, ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧
      (lo v : ℝ) + ((hi v : ℝ) - (lo v : ℝ)) * t = x v :=
    fun v => exists_unit_scalar (hx' v).1 (hx' v).2
  choose u hu1 hu2 using h
  exact ⟨u, hu1, hu2⟩

theorem boxBern_enclosure (lo hi : Fin n → ℚ) (N : MvPolynomial (Fin n) ℚ)
    (d : Fin n → ℕ) (b : (∀ v, Fin (d v + 1)) → ℚ) (m M : ℚ)
    (hexp : boxShift lo hi N = ∑ α, C (b α) * tensorBern d α)
    (hm : ∀ α, m ≤ b α) (hM : ∀ α, b α ≤ M) :
    ∀ x ∈ (ratBox lo hi).set, (m : ℝ) ≤ aeval x N ∧ aeval x N ≤ (M : ℝ) := by
  intro x hx
  obtain ⟨u, hu, hux⟩ := exists_unit_point lo hi hx
  have hxu : aeval x N = aeval u (boxShift lo hi N) := by
    rw [aeval_boxShift,
      show (fun v => (lo v : ℝ) + ((hi v : ℝ) - (lo v : ℝ)) * u v) = x
        from funext hux]
  rw [hxu]
  exact enclosure_unit d b _ m M hexp hm hM u hu

theorem boxBern_enclosure_minmax (lo hi : Fin n → ℚ)
    (N : MvPolynomial (Fin n) ℚ)
    (d : Fin n → ℕ) (b : (∀ v, Fin (d v + 1)) → ℚ)
    (hexp : boxShift lo hi N = ∑ α, C (b α) * tensorBern d α) :
    ∀ x ∈ (ratBox lo hi).set,
      ((Finset.univ.inf' Finset.univ_nonempty b : ℚ) : ℝ) ≤ aeval x N ∧
        aeval x N ≤ ((Finset.univ.sup' Finset.univ_nonempty b : ℚ) : ℝ) :=
  boxBern_enclosure lo hi N d b _ _ hexp
    (fun α => Finset.inf'_le b (Finset.mem_univ α))
    (fun α => Finset.le_sup' b (Finset.mem_univ α))

theorem boxBern_nonpos (lo hi : Fin n → ℚ) (N : MvPolynomial (Fin n) ℚ)
    (d : Fin n → ℕ) (b : (∀ v, Fin (d v + 1)) → ℚ)
    (hexp : boxShift lo hi N = ∑ α, C (b α) * tensorBern d α)
    (hcoeff : ∀ α, b α ≤ 0) :
    ∀ x ∈ (ratBox lo hi).set, aeval x N ≤ 0 := by
  intro x hx
  have h := (boxBern_enclosure lo hi N d b
      (Finset.univ.inf' Finset.univ_nonempty b) 0 hexp
      (fun α => Finset.inf'_le b (Finset.mem_univ α)) hcoeff x hx).2
  simpa using h

end BoxBern
end Qtsl
