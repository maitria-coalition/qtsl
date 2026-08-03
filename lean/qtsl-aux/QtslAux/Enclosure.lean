import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Certified polynomial enclosures of exp, sin, cos, and the erf kernel

This module provides checkable witnesses that a truncated Maclaurin series
encloses a transcendental function on a symmetric interval, so that
occurrences of `exp`, `sin`, `cos`, and the error-function kernel can be
replaced by polynomial brackets in downstream certificates.

Main definitions:

* `FnTag` and `FnTag.eval`: the supported functions (`exp`, `sin`, `cos`,
  and `erfT`, the error-function kernel
  `T y = ∫ s in (0:ℝ)..1, Real.exp (-(y * s ^ 2))`).
* `maclaurin t k`: the `k`-th Maclaurin coefficient of the tagged function,
  as a rational number.
* `EncWitness`: a claimed enclosure — a tag, truncation degree `n`, radius
  `r`, error bound `R`, and coefficient list.
* `tailBound n r`: the closed-form geometric-series tail majorant
  `r^(n+1)/(n+1)! * (n+2)/((n+2) - r)`.
* `encCheck`: the Boolean checker validating a witness by exact rational
  arithmetic (coefficients match, `0 ≤ r < n + 2`, `tailBound n r ≤ R`);
  positive and negative instances are discharged by kernel `decide`.

Main results:

* `hasSum_maclaurin`: the Maclaurin series of each tagged function converges
  to it everywhere.
* `abs_maclaurin_le`, `pow_div_factorial_le`, `abs_sub_partialSum_le`: the
  coefficient bound `|c k| ≤ 1/k!` and the resulting quantitative tail
  estimate for any such power series.
* `encCheck_sound`: soundness of the checker — an accepted witness satisfies
  `|f x - poly x| ≤ R` for all `|x| ≤ r`.
* `encCheck_sound_bracket`, `encCheck_point`: the same conclusion in
  two-sided bracket form, and at rational points.
* `integral_exp_neg_sq`: the reduction of the Gaussian integral to the
  `erfT` kernel: `∫ t in (0:ℝ)..z, Real.exp (-(t ^ 2)) = z * FnTag.erfT.eval (z ^ 2)`.
* `two_div_sqrt_pi_mem`, `inv_sqrt_two_pi_mem`: rational brackets for the
  normalization constants `2 / √π` and `1 / √(2π)`, derived from the
  20-digit rational bounds on `π` by squaring comparisons (no square root
  is ever evaluated).
* `linear_interp_le`: nonpositivity of an affine function on an interval
  follows from nonpositivity at both endpoints.
-/

namespace Qtsl.Enclosure

open Finset

inductive FnTag where
  | exp
  | sin
  | cos
  /-- The error-function kernel `T` with `T y = ∫ s in (0:ℝ)..1, exp (-(y * s ^ 2))`,
  an entire function of `y` equal to the confluent hypergeometric value
  `₁F₁(1/2; 3/2; -y)`. It carries the error function via the substitution
  `y = z ^ 2`: `∫ t in (0:ℝ)..z, exp (-(t ^ 2)) = z * T (z ^ 2)` (see
  `integral_exp_neg_sq`), so `erf z = (2 / √π) * z * T (z ^ 2)`. Its Maclaurin
  coefficients `(-1) ^ k / (k ! * (2 * k + 1))` are dominated by `1 / k !`,
  so the uniform tail bound of `encCheck` applies unchanged. -/
  | erfT
  deriving DecidableEq, Repr

noncomputable def FnTag.eval : FnTag → ℝ → ℝ
  | .exp => Real.exp
  | .sin => Real.sin
  | .cos => Real.cos
  | .erfT => fun y => ∫ s in (0:ℝ)..1, Real.exp (-(y * s ^ 2))

def maclaurin : FnTag → ℕ → ℚ
  | .exp, k => 1 / (Nat.factorial k : ℚ)
  | .sin, k => if k % 2 = 1 then (-1 : ℚ) ^ ((k - 1) / 2) / (Nat.factorial k : ℚ) else 0
  | .cos, k => if k % 2 = 0 then (-1 : ℚ) ^ (k / 2) / (Nat.factorial k : ℚ) else 0
  | .erfT, k => (-1 : ℚ) ^ k / ((Nat.factorial k : ℚ) * (2 * (k : ℚ) + 1))

structure EncWitness where
  tag : FnTag
  n : ℕ
  r : ℚ
  R : ℚ
  coeffs : List ℚ
  deriving DecidableEq, Repr

def tailBound (n : ℕ) (r : ℚ) : ℚ :=
  r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ) * (((n : ℚ) + 2) / ((n : ℚ) + 2 - r))

def encCheck (w : EncWitness) : Bool :=
  decide (w.coeffs.length = w.n + 1) &&
    (List.range (w.n + 1)).all (fun k => decide (w.coeffs.getD k 0 = maclaurin w.tag k)) &&
    decide (0 ≤ w.r) &&
    decide (w.r < (w.n : ℚ) + 2) &&
    decide (tailBound w.n w.r ≤ w.R)

noncomputable def evalPoly (cs : List ℚ) (x : ℝ) : ℝ :=
  ∑ k ∈ range cs.length, ((cs.getD k 0 : ℚ) : ℝ) * x ^ k

theorem abs_maclaurin_le (t : FnTag) (k : ℕ) :
    |maclaurin t k| ≤ 1 / (Nat.factorial k : ℚ) := by
  have hfac : (0 : ℚ) < (Nat.factorial k : ℚ) := by
    exact_mod_cast Nat.factorial_pos k
  cases t with
  | exp =>
    rw [maclaurin, abs_of_nonneg (by positivity)]
  | sin =>
    rw [maclaurin]
    by_cases h : k % 2 = 1
    · rw [if_pos h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hfac]
    · rw [if_neg h, abs_zero]
      positivity
  | cos =>
    rw [maclaurin]
    by_cases h : k % 2 = 0
    · rw [if_pos h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hfac]
    · rw [if_neg h, abs_zero]
      positivity
  | erfT =>
    have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
    have h2k : (0 : ℚ) < 2 * (k : ℚ) + 1 := by linarith
    have h1 : (1 : ℚ) ≤ 2 * (k : ℚ) + 1 := by linarith
    rw [maclaurin, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (mul_pos hfac h2k)]
    calc (1 : ℚ) / ((Nat.factorial k : ℚ) * (2 * (k : ℚ) + 1))
        ≤ 1 / ((Nat.factorial k : ℚ) * 1) := by
          apply one_div_le_one_div_of_le (mul_pos hfac one_pos)
          exact mul_le_mul_of_nonneg_left h1 hfac.le
      _ = 1 / (Nat.factorial k : ℚ) := by rw [mul_one]

theorem pow_div_factorial_le {r : ℝ} (hr : 0 ≤ r) (N j : ℕ) :
    r ^ (N + j) / (Nat.factorial (N + j) : ℝ) ≤
      r ^ N / (Nat.factorial N : ℝ) * (r / ((N : ℝ) + 1)) ^ j := by
  have hcast : ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ j) ≤ (Nat.factorial (N + j) : ℝ) := by
    have h := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
    calc (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ j
        = ((Nat.factorial N * (N + 1) ^ j : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Nat.factorial (N + j) : ℝ) := by exact_mod_cast h
  have h1 : r ^ (N + j) / (Nat.factorial (N + j) : ℝ) ≤
      r ^ (N + j) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ j) := by
    gcongr
  calc r ^ (N + j) / (Nat.factorial (N + j) : ℝ)
      ≤ r ^ (N + j) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ j) := h1
    _ = r ^ N / (Nat.factorial N : ℝ) * (r / ((N : ℝ) + 1)) ^ j := by
        rw [pow_add, div_pow]
        field_simp

theorem abs_sub_partialSum_le {c : ℕ → ℝ} {S x r : ℝ} {N : ℕ}
    (hs : HasSum (fun k => c k * x ^ k) S)
    (hc : ∀ k, |c k| ≤ 1 / (Nat.factorial k : ℝ))
    (hx : |x| ≤ r) (hrN : r < (N : ℝ) + 1) :
    |S - ∑ k ∈ range N, c k * x ^ k| ≤
      r ^ N / (Nat.factorial N : ℝ) * (((N : ℝ) + 1) / ((N : ℝ) + 1 - r)) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (abs_nonneg x) hx
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set q : ℝ := r / ((N : ℝ) + 1) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hN1]
    exact hrN

  have hmaj : ∀ j : ℕ, |c (j + N) * x ^ (j + N)| ≤
      r ^ N / (Nat.factorial N : ℝ) * q ^ j := by
    intro j
    have h1 : |c (j + N) * x ^ (j + N)| = |c (j + N)| * |x| ^ (j + N) := by
      rw [abs_mul, abs_pow]
    have h2 : |c (j + N)| * |x| ^ (j + N) ≤
        (1 / (Nat.factorial (j + N) : ℝ)) * r ^ (j + N) := by
      apply mul_le_mul (hc _) _ (by positivity) (by positivity)
      exact pow_le_pow_left₀ (abs_nonneg x) hx _
    have h3 : (1 / (Nat.factorial (j + N) : ℝ)) * r ^ (j + N) =
        r ^ (N + j) / (Nat.factorial (N + j) : ℝ) := by
      rw [add_comm j N]
      ring
    have h4 := pow_div_factorial_le hr0 N j
    rw [h1]
    calc |c (j + N)| * |x| ^ (j + N)
        ≤ (1 / (Nat.factorial (j + N) : ℝ)) * r ^ (j + N) := h2
      _ = r ^ (N + j) / (Nat.factorial (N + j) : ℝ) := h3
      _ ≤ r ^ N / (Nat.factorial N : ℝ) * q ^ j := h4

  have hgeom : Summable (fun j : ℕ => r ^ N / (Nat.factorial N : ℝ) * q ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have habs : Summable (fun j : ℕ => |c (j + N) * x ^ (j + N)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hmaj hgeom
  have htail : Summable (fun j : ℕ => c (j + N) * x ^ (j + N)) := habs.of_abs

  have hsum : Summable (fun k => c k * x ^ k) := hs.summable
  have hsplit : S - ∑ k ∈ range N, c k * x ^ k = ∑' j : ℕ, c (j + N) * x ^ (j + N) := by
    have h := hsum.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    linarith

  have habs' : Summable fun j : ℕ => ‖c (j + N) * x ^ (j + N)‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have hnorm : |∑' j : ℕ, c (j + N) * x ^ (j + N)| ≤
      ∑' j : ℕ, |c (j + N) * x ^ (j + N)| := by
    have h0 := norm_tsum_le_tsum_norm (f := fun j : ℕ => c (j + N) * x ^ (j + N)) habs'
    simpa only [Real.norm_eq_abs] using h0
  have hcomp : (∑' j : ℕ, |c (j + N) * x ^ (j + N)|) ≤
      ∑' j : ℕ, r ^ N / (Nat.factorial N : ℝ) * q ^ j :=
    habs.tsum_le_tsum hmaj hgeom
  have hgeo_eval : (∑' j : ℕ, r ^ N / (Nat.factorial N : ℝ) * q ^ j) =
      r ^ N / (Nat.factorial N : ℝ) * (((N : ℝ) + 1) / ((N : ℝ) + 1 - r)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    congr 1
    rw [hqdef]
    have hne : (N : ℝ) + 1 - r > 0 := by linarith
    field_simp
  rw [hsplit]
  calc |∑' j : ℕ, c (j + N) * x ^ (j + N)|
      ≤ ∑' j : ℕ, |c (j + N) * x ^ (j + N)| := hnorm
    _ ≤ ∑' j : ℕ, r ^ N / (Nat.factorial N : ℝ) * q ^ j := hcomp
    _ = r ^ N / (Nat.factorial N : ℝ) * (((N : ℝ) + 1) / ((N : ℝ) + 1 - r)) := hgeo_eval

theorem hasSum_maclaurin_exp (x : ℝ) :
    HasSum (fun k => ((maclaurin .exp k : ℚ) : ℝ) * x ^ k) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at h
  have hfg : (fun k => ((maclaurin .exp k : ℚ) : ℝ) * x ^ k) =
      (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) := by
    funext k
    rw [maclaurin]
    push_cast
    ring
  rw [hfg]
  exact h

theorem hasSum_maclaurin_sin (x : ℝ) :
    HasSum (fun k => ((maclaurin .sin k : ℚ) : ℝ) * x ^ k) (Real.sin x) := by
  have h := Real.hasSum_sin x
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    have h' : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have hvan : ∀ k ∉ Set.range (fun n : ℕ => 2 * n + 1),
      ((maclaurin .sin k : ℚ) : ℝ) * x ^ k = 0 := by
    intro k hk
    have hk2 : ¬ k % 2 = 1 := by
      intro hodd
      exact hk ⟨k / 2, show 2 * (k / 2) + 1 = k by omega⟩
    rw [maclaurin, if_neg hk2]
    simp
  refine (Function.Injective.hasSum_iff hinj hvan).mp ?_
  have hcomp : ((fun k => ((maclaurin .sin k : ℚ) : ℝ) * x ^ k) ∘ (fun n : ℕ => 2 * n + 1)) =
      (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
    funext n
    have h21 : (2 * n + 1) % 2 = 1 := by omega
    have h22 : (2 * n + 1 - 1) / 2 = n := by omega
    simp only [Function.comp_apply, maclaurin, if_pos h21, h22]
    push_cast
    ring
  rw [hcomp]
  exact h

theorem hasSum_maclaurin_cos (x : ℝ) :
    HasSum (fun k => ((maclaurin .cos k : ℚ) : ℝ) * x ^ k) (Real.cos x) := by
  have h := Real.hasSum_cos x
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    have h' : 2 * a = 2 * b := hab
    omega
  have hvan : ∀ k ∉ Set.range (fun n : ℕ => 2 * n),
      ((maclaurin .cos k : ℚ) : ℝ) * x ^ k = 0 := by
    intro k hk
    have hk2 : ¬ k % 2 = 0 := by
      intro heven
      exact hk ⟨k / 2, show 2 * (k / 2) = k by omega⟩
    rw [maclaurin, if_neg hk2]
    simp
  refine (Function.Injective.hasSum_iff hinj hvan).mp ?_
  have hcomp : ((fun k => ((maclaurin .cos k : ℚ) : ℝ) * x ^ k) ∘ (fun n : ℕ => 2 * n)) =
      (fun n : ℕ => (-1) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) := by
    funext n
    have h20 : (2 * n) % 2 = 0 := by omega
    have h21 : (2 * n) / 2 = n := by omega
    simp only [Function.comp_apply, maclaurin, if_pos h20, h21]
    push_cast
    ring
  rw [hcomp]
  exact h

/-- The Maclaurin series of the error-function kernel converges to it
everywhere: `T y = ∑' k, (-1) ^ k * y ^ k / (k ! * (2 * k + 1))`. Obtained by
expanding `exp (-(y * s ^ 2))` into its exponential series under the integral
sign and integrating term by term (`∫ s in (0:ℝ)..1, s ^ (2 * k) = 1 / (2 * k + 1)`),
justified by summability of the norm integrals. -/
theorem hasSum_maclaurin_erfT (y : ℝ) :
    HasSum (fun k => ((maclaurin .erfT k : ℚ) : ℝ) * y ^ k) (FnTag.erfT.eval y) := by
  have hcont : ∀ k : ℕ, Continuous fun s : ℝ => (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ) :=
    fun k => ((continuous_const.mul (continuous_pow 2)).neg.pow k).div_const _
  have hFint : ∀ k : ℕ, MeasureTheory.IntegrableOn
      (fun s : ℝ => (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)) (Set.Ioc (0 : ℝ) 1) := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((hcont k).intervalIntegrable 0 1)
  -- pointwise, the exponential series at `-(y * s ^ 2)`
  have hFsum : ∀ s : ℝ, HasSum (fun k => (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ))
      (Real.exp (-(y * s ^ 2))) := by
    intro s
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-(y * s ^ 2))
    rwa [← Real.exp_eq_exp_ℝ] at h
  -- the `k`-th term integrates to the `k`-th Maclaurin coefficient times `y ^ k`
  have hterm : ∀ k : ℕ,
      (∫ s in Set.Ioc (0 : ℝ) 1, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)) =
        ((maclaurin .erfT k : ℚ) : ℝ) * y ^ k := by
    intro k
    have hfac : (Nat.factorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos k).ne'
    have h2k1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have hsplit : (∫ s in (0:ℝ)..1, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)) =
        ((-y) ^ k / (Nat.factorial k : ℝ)) * ∫ s in (0:ℝ)..1, s ^ (2 * k) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [show -(y * s ^ 2) = -y * s ^ 2 by ring, mul_pow, ← pow_mul]
      ring
    rw [hsplit, integral_pow, maclaurin]
    push_cast
    rw [one_pow, zero_pow (by omega : 2 * k + 1 ≠ 0), neg_pow]
    field_simp
    ring
  -- the norm integrals are dominated by `|y| ^ k / k !`, hence summable
  have hnorm_le : ∀ k : ℕ,
      (∫ s in Set.Ioc (0 : ℝ) 1, ‖(-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)‖) ≤
        |y| ^ k / (Nat.factorial k : ℝ) := by
    intro k
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => |y| ^ k / (Nat.factorial k : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (continuous_const.intervalIntegrable 0 1)
    have hptwise : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
        ‖(-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)‖ ≤ |y| ^ k / (Nat.factorial k : ℝ) := by
      intro s hs
      have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1.le hs.2
      have hbase : |y * s ^ 2| ≤ |y| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
        calc |y| * s ^ 2 ≤ |y| * 1 := mul_le_mul_of_nonneg_left hs2 (abs_nonneg y)
          _ = |y| := mul_one _
      simp only [norm_div, norm_pow, norm_neg, Real.norm_eq_abs, Nat.abs_cast]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hbase k)
        (by positivity)
    calc (∫ s in Set.Ioc (0 : ℝ) 1, ‖(-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)‖)
        ≤ ∫ _s in Set.Ioc (0 : ℝ) 1, |y| ^ k / (Nat.factorial k : ℝ) :=
          MeasureTheory.setIntegral_mono_on ((hFint k).norm) hconst measurableSet_Ioc hptwise
      _ = |y| ^ k / (Nat.factorial k : ℝ) := by
          rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const]
          simp
  have hFnorm : Summable fun k : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖(-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)‖ :=
    Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg fun s => norm_nonneg _)
      hnorm_le (Real.summable_pow_div_factorial |y|)
  -- swap the sum and the integral
  have hswap : HasSum
      (fun k : ℕ => ∫ s in Set.Ioc (0 : ℝ) 1, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ))
      (∫ s in Set.Ioc (0 : ℝ) 1, ∑' k : ℕ, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ)) :=
    MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFnorm
  have hval : (∫ s in Set.Ioc (0 : ℝ) 1, ∑' k : ℕ, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ))
      = FnTag.erfT.eval y := by
    have h1 : ∀ s : ℝ, (∑' k : ℕ, (-(y * s ^ 2)) ^ k / (Nat.factorial k : ℝ))
        = Real.exp (-(y * s ^ 2)) := fun s => (hFsum s).tsum_eq
    simp only [h1]
    rw [show FnTag.erfT.eval y = ∫ s in (0:ℝ)..1, Real.exp (-(y * s ^ 2)) from rfl,
      intervalIntegral.integral_of_le zero_le_one]
  simp only [hterm] at hswap
  rwa [hval] at hswap

theorem hasSum_maclaurin (t : FnTag) (x : ℝ) :
    HasSum (fun k => ((maclaurin t k : ℚ) : ℝ) * x ^ k) (t.eval x) := by
  cases t with
  | exp => exact hasSum_maclaurin_exp x
  | sin => exact hasSum_maclaurin_sin x
  | cos => exact hasSum_maclaurin_cos x
  | erfT => exact hasSum_maclaurin_erfT x

theorem encCheck_sound (w : EncWitness) (h : encCheck w = true) :
    ∀ x : ℝ, |x| ≤ (w.r : ℝ) →
      |w.tag.eval x - evalPoly w.coeffs x| ≤ (w.R : ℝ) := by

  rw [encCheck] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hco⟩, hr0⟩, hrlt⟩, htail⟩ := h
  intro x hx

  have hP : evalPoly w.coeffs x =
      ∑ k ∈ range (w.n + 1), ((maclaurin w.tag k : ℚ) : ℝ) * x ^ k := by
    rw [evalPoly, hlen]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hco k (Finset.mem_range.mp hk)]

  have hcR : ∀ k : ℕ, |((maclaurin w.tag k : ℚ) : ℝ)| ≤ 1 / (Nat.factorial k : ℝ) := by
    intro k
    have h1 := abs_maclaurin_le w.tag k
    have h2 : ((|maclaurin w.tag k| : ℚ) : ℝ) ≤ ((1 / (Nat.factorial k : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast h1
    rw [Rat.cast_abs] at h2
    calc |((maclaurin w.tag k : ℚ) : ℝ)| ≤ ((1 / (Nat.factorial k : ℚ) : ℚ) : ℝ) := h2
      _ = 1 / (Nat.factorial k : ℝ) := by push_cast; ring

  have hrN : (w.r : ℝ) < ((w.n + 1 : ℕ) : ℝ) + 1 := by
    have : (w.r : ℝ) < (w.n : ℝ) + 2 := by exact_mod_cast hrlt
    push_cast
    linarith

  have hbound := abs_sub_partialSum_le (N := w.n + 1)
    (hasSum_maclaurin w.tag x) hcR hx hrN
  rw [← hP] at hbound

  have htailR : (w.r : ℝ) ^ (w.n + 1) / (Nat.factorial (w.n + 1) : ℝ) *
      ((((w.n + 1 : ℕ) : ℝ) + 1) / (((w.n + 1 : ℕ) : ℝ) + 1 - (w.r : ℝ))) =
      ((tailBound w.n w.r : ℚ) : ℝ) := by
    rw [tailBound]
    push_cast
    ring
  have hRR : ((tailBound w.n w.r : ℚ) : ℝ) ≤ (w.R : ℝ) := by exact_mod_cast htail
  calc |w.tag.eval x - evalPoly w.coeffs x|
      ≤ (w.r : ℝ) ^ (w.n + 1) / (Nat.factorial (w.n + 1) : ℝ) *
        ((((w.n + 1 : ℕ) : ℝ) + 1) / (((w.n + 1 : ℕ) : ℝ) + 1 - (w.r : ℝ))) := hbound
    _ = ((tailBound w.n w.r : ℚ) : ℝ) := htailR
    _ ≤ (w.R : ℝ) := hRR

theorem encCheck_sound_bracket (w : EncWitness) (h : encCheck w = true) :
    ∀ x : ℝ, |x| ≤ (w.r : ℝ) →
      evalPoly w.coeffs x - (w.R : ℝ) ≤ w.tag.eval x ∧
      w.tag.eval x ≤ evalPoly w.coeffs x + (w.R : ℝ) := by
  intro x hx
  have h1 := encCheck_sound w h x hx
  rw [abs_sub_le_iff] at h1
  constructor
  · linarith [h1.1]
  · linarith [h1.2]

theorem encCheck_point (w : EncWitness) (h : encCheck w = true) (c : ℚ)
    (hc : |c| ≤ w.r) :
    evalPoly w.coeffs (c : ℝ) - (w.R : ℝ) ≤ w.tag.eval (c : ℝ) ∧
    w.tag.eval (c : ℝ) ≤ evalPoly w.coeffs (c : ℝ) + (w.R : ℝ) := by
  apply encCheck_sound_bracket w h
  rw [← Rat.cast_abs]
  exact_mod_cast hc

theorem linear_interp_le {A C l h w : ℝ} (hlw : l ≤ w) (hwh : w ≤ h)
    (hl : A + C * l ≤ 0) (hh : A + C * h ≤ 0) : A + C * w ≤ 0 := by
  rcases le_total 0 C with hC | hC
  · have : C * w ≤ C * h := mul_le_mul_of_nonneg_left hwh hC
    linarith
  · have : C * w ≤ C * l := mul_le_mul_of_nonpos_left hlw hC
    linarith

/-- The Gaussian integral reduces to the error-function kernel by the
substitution `t = z * s`: `∫ t in (0:ℝ)..z, exp (-(t ^ 2)) = z * T (z ^ 2)`.
Both sides are odd in `z`, and the oriented interval integral makes the
identity hold for every real `z` without a sign case split. Together with a
bracket for `2 / √π` (see `two_div_sqrt_pi_mem`) this carries polynomial
enclosures of `T` to enclosures of the error function. -/
theorem integral_exp_neg_sq (z : ℝ) :
    ∫ t in (0:ℝ)..z, Real.exp (-(t ^ 2)) = z * FnTag.erfT.eval (z ^ 2) := by
  have h : (z • ∫ s in (0:ℝ)..1, Real.exp (-((z * s) ^ 2)))
      = ∫ t in z * 0..z * 1, Real.exp (-(t ^ 2)) :=
    intervalIntegral.smul_integral_comp_mul_left (f := fun t : ℝ => Real.exp (-(t ^ 2))) z
  rw [mul_zero, mul_one] at h
  rw [← h, smul_eq_mul]
  congr 1
  rw [show FnTag.erfT.eval (z ^ 2) = ∫ s in (0:ℝ)..1, Real.exp (-(z ^ 2 * s ^ 2)) from rfl]
  exact intervalIntegral.integral_congr fun s _ => by rw [mul_pow]

/-! ### Rational brackets for the constants `2 / √π` and `1 / √(2π)`

Downstream certificates need exact rational brackets for the normalization
constants of the error function and of the standard normal density. Both are
derived from the 20-digit rational bounds on `π` by squaring comparisons —
no square root is ever evaluated: for `0 < c`, `c ≤ 2 / √π ↔ c ^ 2 * π ≤ 4`,
and similarly on the other side. Each bracket has relative width at most
`2 ^ (-55)` (see the `example`s below). -/

/-- Lower endpoint of the rational bracket for `2 / √π`. -/
def twoDivSqrtPiLo : ℚ := 1.12837916709551257389

/-- Upper endpoint of the rational bracket for `2 / √π`. -/
def twoDivSqrtPiHi : ℚ := 1.12837916709551257390

/-- Lower endpoint of the rational bracket for `1 / √(2π)`. -/
def invSqrtTwoPiLo : ℚ := 0.398942280401432677939

/-- Upper endpoint of the rational bracket for `1 / √(2π)`. -/
def invSqrtTwoPiHi : ℚ := 0.398942280401432677941

/-- `2 / √π` lies in the rational bracket `[twoDivSqrtPiLo, twoDivSqrtPiHi]`.
Derived from `Real.pi_gt_d20` and `Real.pi_lt_d20` by squaring comparisons. -/
theorem two_div_sqrt_pi_mem :
    ((twoDivSqrtPiLo : ℚ) : ℝ) ≤ 2 / Real.sqrt Real.pi ∧
      2 / Real.sqrt Real.pi ≤ ((twoDivSqrtPiHi : ℚ) : ℝ) := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi0
  have hs2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi0.le
  have hlo : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hhi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hclo : ((twoDivSqrtPiLo : ℚ) : ℝ) = 1.12837916709551257389 := by
    norm_num [twoDivSqrtPiLo]
  have hchi : ((twoDivSqrtPiHi : ℚ) : ℝ) = 1.12837916709551257390 := by
    norm_num [twoDivSqrtPiHi]
  constructor
  · rw [hclo, le_div_iff₀ hs0]
    nlinarith [hs2, hs0, hhi,
      sq_nonneg ((1.12837916709551257389 : ℝ) * Real.sqrt Real.pi - 2)]
  · rw [hchi, div_le_iff₀ hs0]
    nlinarith [hs2, hlo, hs0,
      mul_pos (show (0:ℝ) < 1.12837916709551257390 by norm_num) hs0]

/-- `1 / √(2π)` lies in the rational bracket `[invSqrtTwoPiLo, invSqrtTwoPiHi]`.
Derived from `Real.pi_gt_d20` and `Real.pi_lt_d20` by squaring comparisons. -/
theorem inv_sqrt_two_pi_mem :
    ((invSqrtTwoPiLo : ℚ) : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ ∧
      (Real.sqrt (2 * Real.pi))⁻¹ ≤ ((invSqrtTwoPiHi : ℚ) : ℝ) := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi0 : (0 : ℝ) < 2 * Real.pi := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi0
  have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt h2pi0.le
  have hlo : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hhi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hdlo : ((invSqrtTwoPiLo : ℚ) : ℝ) = 0.398942280401432677939 := by
    norm_num [invSqrtTwoPiLo]
  have hdhi : ((invSqrtTwoPiHi : ℚ) : ℝ) = 0.398942280401432677941 := by
    norm_num [invSqrtTwoPiHi]
  constructor
  · rw [hdlo, inv_eq_one_div, le_div_iff₀ hs0]
    nlinarith [hs2, hhi,
      sq_nonneg ((0.398942280401432677939 : ℝ) * Real.sqrt (2 * Real.pi) - 1)]
  · rw [hdhi, inv_eq_one_div, div_le_iff₀ hs0]
    nlinarith [hs2, hlo, hs0,
      mul_pos (show (0:ℝ) < 0.398942280401432677941 by norm_num) hs0]

/-- The `2 / √π` bracket has relative width at most `2 ^ (-55)`. -/
example : (twoDivSqrtPiHi - twoDivSqrtPiLo) / twoDivSqrtPiLo ≤ 1 / 2 ^ 55 := by
  norm_num [twoDivSqrtPiLo, twoDivSqrtPiHi]

/-- The `1 / √(2π)` bracket has relative width at most `2 ^ (-55)`. -/
example : (invSqrtTwoPiHi - invSqrtTwoPiLo) / invSqrtTwoPiLo ≤ 1 / 2 ^ 55 := by
  norm_num [invSqrtTwoPiLo, invSqrtTwoPiHi]

example : encCheck ⟨.sin, 7, 1, 1/35840,
    [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040]⟩ = true := by decide +kernel

example : encCheck ⟨.exp, 4, 1/2, 1/3520,
    [1, 1, 1/2, 1/6, 1/24]⟩ = true := by decide +kernel

example : encCheck ⟨.cos, 6, 1, 1/4410,
    [1, 0, -1/2, 0, 1/24, 0, -1/720]⟩ = true := by decide +kernel

example : encCheck ⟨.sin, 7, 1, 1/35840,
    [0, 1, 0, 1/6, 0, 1/120, 0, -1/5040]⟩ = false := by decide +kernel

example : encCheck ⟨.sin, 7, 1, 1/40000,
    [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040]⟩ = false := by decide +kernel

example : encCheck ⟨.sin, 7, 9, 1,
    [0, 1, 0, -1/6, 0, 1/120, 0, -1/5040]⟩ = false := by decide +kernel

example : encCheck ⟨.sin, 7, 1, 1/35840,
    [0, 1, 0, -1/6, 0, 1/120, 0]⟩ = false := by decide +kernel

-- erfT receipts: one accept with `R` exactly at the tail bound
-- (`tailBound 8 1 = (1/9!) * (10/9) = 1/326592`), then the four mutants.
example : encCheck ⟨.erfT, 8, 1, 1/326592,
    [1, -1/3, 1/10, -1/42, 1/216, -1/1320, 1/9360, -1/75600, 1/685440]⟩ = true := by
  decide +kernel

-- coefficient flip at `k = 2`
example : encCheck ⟨.erfT, 8, 1, 1/326592,
    [1, -1/3, -1/10, -1/42, 1/216, -1/1320, 1/9360, -1/75600, 1/685440]⟩ = false := by
  decide +kernel

-- `R` strictly below the tail bound
example : encCheck ⟨.erfT, 8, 1, 1/326593,
    [1, -1/3, 1/10, -1/42, 1/216, -1/1320, 1/9360, -1/75600, 1/685440]⟩ = false := by
  decide +kernel

-- radius overflow: `r = 10 = n + 2` exactly (the `r < n + 2` side condition)
example : encCheck ⟨.erfT, 8, 10, 1,
    [1, -1/3, 1/10, -1/42, 1/216, -1/1320, 1/9360, -1/75600, 1/685440]⟩ = false := by
  decide +kernel

-- short coefficient list (8 entries for `n = 8`)
example : encCheck ⟨.erfT, 8, 1, 1/326592,
    [1, -1/3, 1/10, -1/42, 1/216, -1/1320, 1/9360, -1/75600]⟩ = false := by
  decide +kernel

end Qtsl.Enclosure
