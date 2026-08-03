import Qtsl.OdeProfile
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The polynomial-gradient identification

`fderiv` of multivariate polynomial evaluation is the formal `pderiv`
gradient — so the algebraic rows the checker bounds are analytic
derivatives. Proved via the analyticity route (the only route available
at the pinned mathlib version), giving the statics half of the
profile identification: differentiability of the observable plus the
identification of its derivative with the formal gradient.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set Topology MvPolynomial

noncomputable section

section PolyStatics

variable {n : ℕ}

def polyGradCLM (V : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i V) • ContinuousLinearMap.proj i

@[simp] theorem polyGradCLM_apply (V : MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    polyGradCLM V x v = ∑ i, eval x (pderiv i V) * v i := by
  simp [polyGradCLM, smul_eq_mul]

theorem polyGradCLM_C (a : ℝ) (x : Fin n → ℝ) :
    polyGradCLM (MvPolynomial.C a) x = 0 := by
  ext v
  simp [polyGradCLM_apply]

theorem polyGradCLM_add (p q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    polyGradCLM (p + q) x = polyGradCLM p x + polyGradCLM q x := by
  ext v
  simp [polyGradCLM_apply, add_mul, Finset.sum_add_distrib]

theorem polyGradCLM_mul_X (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (x : Fin n → ℝ) :
    polyGradCLM (p * X j) x
      = eval x p • ContinuousLinearMap.proj j + x j • polyGradCLM p x := by
  ext v
  simp only [polyGradCLM_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hterm : ∀ i : Fin n,
      eval x (pderiv i (p * X j)) * v i
        = eval x (pderiv i p) * v i * x j
          + (if j = i then eval x p * v i else 0) := by
    intro i
    by_cases h : j = i
    · simp only [h, pderiv_mul, pderiv_X_self, eval_add, eval_mul, eval_X,
        mul_one, if_pos]
      ring
    · simp only [pderiv_mul, pderiv_X_of_ne h, eval_mul, eval_X,
        mul_zero, add_zero, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq, ← Finset.sum_mul]
  simp only [Finset.mem_univ, if_true]
  ring

theorem hasFDerivAt_eval_poly (V : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y V) (polyGradCLM V x) x := by
  induction V using MvPolynomial.induction_on with
  | C a =>
      rw [polyGradCLM_C]
      have h := hasFDerivAt_const (𝕜 := ℝ) (E := Fin n → ℝ) a x
      have heq : (fun _ : Fin n → ℝ => a)
          = fun y : Fin n → ℝ => eval y (MvPolynomial.C a) :=
        funext fun y => (eval_C (σ := Fin n) a).symm
      rw [heq] at h
      exact h
  | add p q hp hq =>
      rw [polyGradCLM_add]
      have h := hp.add hq
      have heq : ((fun y : Fin n → ℝ => eval y p) + fun y : Fin n → ℝ => eval y q)
          = fun y : Fin n → ℝ => eval y (p + q) :=
        funext fun y => by simp [Pi.add_apply, eval_add]
      rw [heq] at h
      exact h
  | mul_X p j hp =>
      rw [polyGradCLM_mul_X]
      have hproj : HasFDerivAt (fun y : Fin n → ℝ => y j)
          (ContinuousLinearMap.proj j) x :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
          j).hasFDerivAt
      have h := hp.mul hproj
      have heq : ((fun y : Fin n → ℝ => eval y p) * fun y : Fin n → ℝ => y j)
          = fun y : Fin n → ℝ => eval y (p * X j) :=
        funext fun y => by simp [Pi.mul_apply, eval_mul, eval_X]
      rw [heq] at h
      exact h

theorem continuous_eval_poly (V : MvPolynomial (Fin n) ℝ) :
    Continuous fun y : Fin n → ℝ => eval y V :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_eval_poly V x).continuousAt

theorem polyGradCLM_row (V : MvPolynomial (Fin n) ℝ)
    (fp : Fin n → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    polyGradCLM V x (fun i => eval x (fp i))
      = eval x (∑ i, pderiv i V * fp i) := by
  simp [polyGradCLM_apply, eval_mul, map_sum]

end PolyStatics

section RatCoefficients

variable {n : ℕ}

theorem aeval_eq_eval_map_rat (V : MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) :
    aeval x V = eval x (map (algebraMap ℚ ℝ) V) := by
  rw [aeval_def, eval₂_eq_eval_map]

theorem hasFDerivAt_aeval_poly (V : MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => aeval y V)
      (polyGradCLM (map (algebraMap ℚ ℝ) V) x) x := by
  have h := hasFDerivAt_eval_poly (map (algebraMap ℚ ℝ) V) x
  simpa only [aeval_eq_eval_map_rat] using h

theorem continuous_aeval_poly (V : MvPolynomial (Fin n) ℚ) :
    Continuous fun y : Fin n → ℝ => aeval y V :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_aeval_poly V x).continuousAt

theorem polyGradCLM_row_rat (V : MvPolynomial (Fin n) ℚ)
    (fp : Fin n → MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ) :
    polyGradCLM (map (algebraMap ℚ ℝ) V) x (fun i => aeval x (fp i))
      = aeval x (∑ i, pderiv i V * fp i) := by
  have hfp : (fun i => aeval x (fp i))
      = fun i => eval x (map (algebraMap ℚ ℝ) (fp i)) :=
    funext fun i => aeval_eq_eval_map_rat (fp i) x
  rw [hfp, polyGradCLM_row, aeval_eq_eval_map_rat]
  congr 1
  simp [map_sum, map_mul, pderiv_map]

end RatCoefficients

section LipschitzStatics

variable {n : ℕ}

theorem continuous_polyGradCLM (V : MvPolynomial (Fin n) ℝ) :
    Continuous fun x : Fin n → ℝ => polyGradCLM V x :=
  continuous_finsetSum _ fun i _ =>
    (continuous_eval_poly (pderiv i V)).smul continuous_const

theorem exists_lipschitzOnWith_eval_poly (V : MvPolynomial (Fin n) ℝ)
    {C : Set (Fin n → ℝ)} (hC : IsCompact C) (hconv : Convex ℝ C) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x : Fin n → ℝ => eval x V) C := by
  obtain ⟨K, hK⟩ := hC.exists_bound_of_continuousOn
    ((continuous_polyGradCLM V).continuousOn (s := C))
  refine ⟨⟨max K 0, le_max_right _ _⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := fun x => polyGradCLM V x)
    (fun x _ => (hasFDerivAt_eval_poly V x).hasFDerivWithinAt)
    (fun x hx => ?_) hconv
  rw [← NNReal.coe_le_coe]
  exact (hK x hx).trans (le_max_left _ _)

theorem exists_lipschitzOnWith_aeval_poly (V : MvPolynomial (Fin n) ℚ)
    {C : Set (Fin n → ℝ)} (hC : IsCompact C) (hconv : Convex ℝ C) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x : Fin n → ℝ => aeval x V) C := by
  obtain ⟨K, hK⟩ :=
    exists_lipschitzOnWith_eval_poly (map (algebraMap ℚ ℝ) V) hC hconv
  refine ⟨K, ?_⟩
  have heq : (fun x : Fin n → ℝ => aeval x V)
      = fun x : Fin n → ℝ => eval x (map (algebraMap ℚ ℝ) V) :=
    funext fun x => aeval_eq_eval_map_rat V x
  rw [heq]
  exact hK

end LipschitzStatics

namespace Semiflow

variable {n : ℕ}

theorem FlowDerivOn.of_poly_ode {φ : Semiflow (Fin n → ℝ)}
    {fp : Fin n → MvPolynomial (Fin n) ℚ} {V : MvPolynomial (Fin n) ℚ}
    {C : Set (Fin n → ℝ)}
    (hode : φ.SolvesODEOn (fun x i => aeval x (fp i)) C) :
    φ.FlowDerivOn (fun x => aeval x V)
      (fun x => aeval x (∑ i, pderiv i V * fp i)) C := by
  intro x hx
  have h := FlowDerivOn.of_solvesODE hode
    (fun x _ => hasFDerivAt_aeval_poly V x) x hx
  simpa only [polyGradCLM_row_rat] using h

theorem FlowDerivOn.of_poly_ode_real {φ : Semiflow (Fin n → ℝ)}
    {fp : Fin n → MvPolynomial (Fin n) ℝ} {V : MvPolynomial (Fin n) ℝ}
    {C : Set (Fin n → ℝ)}
    (hode : φ.SolvesODEOn (fun x i => eval x (fp i)) C) :
    φ.FlowDerivOn (fun x => eval x V)
      (fun x => eval x (∑ i, pderiv i V * fp i)) C := by
  intro x hx
  have h := FlowDerivOn.of_solvesODE hode
    (fun x _ => hasFDerivAt_eval_poly V x) x hx
  simpa only [polyGradCLM_row] using h

theorem hasTransitCert_of_poly_rows {φ : Semiflow (Fin n → ℝ)}
    {C : Set (Fin n → ℝ)} {fp : Fin n → MvPolynomial (Fin n) ℚ}
    {V : MvPolynomial (Fin n) ℚ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hC : IsCompact C) (hε : 0 < ε)
    (hode : φ.SolvesODEOn (fun x i => aeval x (fp i)) C)
    (hrow : ∀ y ∈ C, aeval y (∑ i, pderiv i V * fp i) ≤ -ε) :
    φ.HasTransitCert C :=
  hasTransitCert_of_rows_isCompact htraj hC hε
    ((continuous_aeval_poly V).continuousOn)
    (FlowDerivOn.of_poly_ode hode) hrow

theorem hasCrossingCert_of_poly {φ : Semiflow (Fin n → ℝ)}
    {O : Set (Fin n → ℝ)} {fp : Fin n → MvPolynomial (Fin n) ℚ}
    {V : MvPolynomial (Fin n) ℚ} {c : ℝ}
    (hlevel : ∀ x ∈ O, aeval x V = c)
    (hode : φ.SolvesODEOn (fun x i => aeval x (fp i)) O)
    (hneg : ∀ x ∈ O, aeval x (∑ i, pderiv i V * fp i) < 0) :
    φ.HasCrossingCert O :=
  hasCrossingCert_of_flowDeriv hlevel (FlowDerivOn.of_poly_ode hode) hneg

theorem hasFacetRows_of_poly_rows {φ : Semiflow (Fin n → ℝ)}
    {D N : Set (Fin n → ℝ)} {m : ℕ}
    {ℓp : Fin m → MvPolynomial (Fin n) ℚ} {ε : Fin m → ℝ}
    {F : Fin m → Set (Fin n → ℝ)} {fp : Fin n → MvPolynomial (Fin n) ℚ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : ∀ i, 0 < ε i)
    (hode : ∀ i, φ.SolvesODEOn (fun x j => aeval x (fp j)) (F i))
    (hrow : ∀ i, ∀ y ∈ F i,
      ε i ≤ aeval y (∑ j, pderiv j (ℓp i) * fp j))
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin m))
        (U : Set (Fin n → ℝ)), U ∈ 𝓝 x ∧
      (∀ i ∈ A, aeval x (ℓp i) = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ aeval y (ℓp i)) → y ∈ N) :
    φ.HasFacetRows D N :=
  hasFacetRows_of_rows
    (fun i x => aeval x (∑ j, pderiv j (ℓp i) * fp j)) htraj hε
    (fun i => (continuous_aeval_poly (ℓp i)).continuousOn)
    (fun i => FlowDerivOn.of_poly_ode (hode i))
    hrow hlocal

end Semiflow

end

end Qtsl

#print axioms Qtsl.polyGradCLM_apply
#print axioms Qtsl.hasFDerivAt_eval_poly
#print axioms Qtsl.continuous_eval_poly
#print axioms Qtsl.polyGradCLM_row
#print axioms Qtsl.hasFDerivAt_aeval_poly
#print axioms Qtsl.continuous_aeval_poly
#print axioms Qtsl.polyGradCLM_row_rat
#print axioms Qtsl.continuous_polyGradCLM
#print axioms Qtsl.exists_lipschitzOnWith_eval_poly
#print axioms Qtsl.exists_lipschitzOnWith_aeval_poly
#print axioms Qtsl.Semiflow.FlowDerivOn.of_poly_ode
#print axioms Qtsl.Semiflow.FlowDerivOn.of_poly_ode_real
#print axioms Qtsl.Semiflow.hasTransitCert_of_poly_rows
#print axioms Qtsl.Semiflow.hasCrossingCert_of_poly
#print axioms Qtsl.Semiflow.hasFacetRows_of_poly_rows

end PPLC
