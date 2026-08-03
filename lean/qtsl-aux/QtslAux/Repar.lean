import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import QtslAux.GridCx

/-! # Affine reparameterization witnesses for polynomial certificates

This module proves soundness of certificate transport along invertible affine
changes of coordinates with rational data: a nonpositivity certificate checked
in transformed coordinates yields nonpositivity of the original polynomial on
the original region.

Principal declarations:

* `AffineWitness n`: a rational matrix `A`, a claimed inverse `Ainv` with the
  checkable equation `A * Ainv = 1` (`certified`; the left inverse follows by
  `left_certified`), and an offset `b`. Over any commutative `ℚ`-algebra it
  induces mutually inverse point maps `toMapA`/`invMapA`
  (`toMapA_invMapA`, `invMapA_toMapA`, `toMapA_bijective`).
* `AffineWitness.subst`: the corresponding polynomial substitution
  (`bind₁` along the affine coordinate polynomials `lin`), with the evaluation
  identity `aeval_subst : aeval x (subst N) = aeval (toMapA x) N` and an
  explicit inverse witness `inv` satisfying `inv_subst_subst` and
  `subst_inv_subst`.
* `t0_soundness`: single-chart transport — if `Nhat = subst N`, the pulled
  back region `invMapA '' X` lies in the checked domain `D`, and `Nhat ≤ 0`
  on `D`, then `N ≤ 0` on `X`.
* `t05_soundness`, `t05_soundness_images`, `t05_soundness_gridcx`: the
  multi-chart (patch cover) versions, including cells produced by a grid
  patch tree.
* `totalDegree_subst` (via `totalDegree_bind₁_le`): affine substitution
  preserves total degree, so degree budgets transfer exactly.
* `pderiv_subst`, `lieDeriv_subst`: the chain rule for partial derivatives
  under affine substitution, and covariance of the polynomial Lie derivative:
  transporting the vector field by `pullVec` (conjugation by `Ainv`) commutes
  with `subst`.
-/

namespace Qtsl
namespace Repar

open MvPolynomial

theorem forall_mem_image_iff {α β : Type*} {f : α → β} {s : Set α}
    {P : β → Prop} :
    (∀ w ∈ s, P (f w)) ↔ ∀ z ∈ f '' s, P z :=
  Set.forall_mem_image.symm

theorem forall_of_patch_cover {α β : Type*} {ι : Sort*} {P : β → Prop}
    (f : ι → α → β) (D : ι → Set α) (X : Set β)
    (hX : X ⊆ ⋃ i, f i '' D i)
    (h : ∀ i, ∀ w ∈ D i, P (f i w)) :
    ∀ z ∈ X, P z := by
  intro z hz
  rcases Set.mem_iUnion.mp (hX hz) with ⟨i, w, hw, rfl⟩
  exact h i w hw

structure AffineWitness (n : ℕ) where

  A : Matrix (Fin n) (Fin n) ℚ

  Ainv : Matrix (Fin n) (Fin n) ℚ

  b : Fin n → ℚ

  certified : A * Ainv = 1

namespace AffineWitness

variable {n : ℕ} (φ : AffineWitness n)

theorem left_certified : φ.Ainv * φ.A = 1 :=
  mul_eq_one_comm.mp φ.certified

section PointMaps

variable {K : Type*} [CommRing K] [Algebra ℚ K]

def AK : Matrix (Fin n) (Fin n) K :=
  φ.A.map (algebraMap ℚ K)

def AinvK : Matrix (Fin n) (Fin n) K :=
  φ.Ainv.map (algebraMap ℚ K)

def bK : Fin n → K := fun i => algebraMap ℚ K (φ.b i)

theorem AK_mul_AinvK : φ.AK (K := K) * φ.AinvK = 1 := by
  rw [AK, AinvK, ← Matrix.map_mul, φ.certified,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem AinvK_mul_AK : φ.AinvK (K := K) * φ.AK = 1 := by
  rw [AK, AinvK, ← Matrix.map_mul, φ.left_certified,
    Matrix.map_one _ (map_zero _) (map_one _)]

def toMapA (w : Fin n → K) : Fin n → K :=
  φ.AK.mulVec w + φ.bK

def invMapA (z : Fin n → K) : Fin n → K :=
  φ.AinvK.mulVec (z - φ.bK)

theorem toMapA_invMapA (z : Fin n → K) : φ.toMapA (φ.invMapA z) = z := by
  unfold toMapA invMapA
  rw [Matrix.mulVec_mulVec, AK_mul_AinvK, Matrix.one_mulVec]
  abel

theorem invMapA_toMapA (w : Fin n → K) : φ.invMapA (φ.toMapA w) = w := by
  unfold toMapA invMapA
  have h : φ.AK.mulVec w + φ.bK - φ.bK = (φ.AK (K := K)).mulVec w := by abel
  rw [h, Matrix.mulVec_mulVec, AinvK_mul_AK, Matrix.one_mulVec]

theorem toMapA_bijective : Function.Bijective (φ.toMapA (K := K)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨φ.invMapA, φ.invMapA_toMapA, φ.toMapA_invMapA⟩

theorem invMapA_image_subset_iff (X D : Set (Fin n → K)) :
    φ.invMapA '' X ⊆ D ↔ X ⊆ φ.toMapA '' D := by
  rw [Set.image_subset_iff,
    Set.image_eq_preimage_of_inverse φ.invMapA_toMapA φ.toMapA_invMapA]

end PointMaps

noncomputable def lin : Fin n → MvPolynomial (Fin n) ℚ :=
  φ.toMapA X

theorem lin_eq (i : Fin n) :
    φ.lin i = (∑ j, C (φ.A i j) * X j) + C (φ.b i) := by
  simp [lin, toMapA, AK, bK, Matrix.mulVec_apply_eq_sum, Matrix.map_apply,
    algebraMap_eq]

noncomputable def subst : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  bind₁ φ.lin

variable {K : Type*} [CommRing K] [Algebra ℚ K]

theorem aeval_lin (x : Fin n → K) :
    (fun i => aeval x (φ.lin i)) = φ.toMapA x := by
  funext i
  simp [lin, toMapA, AK, bK, Matrix.mulVec_apply_eq_sum, Matrix.map_apply,
    map_sum, map_add, map_mul]

theorem aeval_subst (x : Fin n → K) (N : MvPolynomial (Fin n) ℚ) :
    aeval x (φ.subst N) = aeval (φ.toMapA x) N := by
  have h : aeval x (bind₁ φ.lin N) = aeval (fun i => aeval x (φ.lin i)) N :=
    aeval_bind₁ x φ.lin N
  rw [aeval_lin] at h
  exact h

def inv : AffineWitness n where
  A := φ.Ainv
  Ainv := φ.A
  b := -(φ.Ainv.mulVec φ.b)
  certified := φ.left_certified

theorem inv_toMapA (z : Fin n → K) : φ.inv.toMapA z = φ.invMapA z := by
  have hb : (φ.inv).bK (K := K) = -(φ.AinvK.mulVec φ.bK) := by
    funext i
    simp [inv, bK, AinvK, Matrix.mulVec_apply_eq_sum, Matrix.map_apply,
      Pi.neg_apply, map_neg, map_sum, map_mul]
  have hA : (φ.inv).AK (K := K) = φ.AinvK := rfl
  unfold toMapA invMapA
  rw [hA, hb, Matrix.mulVec_sub]
  abel

theorem inv_subst_subst (N : MvPolynomial (Fin n) ℚ) :
    φ.inv.subst (φ.subst N) = N := by
  have h : φ.inv.subst (φ.subst N) = aeval φ.inv.lin (φ.subst N) := rfl
  have h2 : φ.toMapA (φ.inv.lin) = X := by
    show φ.toMapA (φ.inv.toMapA X) = X
    rw [inv_toMapA, toMapA_invMapA]
  rw [h, φ.aeval_subst, h2, aeval_X_left_apply]

theorem subst_inv_subst (N : MvPolynomial (Fin n) ℚ) :
    φ.subst (φ.inv.subst N) = N := by
  have h : φ.subst (φ.inv.subst N) = aeval φ.lin (φ.inv.subst N) := rfl
  have h2 : φ.inv.toMapA (φ.lin) = X := by
    show φ.inv.toMapA (φ.toMapA X) = X
    rw [inv_toMapA, invMapA_toMapA]
  rw [h, φ.inv.aeval_subst, h2, aeval_X_left_apply]

theorem cell_pullback (N : MvPolynomial (Fin n) ℚ) (C : Set (Fin n → ℝ)) :
    (∀ w ∈ C, aeval w (φ.subst N) ≤ 0) ↔
      ∀ z ∈ φ.toMapA '' C, aeval z N ≤ 0 := by
  constructor
  · rintro h z ⟨w, hw, rfl⟩
    rw [← φ.aeval_subst]
    exact h w hw
  · intro h w hw
    rw [φ.aeval_subst]
    exact h _ ⟨w, hw, rfl⟩

theorem t0_soundness (N Nhat : MvPolynomial (Fin n) ℚ)
    (X D : Set (Fin n → ℝ))
    (hreplay : Nhat = φ.subst N)
    (hcorr : φ.invMapA '' X ⊆ D)
    (hcells : ∀ w ∈ D, aeval w Nhat ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 := by
  intro z hz
  have hw := hcells _ (hcorr (Set.mem_image_of_mem _ hz))
  rwa [hreplay, φ.aeval_subst, φ.toMapA_invMapA] at hw

theorem invMapA_image_sublevel (g : MvPolynomial (Fin n) ℚ) :
    φ.invMapA '' {z : Fin n → ℝ | aeval z g ≤ 0}
      = {w : Fin n → ℝ | aeval w (φ.subst g) ≤ 0} := by
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [φ.aeval_subst, φ.toMapA_invMapA]
  · intro hw
    exact ⟨φ.toMapA w, by rwa [← φ.aeval_subst], φ.invMapA_toMapA w⟩

end AffineWitness

open AffineWitness

theorem t05_soundness {n : ℕ} {ι : Type*} (φs : ι → AffineWitness n)
    (N : MvPolynomial (Fin n) ℚ) (Nhat : ι → MvPolynomial (Fin n) ℚ)
    (X : Set (Fin n → ℝ)) (Xp : ι → Set (Fin n → ℝ))
    (D : ι → Set (Fin n → ℝ))
    (hX : X ⊆ ⋃ i, Xp i)
    (hreplay : ∀ i, Nhat i = (φs i).subst N)
    (hcorr : ∀ i, (φs i).invMapA '' Xp i ⊆ D i)
    (hcells : ∀ i, ∀ w ∈ D i, aeval w (Nhat i) ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 := by
  intro z hz
  rcases Set.mem_iUnion.mp (hX hz) with ⟨i, hi⟩
  exact (φs i).t0_soundness N (Nhat i) (Xp i) (D i) (hreplay i) (hcorr i)
    (hcells i) z hi

theorem t05_soundness_images {n : ℕ} {ι : Type*}
    (f : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (N : MvPolynomial (Fin n) ℚ) (Nhat : ι → MvPolynomial (Fin n) ℚ)
    (X : Set (Fin n → ℝ)) (D : ι → Set (Fin n → ℝ))
    (hX : X ⊆ ⋃ i, f i '' D i)
    (hreplay : ∀ i (w : Fin n → ℝ), aeval w (Nhat i) = aeval (f i w) N)
    (hcells : ∀ i, ∀ w ∈ D i, aeval w (Nhat i) ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 :=
  forall_of_patch_cover f D X hX fun i w hw => by
    rw [← hreplay i w]
    exact hcells i w hw

theorem t05_soundness_gridcx {n : ℕ} {ι : Type*} (φs : ι → AffineWitness n)
    (N : MvPolynomial (Fin n) ℚ) (Nhat : ι → MvPolynomial (Fin n) ℚ)
    (B : ι → GridCx.Box n) (T : ∀ i, GridCx.PatchTree n (B i))
    (X : Set (Fin n → ℝ)) (Xp : ι → Set (Fin n → ℝ))
    (hX : X ⊆ ⋃ i, Xp i)
    (hreplay : ∀ i, Nhat i = (φs i).subst N)
    (hcorr : ∀ i, (φs i).invMapA '' Xp i ⊆ (B i).set)
    (hcells : ∀ i (c : (T i).CellIdx), ∀ w ∈ (T i).cell c,
      aeval w (Nhat i) ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 := by
  refine t05_soundness φs N Nhat X Xp (fun i => (B i).set) hX hreplay hcorr ?_
  intro i w hw
  rcases (T i).exists_mem_cell hw with ⟨c, hc⟩
  exact hcells i c w hc

theorem totalDegree_bind₁_le {σ τ : Type*}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℚ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun u hu => ?_)
  refine le_trans ?_ (le_totalDegree hu)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ u.support, ((f i) ^ (u i)).totalDegree
      ≤ ∑ i ∈ u.support, u i * (f i).totalDegree :=
        Finset.sum_le_sum fun i _ => totalDegree_pow _ _
    _ ≤ ∑ i ∈ u.support, u i * 1 :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul le_rfl (hf i)
    _ = u.sum fun _ e => e := by
        simp [Finsupp.sum]

namespace AffineWitness

variable {n : ℕ} (φ : AffineWitness n)

theorem totalDegree_lin_le (i : Fin n) : (φ.lin i).totalDegree ≤ 1 := by
  rw [lin_eq]
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp [totalDegree_C]))
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_C, totalDegree_X]

theorem totalDegree_subst_le (N : MvPolynomial (Fin n) ℚ) :
    (φ.subst N).totalDegree ≤ N.totalDegree :=
  totalDegree_bind₁_le φ.lin φ.totalDegree_lin_le N

theorem totalDegree_subst (N : MvPolynomial (Fin n) ℚ) :
    (φ.subst N).totalDegree = N.totalDegree := by
  refine le_antisymm (φ.totalDegree_subst_le N) ?_
  have h := φ.inv.totalDegree_subst_le (φ.subst N)
  rwa [φ.inv_subst_subst] at h

theorem image_totalDegree_le (d : ℕ) :
    φ.subst '' {N | N.totalDegree ≤ d} = {N | N.totalDegree ≤ d} := by
  ext N
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact (φ.totalDegree_subst M).le.trans hM
  · intro hN
    exact ⟨φ.inv.subst N, (φ.inv.totalDegree_subst N).le.trans hN,
      φ.subst_inv_subst N⟩

theorem pderiv_lin (k i : Fin n) : pderiv i (φ.lin k) = C (φ.A k i) := by
  rw [lin_eq]
  simp [pderiv_X, Pi.single_apply, map_add, map_sum, mul_ite,
    Finset.sum_ite_eq']

theorem pderiv_subst (N : MvPolynomial (Fin n) ℚ) (i : Fin n) :
    pderiv i (φ.subst N) = ∑ j, C (φ.A j i) * φ.subst (pderiv j N) := by
  induction N using MvPolynomial.induction_on with
  | C a =>
    simp [subst]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hsubst_mul : φ.subst (p * X k) = φ.subst p * φ.lin k := by
      rw [map_mul]
      congr 1
      exact bind₁_X_right _ _
    have hrhs : ∀ j : Fin n,
        φ.subst (pderiv j (p * X k))
          = φ.subst (pderiv j p) * φ.lin k
            + if k = j then φ.subst p else 0 := by
      intro j
      rw [pderiv_mul, map_add, map_mul, map_mul, pderiv_X, Pi.single_apply]
      congr 1
      · congr 1
        exact bind₁_X_right _ _
      · rw [apply_ite (fun q => φ.subst q), map_one, map_zero, mul_ite,
          mul_one, mul_zero]
    rw [hsubst_mul, pderiv_mul, hp, pderiv_lin]
    simp only [hrhs, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    congr 1
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    · rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k), mul_comm]

noncomputable def lieDeriv (V : MvPolynomial (Fin n) ℚ)
    (f : Fin n → MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  ∑ j, pderiv j V * f j

noncomputable def pullVec (f : Fin n → MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial (Fin n) ℚ :=
  ∑ j, C (φ.Ainv i j) * φ.subst (f j)

theorem lieDeriv_subst (V : MvPolynomial (Fin n) ℚ)
    (f : Fin n → MvPolynomial (Fin n) ℚ) :
    lieDeriv (φ.subst V) (φ.pullVec f) = φ.subst (lieDeriv V f) := by
  have hRHS : φ.subst (lieDeriv V f)
      = ∑ j, φ.subst (pderiv j V) * φ.subst (f j) := by
    unfold lieDeriv
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_mul _ _ _
  have hLHS : lieDeriv (φ.subst V) (φ.pullVec f)
      = ∑ i, ∑ j, ∑ k, (C (φ.A j i) * φ.subst (pderiv j V))
          * (C (φ.Ainv i k) * φ.subst (f k)) := by
    unfold lieDeriv pullVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pderiv_subst, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hswap : (∑ i, ∑ j, ∑ k, (C (φ.A j i) * φ.subst (pderiv j V))
          * (C (φ.Ainv i k) * φ.subst (f k)))
      = ∑ j, ∑ k, ∑ i, (C (φ.A j i) * φ.subst (pderiv j V))
          * (C (φ.Ainv i k) * φ.subst (f k)) := by
    rw [show (∑ i, ∑ j, ∑ k, (C (φ.A j i) * φ.subst (pderiv j V))
            * (C (φ.Ainv i k) * φ.subst (f k)))
        = ∑ j, ∑ i, ∑ k, (C (φ.A j i) * φ.subst (pderiv j V))
            * (C (φ.Ainv i k) * φ.subst (f k)) from Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hcollapse : ∀ j k, (∑ i, (C (φ.A j i) * φ.subst (pderiv j V))
          * (C (φ.Ainv i k) * φ.subst (f k)))
      = C ((φ.A * φ.Ainv) j k) * (φ.subst (pderiv j V) * φ.subst (f k)) := by
    intro j k
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C_mul]
    ring
  have hdiag : ∀ j, (∑ k, C ((φ.A * φ.Ainv) j k)
          * (φ.subst (pderiv j V) * φ.subst (f k)))
      = φ.subst (pderiv j V) * φ.subst (f j) := by
    intro j
    rw [φ.certified]
    have h1 : ∀ k, C ((1 : Matrix (Fin n) (Fin n) ℚ) j k)
          * (φ.subst (pderiv j V) * φ.subst (f k))
        = if j = k then φ.subst (pderiv j V) * φ.subst (f k) else 0 := by
      intro k
      rw [Matrix.one_apply]
      by_cases h : j = k <;> simp [h]
    simp only [h1]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
  rw [hLHS, hswap, hRHS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ k, ∑ i, (C (φ.A j i) * φ.subst (pderiv j V))
        * (C (φ.Ainv i k) * φ.subst (f k)))
      = ∑ k, C ((φ.A * φ.Ainv) j k) * (φ.subst (pderiv j V) * φ.subst (f k))
    from Finset.sum_congr rfl fun k _ => hcollapse j k]
  exact hdiag j

end AffineWitness

end Repar
end Qtsl
