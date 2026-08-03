import QtslAux.Repar

/-! # Tame polynomial reparameterizations: shears, compositions, words

This module extends certificate transport from affine changes of coordinates
to tame polynomial automorphisms: triangular shears, and arbitrary finite
compositions of affine and shear factors.

Principal declarations:

* `bind₁_vars_eq_self`: substitution fixing every variable of `p` fixes `p`.
* `totalDegree_bind₁_le_mul`: degree control
  `(bind₁ f p).totalDegree ≤ d * p.totalDegree` when each `f i` has total
  degree at most `d`.
* `ShearWitness n`: one distinguished coordinate `idx` and a polynomial `g`
  in strictly earlier variables (`triangular`); the forward map adds `g` to
  the `idx`-th coordinate and the backward map subtracts it. Triangularity
  makes the pair exactly mutually inverse (`bind₁_bwd_fwd`, `bind₁_fwd_bwd`).
* `TameWitness n`: a pair of polynomial substitutions `fwd`/`bwd` that are
  mutually inverse as variable assignments (`cov`, `inj`), with induced
  mutually inverse point maps `toMap`/`invMap` over any commutative
  `ℚ`-algebra, the identity witness `TameWitness.id`, embeddings `ofAffine`
  and `ofShear`, and closure under composition `comp`
  (`comp_toMap : (T.comp U).toMap = T.toMap ∘ U.toMap`).
* `TameFactor` and `wordWitness`: words over affine and shear factors,
  evaluated to a single `TameWitness` by folding `comp`.
* `t1_soundness`, `t1_soundness_word`: certificate transport along a tame
  witness (respectively, a word of factors) — `Nhat = T.subst N`,
  `T.invMap '' X ⊆ D`, and `Nhat ≤ 0` on `D` imply `N ≤ 0` on `X`.
* `cell_cofactor_iff`, `cleared_pullback_soundness`: transport in the
  presence of a positive cofactor `q` (e.g. a cleared denominator):
  nonpositivity of the cleared pullback `Nhat = (N ∘ f) * q` on each patch
  yields nonpositivity of `N` on the covered region.
-/

noncomputable section

namespace Qtsl
namespace Repar

open MvPolynomial

theorem bind₁_vars_eq_self {σ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial σ R) (p : MvPolynomial σ R)
    (h : ∀ j ∈ p.vars, f j = X j) : bind₁ f p = p := by
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [bind₁_monomial, monomial_eq]
  simp only [Finsupp.prod]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [h j ((mem_vars_iff_mem_support j).mpr ⟨u, hu, hj⟩)]

theorem totalDegree_bind₁_le_mul {σ τ : Type*}
    (f : σ → MvPolynomial τ ℚ) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (p : MvPolynomial σ ℚ) :
    (bind₁ f p).totalDegree ≤ d * p.totalDegree := by
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun u hu => ?_)
  refine le_trans ?_ (Nat.mul_le_mul le_rfl (le_totalDegree hu))
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ u.support, ((f i) ^ (u i)).totalDegree
      ≤ ∑ i ∈ u.support, u i * (f i).totalDegree :=
        Finset.sum_le_sum fun i _ => totalDegree_pow _ _
    _ ≤ ∑ i ∈ u.support, u i * d :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul le_rfl (hf i)
    _ = d * u.sum fun _ e => e := by
        simp only [Finsupp.sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _

structure ShearWitness (n : ℕ) where

  idx : Fin n

  g : MvPolynomial (Fin n) ℚ

  triangular : ∀ j ∈ g.vars, j < idx

namespace ShearWitness

variable {n : ℕ} (sh : ShearWitness n)

def fwd : Fin n → MvPolynomial (Fin n) ℚ :=
  fun j => if j = sh.idx then X sh.idx + sh.g else X j

def bwd : Fin n → MvPolynomial (Fin n) ℚ :=
  fun j => if j = sh.idx then X sh.idx - sh.g else X j

theorem fwd_apply_ne {j : Fin n} (hj : j ≠ sh.idx) : sh.fwd j = X j :=
  if_neg hj

theorem bwd_apply_ne {j : Fin n} (hj : j ≠ sh.idx) : sh.bwd j = X j :=
  if_neg hj

theorem fwd_apply_idx : sh.fwd sh.idx = X sh.idx + sh.g := if_pos rfl

theorem bwd_apply_idx : sh.bwd sh.idx = X sh.idx - sh.g := if_pos rfl

theorem bind₁_fwd_g : bind₁ sh.fwd sh.g = sh.g :=
  bind₁_vars_eq_self _ _ fun j hj => sh.fwd_apply_ne (sh.triangular j hj).ne

theorem bind₁_bwd_g : bind₁ sh.bwd sh.g = sh.g :=
  bind₁_vars_eq_self _ _ fun j hj => sh.bwd_apply_ne (sh.triangular j hj).ne

theorem bind₁_bwd_fwd (j : Fin n) : bind₁ sh.bwd (sh.fwd j) = X j := by
  by_cases hj : j = sh.idx
  · subst hj
    rw [sh.fwd_apply_idx, map_add, bind₁_X_right, sh.bwd_apply_idx,
      sh.bind₁_bwd_g]
    ring
  · rw [sh.fwd_apply_ne hj, bind₁_X_right, sh.bwd_apply_ne hj]

theorem bind₁_fwd_bwd (j : Fin n) : bind₁ sh.fwd (sh.bwd j) = X j := by
  by_cases hj : j = sh.idx
  · subst hj
    rw [sh.bwd_apply_idx, map_sub, bind₁_X_right, sh.fwd_apply_idx,
      sh.bind₁_fwd_g]
    ring
  · rw [sh.bwd_apply_ne hj, bind₁_X_right, sh.fwd_apply_ne hj]

theorem totalDegree_fwd_le (j : Fin n) :
    (sh.fwd j).totalDegree ≤ max 1 sh.g.totalDegree := by
  by_cases hj : j = sh.idx
  · subst hj
    rw [sh.fwd_apply_idx]
    refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_X]
  · rw [sh.fwd_apply_ne hj]
    exact (totalDegree_X j).le.trans (le_max_left _ _)

end ShearWitness

structure TameWitness (n : ℕ) where

  fwd : Fin n → MvPolynomial (Fin n) ℚ

  bwd : Fin n → MvPolynomial (Fin n) ℚ

  cov : ∀ j, bind₁ bwd (fwd j) = X j

  inj : ∀ j, bind₁ fwd (bwd j) = X j

namespace TameWitness

variable {n : ℕ} (T : TameWitness n)

def subst : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  bind₁ T.fwd

def invSubst : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  bind₁ T.bwd

section PointMaps

variable {K : Type*} [CommRing K] [Algebra ℚ K]

def toMap (x : Fin n → K) : Fin n → K := fun j => aeval x (T.fwd j)

def invMap (z : Fin n → K) : Fin n → K := fun j => aeval z (T.bwd j)

theorem aeval_subst (x : Fin n → K) (N : MvPolynomial (Fin n) ℚ) :
    aeval x (T.subst N) = aeval (T.toMap x) N :=
  aeval_bind₁ x T.fwd N

theorem toMap_invMap (z : Fin n → K) : T.toMap (T.invMap z) = z := by
  funext j
  calc T.toMap (T.invMap z) j
      = aeval z (bind₁ T.bwd (T.fwd j)) :=
        (aeval_bind₁ z T.bwd (T.fwd j)).symm
    _ = aeval z (X j) := by rw [T.cov]
    _ = z j := aeval_X _ _

theorem invMap_toMap (w : Fin n → K) : T.invMap (T.toMap w) = w := by
  funext j
  calc T.invMap (T.toMap w) j
      = aeval w (bind₁ T.fwd (T.bwd j)) :=
        (aeval_bind₁ w T.fwd (T.bwd j)).symm
    _ = aeval w (X j) := by rw [T.inj]
    _ = w j := aeval_X _ _

theorem toMap_bijective : Function.Bijective (T.toMap (K := K)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨T.invMap, T.invMap_toMap, T.toMap_invMap⟩

theorem invMap_image_subset_iff (X D : Set (Fin n → K)) :
    T.invMap '' X ⊆ D ↔ X ⊆ T.toMap '' D := by
  rw [Set.image_subset_iff,
    Set.image_eq_preimage_of_inverse T.invMap_toMap T.toMap_invMap]

end PointMaps

protected def id (n : ℕ) : TameWitness n where
  fwd := X
  bwd := X
  cov j := bind₁_X_right X j
  inj j := bind₁_X_right X j

def ofAffine (φ : AffineWitness n) : TameWitness n where
  fwd := φ.lin
  bwd := φ.inv.lin
  cov j := by
    have h := φ.inv_subst_subst (X j)
    rwa [show φ.subst (X j) = φ.lin j from bind₁_X_right _ _] at h
  inj j := by
    have h := φ.subst_inv_subst (X j)
    rwa [show φ.inv.subst (X j) = φ.inv.lin j from bind₁_X_right _ _] at h

def ofShear (sh : ShearWitness n) : TameWitness n where
  fwd := sh.fwd
  bwd := sh.bwd
  cov := sh.bind₁_bwd_fwd
  inj := sh.bind₁_fwd_bwd

def comp (T U : TameWitness n) : TameWitness n where
  fwd := fun j => bind₁ U.fwd (T.fwd j)
  bwd := fun j => bind₁ T.bwd (U.bwd j)
  cov j := by
    calc bind₁ (fun i => bind₁ T.bwd (U.bwd i)) (bind₁ U.fwd (T.fwd j))
        = bind₁ T.bwd (bind₁ U.bwd (bind₁ U.fwd (T.fwd j))) :=
          (bind₁_bind₁ U.bwd T.bwd (bind₁ U.fwd (T.fwd j))).symm
      _ = bind₁ T.bwd (bind₁ (fun i => bind₁ U.bwd (U.fwd i)) (T.fwd j)) :=
          congrArg (bind₁ T.bwd) (bind₁_bind₁ U.fwd U.bwd (T.fwd j))
      _ = bind₁ T.bwd (bind₁ X (T.fwd j)) := by
          rw [show (fun i => bind₁ U.bwd (U.fwd i))
              = (X : Fin n → MvPolynomial (Fin n) ℚ) from funext U.cov]
      _ = bind₁ T.bwd (T.fwd j) := by
          simp only [bind₁_X_left, AlgHom.id_apply]
      _ = X j := T.cov j
  inj j := by
    calc bind₁ (fun i => bind₁ U.fwd (T.fwd i)) (bind₁ T.bwd (U.bwd j))
        = bind₁ U.fwd (bind₁ T.fwd (bind₁ T.bwd (U.bwd j))) :=
          (bind₁_bind₁ T.fwd U.fwd (bind₁ T.bwd (U.bwd j))).symm
      _ = bind₁ U.fwd (bind₁ (fun i => bind₁ T.fwd (T.bwd i)) (U.bwd j)) :=
          congrArg (bind₁ U.fwd) (bind₁_bind₁ T.bwd T.fwd (U.bwd j))
      _ = bind₁ U.fwd (bind₁ X (U.bwd j)) := by
          rw [show (fun i => bind₁ T.fwd (T.bwd i))
              = (X : Fin n → MvPolynomial (Fin n) ℚ) from funext T.inj]
      _ = bind₁ U.fwd (U.bwd j) := by
          simp only [bind₁_X_left, AlgHom.id_apply]
      _ = X j := U.inj j

theorem comp_toMap {K : Type*} [CommRing K] [Algebra ℚ K]
    (T U : TameWitness n) (x : Fin n → K) :
    (T.comp U).toMap x = T.toMap (U.toMap x) := by
  funext j
  exact aeval_bind₁ x U.fwd (T.fwd j)

theorem totalDegree_subst_le_mul {d : ℕ}
    (hT : ∀ j, (T.fwd j).totalDegree ≤ d) (N : MvPolynomial (Fin n) ℚ) :
    (T.subst N).totalDegree ≤ d * N.totalDegree :=
  totalDegree_bind₁_le_mul T.fwd d hT N

end TameWitness

inductive TameFactor (n : ℕ) where

  | affine (φ : AffineWitness n)

  | shear (sh : ShearWitness n)

def TameFactor.witness {n : ℕ} : TameFactor n → TameWitness n
  | .affine φ => TameWitness.ofAffine φ
  | .shear sh => TameWitness.ofShear sh

def wordWitness {n : ℕ} : List (TameFactor n) → TameWitness n
  | [] => TameWitness.id n
  | f :: fs => (f.witness).comp (wordWitness fs)

theorem wordWitness_cons {n : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    (f : TameFactor n) (fs : List (TameFactor n)) (x : Fin n → K) :
    (wordWitness (f :: fs)).toMap x
      = f.witness.toMap ((wordWitness fs).toMap x) :=
  TameWitness.comp_toMap _ _ x

theorem t1_soundness {n : ℕ} (T : TameWitness n)
    (N Nhat : MvPolynomial (Fin n) ℚ) (X D : Set (Fin n → ℝ))
    (hreplay : Nhat = T.subst N)
    (hcorr : T.invMap '' X ⊆ D)
    (hcells : ∀ w ∈ D, aeval w Nhat ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 := by
  intro z hz
  have hw := hcells _ (hcorr (Set.mem_image_of_mem _ hz))
  rwa [hreplay, T.aeval_subst, T.toMap_invMap] at hw

theorem t1_soundness_word {n : ℕ} (ws : List (TameFactor n))
    (N Nhat : MvPolynomial (Fin n) ℚ) (X D : Set (Fin n → ℝ))
    (hreplay : Nhat = (wordWitness ws).subst N)
    (hcorr : (wordWitness ws).invMap '' X ⊆ D)
    (hcells : ∀ w ∈ D, aeval w Nhat ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 :=
  t1_soundness (wordWitness ws) N Nhat X D hreplay hcorr hcells

theorem mul_nonpos_iff_of_pos {x q : ℝ} (hq : 0 < q) :
    x * q ≤ 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (not_le.mpr (mul_pos (not_le.mp hx) hq))
  · intro h
    calc x * q ≤ 0 * q := mul_le_mul_of_nonneg_right h hq.le
      _ = 0 := zero_mul q

theorem cell_cofactor_iff {n : ℕ} (M q : MvPolynomial (Fin n) ℚ)
    (D : Set (Fin n → ℝ)) (hq : ∀ w ∈ D, 0 < aeval w q) :
    (∀ w ∈ D, aeval w (M * q) ≤ 0) ↔ ∀ w ∈ D, aeval w M ≤ 0 := by
  constructor <;> intro h w hw
  · have hh := h w hw
    rw [map_mul] at hh
    exact (mul_nonpos_iff_of_pos (hq w hw)).mp hh
  · rw [map_mul]
    exact (mul_nonpos_iff_of_pos (hq w hw)).mpr (h w hw)

theorem cleared_pullback_soundness {n : ℕ} {ι : Sort*}
    (f : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (N : MvPolynomial (Fin n) ℚ) (Nhat q : ι → MvPolynomial (Fin n) ℚ)
    (X : Set (Fin n → ℝ)) (D : ι → Set (Fin n → ℝ))
    (hX : X ⊆ ⋃ i, f i '' D i)
    (hq : ∀ i, ∀ w ∈ D i, 0 < aeval w (q i))
    (hreplay : ∀ i, ∀ w ∈ D i,
      aeval w (Nhat i) = aeval (f i w) N * aeval w (q i))
    (hcells : ∀ i, ∀ w ∈ D i, aeval w (Nhat i) ≤ 0) :
    ∀ z ∈ X, aeval z N ≤ 0 :=
  forall_of_patch_cover f D X hX fun i w hw => by
    have h := hcells i w hw
    rw [hreplay i w hw] at h
    exact (mul_nonpos_iff_of_pos (hq i w hw)).mp h

end Repar
end Qtsl
