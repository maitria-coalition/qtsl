import Qtsl.Core.Catalogue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Positive-(semi)definiteness certificate theorems

Mathlib-side warrant for the checker's mathlib-free PSD witness checks:
each Boolean check implies positive (semi)definiteness of the ℝ-cast of
the certified ℚ-matrix, and hence nonnegativity of the quadratic form
at every rational point. Three certificate species:

* `checkT_posDef` — triangular-inverse witness: the congruence of an
  upper-triangular positive-diagonal witness against a lower-triangular
  positive-diagonal product is diagonal and positive, and transports
  back through the invertible factor;
* `checkDD_posDef` — congruence to a strictly diagonally dominant
  matrix;
* `checkK_posSemidef` — Gram-factor witness for the semidefinite case.
-/

namespace PPLC
namespace PsdCert

open Matrix Finset

section RealTheorems

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] [LinearOrder n] in
theorem isHermitian_of_symm {A : Matrix n n ℝ}
    (hA : ∀ i j, A i j = A j i) : A.IsHermitian := by
  ext i j
  simp [conjTranspose_apply, hA j i]

theorem congruence_eq_diagonal {A Z : Matrix n n ℝ}
    (hA : ∀ i j, A i j = A j i)
    (hZu : ∀ ⦃i j⦄, j < i → Z i j = 0)
    (hMl : ∀ ⦃i j⦄, i < j → (A * Z) i j = 0) :
    Zᴴ * (A * Z) = diagonal fun i => Z i i * (A * Z) i i := by
  classical
  set M := A * Z with hM
  have hB : ∀ i j, (Zᴴ * M) i j = ∑ k, Z k i * M k j := by
    intro i j
    simp [mul_apply]

  have hupper : ∀ ⦃i j⦄, i < j → (Zᴴ * M) i j = 0 := by
    intro i j hij
    rw [hB]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [hZu hik, zero_mul]
    · rw [hMl (lt_of_le_of_lt hki hij), mul_zero]

  have hherm : (Zᴴ * M).IsHermitian := by
    have : (Zᴴ * M) = Zᴴ * A * Z := by rw [hM, Matrix.mul_assoc]
    rw [this]
    exact isHermitian_conjTranspose_mul_mul Z (isHermitian_of_symm hA)
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [hupper hij, diagonal_apply_ne _ (ne_of_lt hij)]
  · rw [diagonal_apply_eq, hB]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with hki | hik
    · rw [hMl hki, mul_zero]
    · rw [hZu hik, zero_mul]
  · rw [diagonal_apply_ne _ (ne_of_gt hji)]
    have := congrFun (congrFun hherm i) j
    rw [conjTranspose_apply, star_trivial] at this
    rw [← this, hupper hji]

theorem posDef_of_congruence_posDef {A Z : Matrix n n ℝ}
    (hZu : ∀ ⦃i j⦄, j < i → Z i j = 0)
    (hZd : ∀ i, 0 < Z i i)
    (hBd : (Zᴴ * (A * Z)).PosDef) :
    A.PosDef := by
  classical

  have hdet : IsUnit Z.det := by
    rw [Matrix.det_of_upperTriangular (fun i j (h : j < i) => hZu h)]
    exact (Finset.prod_pos fun i _ => hZd i).ne'.isUnit
  have : Invertible Z := Z.invertibleOfIsUnitDet hdet

  have hres : (⅟Z)ᴴ * (Zᴴ * (A * Z)) * ⅟Z = A := by
    calc (⅟Z)ᴴ * (Zᴴ * (A * Z)) * ⅟Z
        = ((Z * ⅟Z)ᴴ) * A * (Z * ⅟Z) := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
    _ = A := by rw [mul_invOf_self]; simp
  rw [← hres]
  exact hBd.conjTranspose_mul_mul_same (mulVec_injective_of_invertible (⅟Z))

theorem posDef_of_triangular_witness {A Z : Matrix n n ℝ}
    (hA : ∀ i j, A i j = A j i)
    (hZu : ∀ ⦃i j⦄, j < i → Z i j = 0)
    (hZd : ∀ i, 0 < Z i i)
    (hMl : ∀ ⦃i j⦄, i < j → (A * Z) i j = 0)
    (hMd : ∀ i, 0 < (A * Z) i i) :
    A.PosDef := by
  refine posDef_of_congruence_posDef hZu hZd ?_
  rw [congruence_eq_diagonal hA hZu hMl]
  exact .diagonal fun i => mul_pos (hZd i) (hMd i)

omit [LinearOrder n] in

private lemma abs_mul_abs_le_half_sq (a b : ℝ) :
    |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b,
    abs_nonneg a, abs_nonneg b]

omit [LinearOrder n] in

private lemma sum_ite_eq_sum_erase [DecidableEq n] (i : n) (g : n → ℝ) :
    (∑ j, if j = i then 0 else g j) = ∑ j ∈ Finset.univ.erase i, g j := by
  rw [← Finset.sum_erase (Finset.univ) (a := i)
      (f := fun j => if j = i then 0 else g j) (by simp)]
  exact Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

omit [LinearOrder n] in

theorem posDef_of_dominant [DecidableEq n] {B : Matrix n n ℝ}
    (hsym : ∀ i j, B i j = B j i)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, |B i j|) < B i i) :
    B.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_of_symm hsym)
    (fun x hx => ?_)
  have hstar : star x = x := funext fun i => star_trivial (x i)
  rw [hstar]

  have hexp : x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ j, x i * (B i j * x j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hexp]

  have hsplit : (∑ i, ∑ j, x i * (B i j * x j))
      = (∑ i, B i i * x i ^ 2)
        + ∑ i, ∑ j ∈ Finset.univ.erase i, x i * (B i j * x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring_nf
  rw [hsplit]

  have hoff : ∀ i, ∀ j, -(|B i j| * (x i ^ 2 + x j ^ 2) / 2)
      ≤ x i * (B i j * x j) := by
    intro i j
    have h1 : |x i * (B i j * x j)| ≤ |B i j| * (x i ^ 2 + x j ^ 2) / 2 := by
      have h2 : |x i * (B i j * x j)| = |B i j| * (|x i| * |x j|) := by
        rw [abs_mul, abs_mul]; ring
      rw [h2]
      have h3 := abs_mul_abs_le_half_sq (x i) (x j)
      calc |B i j| * (|x i| * |x j|)
          ≤ |B i j| * ((x i ^ 2 + x j ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |B i j| * (x i ^ 2 + x j ^ 2) / 2 := by ring
    calc -(|B i j| * (x i ^ 2 + x j ^ 2) / 2)
        ≤ -|x i * (B i j * x j)| := neg_le_neg h1
      _ ≤ x i * (B i j * x j) := neg_abs_le _
  have henv : -(∑ i, ∑ j ∈ Finset.univ.erase i, |B i j| * (x i ^ 2 + x j ^ 2) / 2)
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, x i * (B i j * x j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => hoff i j

  have hfold : (∑ i, ∑ j ∈ Finset.univ.erase i, |B i j| * (x i ^ 2 + x j ^ 2) / 2)
      = ∑ i, (∑ j ∈ Finset.univ.erase i, |B i j|) * x i ^ 2 := by
    have hhalf : ∀ i j, |B i j| * (x i ^ 2 + x j ^ 2) / 2
        = |B i j| * x i ^ 2 / 2 + |B i j| * x j ^ 2 / 2 := by
      intro i j; ring
    simp only [hhalf, Finset.sum_add_distrib]

    have hswap : (∑ i, ∑ j ∈ Finset.univ.erase i, |B i j| * x j ^ 2 / 2)
        = ∑ i, ∑ j ∈ Finset.univ.erase i, |B i j| * x i ^ 2 / 2 := by
      have hsub : ∀ (g : n → n → ℝ),
          (∑ i, ∑ j ∈ Finset.univ.erase i, g i j)
          = (∑ i, ∑ j, g i j) - ∑ i, g i i := by
        intro g
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eq_sub_iff_add_eq, add_comm]
        exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
      rw [hsub, hsub]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hsym i j]
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hcpos : ∀ i, 0 < B i i - ∑ j ∈ Finset.univ.erase i, |B i j| :=
    fun i => sub_pos.mpr (hdom i)
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hsumpos : 0 < ∑ i, (B i i - ∑ j ∈ Finset.univ.erase i, |B i j|) * x i ^ 2 := by
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hcpos i).le (sq_nonneg _)) ?_
    exact ⟨i₀, Finset.mem_univ i₀,
      mul_pos (hcpos i₀) (by positivity)⟩
  have hexpand : (∑ i, (B i i - ∑ j ∈ Finset.univ.erase i, |B i j|) * x i ^ 2)
      = (∑ i, B i i * x i ^ 2)
        - ∑ i, (∑ j ∈ Finset.univ.erase i, |B i j|) * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := henv
  rw [hfold] at this
  linarith [hsumpos, hexpand ▸ hsumpos]

theorem posDef_of_dd_witness [DecidableEq n] {A Z : Matrix n n ℝ}
    (hA : ∀ i j, A i j = A j i)
    (hZu : ∀ ⦃i j⦄, j < i → Z i j = 0)
    (hZd : ∀ i, 0 < Z i i)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, |(Zᴴ * (A * Z)) i j|)
              < (Zᴴ * (A * Z)) i i) :
    A.PosDef := by
  refine posDef_of_congruence_posDef hZu hZd ?_
  refine posDef_of_dominant (fun i j => ?_) hdom

  have hherm : (Zᴴ * (A * Z)).IsHermitian := by
    have h : (Zᴴ * (A * Z)) = Zᴴ * A * Z := by rw [Matrix.mul_assoc]
    rw [h]
    exact isHermitian_conjTranspose_mul_mul Z (isHermitian_of_symm hA)
  have := congrFun (congrFun hherm j) i
  rw [conjTranspose_apply, star_trivial] at this
  exact this

end RealTheorems

theorem posSemidef_of_factor {m' n' : Type*} [Fintype m'] [Fintype n']
    {A : Matrix n' n' ℝ} {B : Matrix m' m' ℝ} {L : Matrix m' n' ℝ}
    (hB : B.PosSemidef) (hA : A = Lᴴ * B * L) : A.PosSemidef := by
  rw [hA]
  exact hB.conjTranspose_mul_mul_same L

def matR {a : Nat} (M : Fin a → Fin a → ℚ) : Matrix (Fin a) (Fin a) ℝ :=
  Matrix.of fun i j => ((M i j : ℚ) : ℝ)

def matRe {a b : Nat} (M : Fin a → Fin b → ℚ) : Matrix (Fin a) (Fin b) ℝ :=
  Matrix.of fun i j => ((M i j : ℚ) : ℝ)

@[simp] lemma matR_apply {a : Nat} (M : Fin a → Fin a → ℚ) (i j : Fin a) :
    matR M i j = ((M i j : ℚ) : ℝ) := rfl

@[simp] lemma matRe_apply {a b : Nat} (M : Fin a → Fin b → ℚ) (i : Fin a)
    (j : Fin b) : matRe M i j = ((M i j : ℚ) : ℝ) := rfl

private lemma foldr_add_cast (l : List ℚ) :
    ((l.foldr (· + ·) 0 : ℚ) : ℝ) = (l.map fun q => ((q : ℚ) : ℝ)).foldr (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

private lemma foldr_eq_sum (l : List ℝ) : l.foldr (· + ·) 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

lemma finQSum_cast (a : Nat) (f : Fin a → ℚ) :
    ((finQSum a f : ℚ) : ℝ) = ∑ i, ((f i : ℚ) : ℝ) := by
  rw [finQSum, qlsum, foldr_add_cast, List.map_map, foldr_eq_sum,
    Fin.sum_univ_def]
  rfl

lemma qabs_cast (q : ℚ) : ((qabs q : ℚ) : ℝ) = |((q : ℚ) : ℝ)| := by
  rw [qabs]
  split
  · next h => rw [abs_of_neg (by exact_mod_cast h)]; push_cast; ring
  · next h => rw [abs_of_nonneg (by exact_mod_cast not_lt.mp h)]

private lemma all2_spec {a : Nat} {p : Fin a → Fin a → Bool}
    (h : ((List.finRange a).all fun i => (List.finRange a).all fun j => p i j)
      = true) : ∀ i j, p i j = true := fun i j =>
  List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j
    (List.mem_finRange j)

private lemma all1_spec {a : Nat} {p : Fin a → Bool}
    (h : ((List.finRange a).all fun i => p i) = true) : ∀ i, p i = true :=
  fun i => List.all_eq_true.mp h i (List.mem_finRange i)

lemma matR_mul_apply {a : Nat} (A Z : Fin a → Fin a → ℚ) (i j : Fin a) :
    (matR A * matR Z) i j = ((mulEntry a A Z i j : ℚ) : ℝ) := by
  rw [Matrix.mul_apply, mulEntry, finQSum_cast]
  push_cast
  rfl

lemma matR_cong_apply {a : Nat} (A Z : Fin a → Fin a → ℚ) (i j : Fin a) :
    ((matR Z)ᴴ * (matR A * matR Z)) i j = ((congEntry a A Z i j : ℚ) : ℝ) := by
  rw [Matrix.mul_apply, congEntry, finQSum_cast]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_apply, matR_apply, star_trivial, matR_mul_apply]

/-- The triangular-inverse witness check implies positive definiteness of
the ℝ-cast matrix. -/
theorem checkT_posDef {a : Nat} {A Z : Fin a → Fin a → ℚ}
    (h : checkT a A Z = true) : (matR A).PosDef := by
  rw [checkT, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsym, htri⟩, hMl⟩, hMd⟩ := h
  rw [upperTriPosDiagB, Bool.and_eq_true] at htri
  obtain ⟨hZu, hZd⟩ := htri
  refine posDef_of_triangular_witness (Z := matR Z)
    (fun i j => by
      have := of_decide_eq_true (all2_spec hsym i j)
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i j hij => by
      have := (of_decide_eq_true (all2_spec hZu i j)) hij
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i => by
      have := of_decide_eq_true (all1_spec hZd i)
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i j hij => by
      have := (of_decide_eq_true (all2_spec hMl i j)) hij
      rw [matR_mul_apply]
      exact_mod_cast this)
    (fun i => by
      have := of_decide_eq_true (all1_spec hMd i)
      rw [matR_mul_apply]
      exact_mod_cast this)

/-- The diagonal-dominance witness check implies positive definiteness of
the ℝ-cast matrix. -/
theorem checkDD_posDef {a : Nat} {A Z : Fin a → Fin a → ℚ}
    (h : checkDD a A Z = true) : (matR A).PosDef := by
  rw [checkDD, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsym, htri⟩, hdom⟩ := h
  rw [upperTriPosDiagB, Bool.and_eq_true] at htri
  obtain ⟨hZu, hZd⟩ := htri
  refine posDef_of_dd_witness (Z := matR Z)
    (fun i j => by
      have := of_decide_eq_true (all2_spec hsym i j)
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i j hij => by
      have := (of_decide_eq_true (all2_spec hZu i j)) hij
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i => by
      have := of_decide_eq_true (all1_spec hZd i)
      simp only [matR_apply]
      exact_mod_cast this)
    (fun i => ?_)
  have hq : finQSum a (fun j => if j = i then 0 else qabs (congEntry a A Z i j))
      < congEntry a A Z i i := of_decide_eq_true (all1_spec hdom i)
  have hcast : (((finQSum a (fun j => if j = i then 0
        else qabs (congEntry a A Z i j)) : ℚ)) : ℝ)
      < ((congEntry a A Z i i : ℚ) : ℝ) := by exact_mod_cast hq
  rw [finQSum_cast] at hcast
  have hL : (∑ j, (((if j = i then 0 else qabs (congEntry a A Z i j)) : ℚ) : ℝ))
      = ∑ j ∈ Finset.univ.erase i, |((matR Z)ᴴ * (matR A * matR Z)) i j| := by
    have h1 : ∀ j : Fin a, (((if j = i then 0
          else qabs (congEntry a A Z i j)) : ℚ) : ℝ)
        = (if j = i then 0 else |((matR Z)ᴴ * (matR A * matR Z)) i j|) := by
      intro j
      split
      · simp
      · rw [qabs_cast, matR_cong_apply]
    calc (∑ j, (((if j = i then 0 else qabs (congEntry a A Z i j)) : ℚ) : ℝ))
        = ∑ j, (if j = i then 0
            else |((matR Z)ᴴ * (matR A * matR Z)) i j|) :=
          Finset.sum_congr rfl fun j _ => h1 j
      _ = ∑ j ∈ Finset.univ.erase i,
            |((matR Z)ᴴ * (matR A * matR Z)) i j| :=
          sum_ite_eq_sum_erase i _
  rw [hL, ← matR_cong_apply] at hcast
  exact hcast

/-- The Gram-factor witness check implies positive semidefiniteness of the
ℝ-cast matrix. -/
theorem checkK_posSemidef {m k : Nat} {A : Fin (m + k) → Fin (m + k) → ℚ}
    {N : Fin m → Fin k → ℚ} {B : Fin m → Fin m → ℚ} {innerT : Bool}
    {Z : Fin m → Fin m → ℚ}
    (h : checkK m k A N B innerT Z = true) : (matR A).PosSemidef := by
  rw [checkK, Bool.and_eq_true] at h
  obtain ⟨hfact, hinner⟩ := h

  have hB : (matR B).PosSemidef := by
    rcases hb : innerT with _ | _ <;> rw [hb] at hinner
    · simp only [if_neg Bool.false_ne_true] at hinner
      exact (checkDD_posDef hinner).posSemidef
    · simp only [if_pos rfl] at hinner
      exact (checkT_posDef hinner).posSemidef

  refine posSemidef_of_factor (L := matRe (kernelExt m k N)) hB ?_
  ext i j
  have hq : A i j = qlsum ((List.finRange m).map fun a =>
      qlsum ((List.finRange m).map fun b =>
        kernelExt m k N a i * B a b * kernelExt m k N b j)) :=
    of_decide_eq_true (all2_spec hfact i j)
  have hcast : ((A i j : ℚ) : ℝ) = ∑ a, ∑ b,
      ((kernelExt m k N a i : ℚ) : ℝ) * ((B a b : ℚ) : ℝ)
        * ((kernelExt m k N b j : ℚ) : ℝ) := by
    rw [hq]
    rw [show qlsum ((List.finRange m).map fun a =>
        qlsum ((List.finRange m).map fun b =>
          kernelExt m k N a i * B a b * kernelExt m k N b j))
      = finQSum m (fun a => finQSum m (fun b =>
          kernelExt m k N a i * B a b * kernelExt m k N b j)) from rfl]
    rw [finQSum_cast]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finQSum_cast]
    push_cast
    rfl
  have hRHS : ((matRe (kernelExt m k N))ᴴ * matR B * matRe (kernelExt m k N)) i j
      = ∑ a2, ∑ b, ((kernelExt m k N a2 i : ℚ) : ℝ) * ((B a2 b : ℚ) : ℝ)
          * ((kernelExt m k N b j : ℚ) : ℝ) := by
    rw [Matrix.mul_apply]
    have h1 : ∀ b : Fin m, ((matRe (kernelExt m k N))ᴴ * matR B) i b
        = ∑ a2, ((kernelExt m k N a2 i : ℚ) : ℝ) * ((B a2 b : ℚ) : ℝ) := by
      intro b
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a2 _ => ?_
      rw [conjTranspose_apply, matRe_apply, star_trivial, matR_apply]
    calc ∑ b, ((matRe (kernelExt m k N))ᴴ * matR B) i b
            * matRe (kernelExt m k N) b j
        = ∑ b, ∑ a2, ((kernelExt m k N a2 i : ℚ) : ℝ) * ((B a2 b : ℚ) : ℝ)
            * ((kernelExt m k N b j : ℚ) : ℝ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [h1 b, matRe_apply, Finset.sum_mul]
      _ = ∑ a2, ∑ b, ((kernelExt m k N a2 i : ℚ) : ℝ) * ((B a2 b : ℚ) : ℝ)
            * ((kernelExt m k N b j : ℚ) : ℝ) := Finset.sum_comm
  rw [matR_apply, hcast, hRHS]

theorem quadForm_nonneg_of_posSemidef {a : Nat} {M : Fin a → Fin a → ℚ}
    (h : (matR M).PosSemidef) (x : Fin a → ℚ) :
    0 ≤ finQSum a (fun i => finQSum a (fun j => M i j * x i * x j)) := by
  have hR := h.dotProduct_mulVec_nonneg (fun i => ((x i : ℚ) : ℝ))
  have hstar : star (fun i => ((x i : ℚ) : ℝ)) = fun i => ((x i : ℚ) : ℝ) :=
    funext fun i => star_trivial _
  rw [hstar] at hR
  have hexp : (fun i => ((x i : ℚ) : ℝ)) ⬝ᵥ (matR M *ᵥ fun i => ((x i : ℚ) : ℝ))
      = ((finQSum a (fun i => finQSum a (fun j => M i j * x i * x j)) : ℚ) : ℝ) := by
    rw [finQSum_cast]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finQSum_cast]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dotProduct, matR_apply]
    ring
  rw [hexp] at hR
  exact_mod_cast hR

theorem checkT_quadForm_nonneg {a : Nat} {A Z : Fin a → Fin a → ℚ}
    (h : checkT a A Z = true) (x : Fin a → ℚ) :
    0 ≤ finQSum a (fun i => finQSum a (fun j => A i j * x i * x j)) :=
  quadForm_nonneg_of_posSemidef (checkT_posDef h).posSemidef x

theorem checkDD_quadForm_nonneg {a : Nat} {A Z : Fin a → Fin a → ℚ}
    (h : checkDD a A Z = true) (x : Fin a → ℚ) :
    0 ≤ finQSum a (fun i => finQSum a (fun j => A i j * x i * x j)) :=
  quadForm_nonneg_of_posSemidef (checkDD_posDef h).posSemidef x

theorem checkK_quadForm_nonneg {m k : Nat} {A : Fin (m + k) → Fin (m + k) → ℚ}
    {N : Fin m → Fin k → ℚ} {B : Fin m → Fin m → ℚ} {innerT : Bool}
    {Z : Fin m → Fin m → ℚ}
    (h : checkK m k A N B innerT Z = true) (x : Fin (m + k) → ℚ) :
    0 ≤ finQSum (m + k) (fun i => finQSum (m + k) (fun j => A i j * x i * x j)) :=
  quadForm_nonneg_of_posSemidef (checkK_posSemidef h) x

#guard PsdCert.checkT 2 ![![2, 3], ![3, 7]] ![![1, -3], ![0, 2]]

#guard !(PsdCert.checkT 2 ![![2, 3], ![3, 7]] ![![1, -3], ![0, -2]])

#guard !(PsdCert.checkT 2 ![![0, 1], ![1, 0]] ![![1, 0], ![0, 1]])
#guard PsdCert.checkDD 2 ![![2, 3], ![3, 7]] ![![1, -3], ![0, 2]]

#guard !(PsdCert.checkDD 2 ![![2, 3], ![3, 7]] ![![1, 0], ![0, 1]])
#guard PsdCert.checkK 1 1 ![![1, -1], ![-1, 1]] ![![-1]] ![![1]] true ![![1]]

#guard !(PsdCert.checkK 1 1 ![![1, -1], ![-1, 1]] ![![1]] ![![1]] true ![![1]])

#guard PsdCert.checkK 0 2 ![![0, 0], ![0, 0]] ![] ![] true ![]

end PsdCert
end PPLC
