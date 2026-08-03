import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Defect bounds between soft (power-mean) and hard (lattice) semantics

This module compares two recursive valuations of a connective tree
`RedTerm` — with leaves in `ℝ≥0∞` and connectives `tensor`, `par`, `oplus`,
and `owedge` — and bounds their discrepancy by a counting invariant of the
tree shape.

* `RedTerm.valP p`: the soft semantics, interpreting `oplus` as the
  `ℓᵖ`-sum `(∑ vᵢᵖ)^(1/p)` and `owedge` as its harmonic dual (`tensor` as
  product, `par` as the inverse-product dual).
* `RedTerm.valInf`: the hard (`p → ∞`) semantics, interpreting `oplus` as
  supremum and `owedge` as infimum.
* `RedTerm.defectO` / `RedTerm.defectC`: multiplicative defect counters —
  the products of the branching factors of the `oplus` (respectively
  `owedge`) nodes along the tree.

Main results:

* `RedTerm.valP_le` / `RedTerm.valInf_le`: two-sided comparison —
  `valP p T ≤ defectO^(1/p) * valInf T` and
  `valInf T ≤ defectC^(1/p) * valP p T`; the two semantics agree up to a
  factor `defect^(1/p)` that vanishes as `p → ∞`.
* `hard_of_soft` / `soft_of_hard`: margin transfer — an exponential margin
  `exp η` in one semantics yields the margin `exp (η - log defect / p)` in
  the other.
* `RedTerm.dual` with `valP_dual`, `valInf_dual`, `defectO_dual`,
  `defectC_dual`: the involutive De Morgan duality exchanging
  `tensor`/`par` and `oplus`/`owedge`, inverting values and swapping the two
  defect counters.
* `lse`, `sup'_le_lse`, `lse_le_sup'_add`, `hard_margin_of_lse_le`,
  `lse_le_of_hard_margin`: the scalar log-sum-exp analogue — `lse p`
  overapproximates the maximum by at most `log (n + 1) / p`.
-/

namespace Qtsl.DefectBound

open Finset
open scoped ENNReal NNReal

inductive RedTerm : Type where

  | leaf : ℝ≥0∞ → RedTerm

  | tensor : RedTerm → RedTerm → RedTerm

  | par : RedTerm → RedTerm → RedTerm

  | oplus : (n : ℕ) → (Fin (n + 1) → RedTerm) → RedTerm

  | owedge : (n : ℕ) → (Fin (n + 1) → RedTerm) → RedTerm

namespace RedTerm

noncomputable def valP (p : ℝ) : RedTerm → ℝ≥0∞
  | leaf v => v
  | tensor l r => valP p l * valP p r
  | par l r => ((valP p l)⁻¹ * (valP p r)⁻¹)⁻¹
  | oplus _ c => (∑ i, valP p (c i) ^ p) ^ p⁻¹
  | owedge _ c => ((∑ i, (valP p (c i))⁻¹ ^ p) ^ p⁻¹)⁻¹

noncomputable def valInf : RedTerm → ℝ≥0∞
  | leaf v => v
  | tensor l r => valInf l * valInf r
  | par l r => ((valInf l)⁻¹ * (valInf r)⁻¹)⁻¹
  | oplus _ c => ⨆ i, valInf (c i)
  | owedge _ c => ⨅ i, valInf (c i)

def defectO : RedTerm → ℕ
  | leaf _ => 1
  | tensor l r => defectO l * defectO r
  | par l r => defectO l * defectO r
  | oplus n c => (univ.sup fun i => defectO (c i)) * (n + 1)
  | owedge _ c => univ.sup fun i => defectO (c i)

def defectC : RedTerm → ℕ
  | leaf _ => 1
  | tensor l r => defectC l * defectC r
  | par l r => defectC l * defectC r
  | oplus _ c => univ.sup fun i => defectC (c i)
  | owedge n c => (univ.sup fun i => defectC (c i)) * (n + 1)

theorem defectO_pos : ∀ T : RedTerm, 0 < T.defectO
  | leaf _ => one_pos
  | tensor l r => Nat.mul_pos (defectO_pos l) (defectO_pos r)
  | par l r => Nat.mul_pos (defectO_pos l) (defectO_pos r)
  | oplus n c => Nat.mul_pos
      (lt_of_lt_of_le (defectO_pos (c 0)) (le_sup (f := fun i => defectO (c i)) (mem_univ 0)))
      n.succ_pos
  | owedge _ c =>
      lt_of_lt_of_le (defectO_pos (c 0)) (le_sup (f := fun i => defectO (c i)) (mem_univ 0))

theorem defectC_pos : ∀ T : RedTerm, 0 < T.defectC
  | leaf _ => one_pos
  | tensor l r => Nat.mul_pos (defectC_pos l) (defectC_pos r)
  | par l r => Nat.mul_pos (defectC_pos l) (defectC_pos r)
  | oplus _ c =>
      lt_of_lt_of_le (defectC_pos (c 0)) (le_sup (f := fun i => defectC (c i)) (mem_univ 0))
  | owedge n c => Nat.mul_pos
      (lt_of_lt_of_le (defectC_pos (c 0)) (le_sup (f := fun i => defectC (c i)) (mem_univ 0)))
      n.succ_pos

end RedTerm

private lemma natCast_rpow_ne_zero {d : ℕ} (hd : 0 < d) (r : ℝ) :
    ((d : ℝ≥0∞)) ^ r ≠ 0 :=
  (ENNReal.rpow_pos (by exact_mod_cast hd) (ENNReal.natCast_ne_top d)).ne'

private lemma natCast_rpow_ne_top {d : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ((d : ℝ≥0∞)) ^ r ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg hr (ENNReal.natCast_ne_top d)

theorem le_psum {n : ℕ} (f : Fin (n + 1) → ℝ≥0∞) {p : ℝ} (hp : 0 < p) (i : Fin (n + 1)) :
    f i ≤ (∑ j, f j ^ p) ^ p⁻¹ := by
  have h1 : f i ^ p ≤ ∑ j, f j ^ p :=
    Finset.single_le_sum (f := fun j => f j ^ p) (fun j _ => zero_le) (mem_univ i)
  calc f i = (f i ^ p) ^ p⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
    _ ≤ (∑ j, f j ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow h1 (by positivity)

theorem iSup_le_psum {n : ℕ} (f : Fin (n + 1) → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ≤ (∑ j, f j ^ p) ^ p⁻¹ :=
  iSup_le (le_psum f hp)

theorem psum_le_mul_iSup {n : ℕ} (f : Fin (n + 1) → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∑ j, f j ^ p) ^ p⁻¹ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ p⁻¹ * ⨆ i, f i := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  have hsum : (∑ j, f j ^ p) ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (⨆ i, f i) ^ p := by
    have h := Finset.sum_le_card_nsmul univ (fun j => f j ^ p) ((⨆ i, f i) ^ p)
      (fun j _ => ENNReal.rpow_le_rpow (le_iSup f j) hp.le)
    simpa [Finset.card_univ, nsmul_eq_mul] using h
  calc (∑ j, f j ^ p) ^ p⁻¹
      ≤ (((n + 1 : ℕ) : ℝ≥0∞) * (⨆ i, f i) ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsum hip
    _ = ((n + 1 : ℕ) : ℝ≥0∞) ^ p⁻¹ * ⨆ i, f i := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hip, ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

theorem psum_le_scale_mul_psum {n : ℕ} {f g : Fin (n + 1) → ℝ≥0∞} {s : ℝ≥0∞} {p : ℝ}
    (hp : 0 < p) (h : ∀ i, f i ≤ s * g i) :
    (∑ j, f j ^ p) ^ p⁻¹ ≤ s * (∑ j, g j ^ p) ^ p⁻¹ := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  have hsum : (∑ j, f j ^ p) ≤ s ^ p * ∑ j, g j ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc f j ^ p ≤ (s * g j) ^ p := ENNReal.rpow_le_rpow (h j) hp.le
      _ = s ^ p * g j ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp.le
  calc (∑ j, f j ^ p) ^ p⁻¹
      ≤ (s ^ p * ∑ j, g j ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsum hip
    _ = s * (∑ j, g j ^ p) ^ p⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hip, ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

theorem scale_inv_le_inv {a b s : ℝ≥0∞} (hs0 : s ≠ 0) (hst : s ≠ ∞) (h : a ≤ s * b) :
    s⁻¹ * b⁻¹ ≤ a⁻¹ := by
  rw [← ENNReal.mul_inv (Or.inl hs0) (Or.inl hst)]
  exact ENNReal.inv_le_inv' h

theorem inv_le_scale_mul_inv {a b s : ℝ≥0∞} (hs0 : s ≠ 0) (hst : s ≠ ∞) (h : a ≤ s * b) :
    b⁻¹ ≤ s * a⁻¹ := by
  calc b⁻¹ = s * (s⁻¹ * b⁻¹) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hs0 hst, one_mul]
    _ ≤ s * a⁻¹ := mul_le_mul' le_rfl (scale_inv_le_inv hs0 hst h)

theorem par_le_scale_mul_par {a b a' b' s t : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ∞) (ht0 : t ≠ 0) (htt : t ≠ ∞)
    (ha : a ≤ s * a') (hb : b ≤ t * b') :
    (a⁻¹ * b⁻¹)⁻¹ ≤ (s * t) * (a'⁻¹ * b'⁻¹)⁻¹ := by
  have hst0 : s * t ≠ 0 := mul_ne_zero hs0 ht0
  have hstt : s * t ≠ ∞ := ENNReal.mul_ne_top hst htt
  have h3 : (s * t)⁻¹ * (a'⁻¹ * b'⁻¹) ≤ a⁻¹ * b⁻¹ := by
    calc (s * t)⁻¹ * (a'⁻¹ * b'⁻¹) = (s⁻¹ * a'⁻¹) * (t⁻¹ * b'⁻¹) := by
          rw [ENNReal.mul_inv (Or.inl hs0) (Or.inl hst), mul_mul_mul_comm]
      _ ≤ a⁻¹ * b⁻¹ :=
          mul_le_mul' (scale_inv_le_inv hs0 hst ha) (scale_inv_le_inv ht0 htt hb)
  have hi0 : (s * t)⁻¹ ≠ 0 := by
    simp only [ne_eq, ENNReal.inv_eq_zero]; exact hstt
  have hit : (s * t)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hst0
  calc (a⁻¹ * b⁻¹)⁻¹ ≤ ((s * t)⁻¹ * (a'⁻¹ * b'⁻¹))⁻¹ := ENNReal.inv_le_inv' h3
    _ = (s * t) * (a'⁻¹ * b'⁻¹)⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hi0) (Or.inl hit), inv_inv]

namespace RedTerm

theorem valP_le (p : ℝ) (hp : 0 < p) (T : RedTerm) :
    T.valP p ≤ (T.defectO : ℝ≥0∞) ^ p⁻¹ * T.valInf := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  induction T with
  | leaf v => simp [valP, valInf, defectO]
  | tensor l r ihl ihr =>
      simp only [valP, valInf, defectO]
      rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip, mul_mul_mul_comm]
      exact mul_le_mul' ihl ihr
  | par l r ihl ihr =>
      simp only [valP, valInf, defectO]
      rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip]
      exact par_le_scale_mul_par
        (natCast_rpow_ne_zero (defectO_pos l) _) (natCast_rpow_ne_top hip)
        (natCast_rpow_ne_zero (defectO_pos r) _) (natCast_rpow_ne_top hip) ihl ihr
  | oplus n c ih =>
      simp only [valP, valInf, defectO]
      set S : ℕ := univ.sup fun i => defectO (c i) with hS
      have hchild : ∀ i, valP p (c i) ≤ (S : ℝ≥0∞) ^ p⁻¹ * valInf (c i) := fun i =>
        (ih i).trans (mul_le_mul'
          (ENNReal.rpow_le_rpow
            (by exact_mod_cast Finset.le_sup (f := fun i => defectO (c i)) (mem_univ i))
            hip)
          le_rfl)
      calc (∑ i, valP p (c i) ^ p) ^ p⁻¹
          ≤ (S : ℝ≥0∞) ^ p⁻¹ * (∑ i, valInf (c i) ^ p) ^ p⁻¹ :=
            psum_le_scale_mul_psum hp hchild
        _ ≤ (S : ℝ≥0∞) ^ p⁻¹ * (((n + 1 : ℕ) : ℝ≥0∞) ^ p⁻¹ * ⨆ i, valInf (c i)) :=
            mul_le_mul' le_rfl (psum_le_mul_iSup _ hp)
        _ = ((S * (n + 1) : ℕ) : ℝ≥0∞) ^ p⁻¹ * ⨆ i, valInf (c i) := by
            rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip, mul_assoc]
  | owedge n c ih =>
      simp only [valP, valInf, defectO]
      set S : ℕ := univ.sup fun i => defectO (c i) with hS
      have hSpos : 0 < S :=
        lt_of_lt_of_le (defectO_pos (c 0)) (le_sup (f := fun i => defectO (c i)) (mem_univ 0))
      set s : ℝ≥0∞ := (S : ℝ≥0∞) ^ p⁻¹ with hs
      have hs0 : s ≠ 0 := natCast_rpow_ne_zero hSpos _
      have hst : s ≠ ∞ := natCast_rpow_ne_top hip
      have hchild : ∀ i, valP p (c i) ≤ s * valInf (c i) := fun i =>
        (ih i).trans (mul_le_mul'
          (ENNReal.rpow_le_rpow
            (by exact_mod_cast Finset.le_sup (f := fun i => defectO (c i)) (mem_univ i))
            hip)
          le_rfl)

      have key : s⁻¹ * (⨅ i, valInf (c i))⁻¹ ≤ (∑ j, (valP p (c j))⁻¹ ^ p) ^ p⁻¹ := by
        rw [ENNReal.inv_iInf, ENNReal.mul_iSup]
        exact iSup_le fun i =>
          le_trans (scale_inv_le_inv hs0 hst (hchild i)) (le_psum _ hp i)
      have hi0 : s⁻¹ ≠ 0 := by simp only [ne_eq, ENNReal.inv_eq_zero]; exact hst
      have hit : s⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hs0
      calc ((∑ j, (valP p (c j))⁻¹ ^ p) ^ p⁻¹)⁻¹
          ≤ (s⁻¹ * (⨅ i, valInf (c i))⁻¹)⁻¹ := ENNReal.inv_le_inv' key
        _ = s * ⨅ i, valInf (c i) := by
            rw [ENNReal.mul_inv (Or.inl hi0) (Or.inl hit), inv_inv, inv_inv]

theorem valInf_le (p : ℝ) (hp : 0 < p) (T : RedTerm) :
    T.valInf ≤ (T.defectC : ℝ≥0∞) ^ p⁻¹ * T.valP p := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  induction T with
  | leaf v => simp [valP, valInf, defectC]
  | tensor l r ihl ihr =>
      simp only [valP, valInf, defectC]
      rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip, mul_mul_mul_comm]
      exact mul_le_mul' ihl ihr
  | par l r ihl ihr =>
      simp only [valP, valInf, defectC]
      rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip]
      exact par_le_scale_mul_par
        (natCast_rpow_ne_zero (defectC_pos l) _) (natCast_rpow_ne_top hip)
        (natCast_rpow_ne_zero (defectC_pos r) _) (natCast_rpow_ne_top hip) ihl ihr
  | oplus n c ih =>
      simp only [valP, valInf, defectC]
      set S : ℕ := univ.sup fun i => defectC (c i) with hS

      refine iSup_le fun i => ?_
      calc valInf (c i) ≤ (defectC (c i) : ℝ≥0∞) ^ p⁻¹ * valP p (c i) := ih i
        _ ≤ (S : ℝ≥0∞) ^ p⁻¹ * (∑ j, valP p (c j) ^ p) ^ p⁻¹ :=
            mul_le_mul'
              (ENNReal.rpow_le_rpow
                (by exact_mod_cast Finset.le_sup (f := fun i => defectC (c i)) (mem_univ i))
                hip)
              (le_psum _ hp i)
  | owedge n c ih =>
      simp only [valP, valInf, defectC]
      set S : ℕ := univ.sup fun i => defectC (c i) with hS
      have hSpos : 0 < S :=
        lt_of_lt_of_le (defectC_pos (c 0)) (le_sup (f := fun i => defectC (c i)) (mem_univ 0))
      set t : ℝ≥0∞ := (S : ℝ≥0∞) ^ p⁻¹ with hts
      set ν : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞) ^ p⁻¹ with hν
      have ht0 : t ≠ 0 := natCast_rpow_ne_zero hSpos _
      have htt : t ≠ ∞ := natCast_rpow_ne_top hip
      have hν0 : ν ≠ 0 := natCast_rpow_ne_zero n.succ_pos _
      have hνt : ν ≠ ∞ := natCast_rpow_ne_top hip
      have htν0 : t * ν ≠ 0 := mul_ne_zero ht0 hν0
      have htνt : t * ν ≠ ∞ := ENNReal.mul_ne_top htt hνt
      set A : ℝ≥0∞ := (∑ j, (valP p (c j))⁻¹ ^ p) ^ p⁻¹ with hA

      have key : (t * ν)⁻¹ * A ≤ ⨆ i, (valInf (c i))⁻¹ := by
        have h2 : A ≤ ν * ⨆ j, (valP p (c j))⁻¹ := psum_le_mul_iSup _ hp
        have h3 : (⨆ j, (valP p (c j))⁻¹) ≤ t * ⨆ i, (valInf (c i))⁻¹ := by
          rw [ENNReal.mul_iSup]
          exact iSup_mono fun j =>
            inv_le_scale_mul_inv ht0 htt
              ((ih j).trans (mul_le_mul'
                (ENNReal.rpow_le_rpow
                  (by exact_mod_cast
                    Finset.le_sup (f := fun i => defectC (c i)) (mem_univ j))
                  hip)
                le_rfl))
        calc (t * ν)⁻¹ * A ≤ (t * ν)⁻¹ * (ν * (t * ⨆ i, (valInf (c i))⁻¹)) :=
              mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3))
          _ = ((t * ν)⁻¹ * (t * ν)) * ⨆ i, (valInf (c i))⁻¹ := by ring
          _ = ⨆ i, (valInf (c i))⁻¹ := by
              rw [ENNReal.inv_mul_cancel htν0 htνt, one_mul]
      have hkey' : (⨆ i, (valInf (c i))⁻¹)⁻¹ ≤ ((t * ν)⁻¹ * A)⁻¹ := ENNReal.inv_le_inv' key
      have hi0 : (t * ν)⁻¹ ≠ 0 := by simp only [ne_eq, ENNReal.inv_eq_zero]; exact htνt
      have hit : (t * ν)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr htν0
      calc (⨅ i, valInf (c i)) = (⨆ i, (valInf (c i))⁻¹)⁻¹ := by
            rw [ENNReal.inv_iSup]; exact iInf_congr fun i => (inv_inv _).symm
        _ ≤ ((t * ν)⁻¹ * A)⁻¹ := hkey'
        _ = (t * ν) * A⁻¹ := by rw [ENNReal.mul_inv (Or.inl hi0) (Or.inl hit), inv_inv]
        _ = ((S * (n + 1) : ℕ) : ℝ≥0∞) ^ p⁻¹ * A⁻¹ := by
            rw [Nat.cast_mul, ENNReal.mul_rpow_of_nonneg _ _ hip]

private lemma two_rpow_logb_div {d : ℕ} (hd : 0 < d) (p : ℝ) :
    (2 : ℝ≥0∞) ^ (Real.logb 2 d / p) = (d : ℝ≥0∞) ^ p⁻¹ := by
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [div_eq_mul_inv, ENNReal.rpow_mul]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
    ENNReal.ofReal_rpow_of_pos (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hD, ENNReal.ofReal_natCast]

theorem valP_le_two_rpow (p : ℝ) (hp : 0 < p) (T : RedTerm) :
    T.valP p ≤ (2 : ℝ≥0∞) ^ (Real.logb 2 T.defectO / p) * T.valInf := by
  rw [two_rpow_logb_div (defectO_pos T) p]; exact valP_le p hp T

theorem valInf_le_two_rpow (p : ℝ) (hp : 0 < p) (T : RedTerm) :
    T.valInf ≤ (2 : ℝ≥0∞) ^ (Real.logb 2 T.defectC / p) * T.valP p := by
  rw [two_rpow_logb_div (defectC_pos T) p]; exact valInf_le p hp T

theorem hard_of_soft {p : ℝ} (hp : 0 < p) {T : RedTerm} {η : ℝ}
    (h : ENNReal.ofReal (Real.exp η) ≤ T.valP p) :
    ENNReal.ofReal (Real.exp (η - Real.log T.defectO / p)) ≤ T.valInf := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  have hD : (0 : ℝ) < (T.defectO : ℝ) := by exact_mod_cast defectO_pos T
  set S : ℝ≥0∞ := (T.defectO : ℝ≥0∞) ^ p⁻¹ with hSdef
  have hS0 : S ≠ 0 := natCast_rpow_ne_zero (defectO_pos T) _
  have hSt : S ≠ ∞ := natCast_rpow_ne_top hip

  have hreal : Real.exp (η - Real.log T.defectO / p) * (T.defectO : ℝ) ^ (p⁻¹ : ℝ)
      = Real.exp η := by
    rw [Real.rpow_def_of_pos hD, Real.exp_sub, div_eq_mul_inv]
    exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
  have hSofReal : S = ENNReal.ofReal ((T.defectO : ℝ) ^ (p⁻¹ : ℝ)) := by
    rw [hSdef, ← ENNReal.ofReal_natCast T.defectO,
      ENNReal.ofReal_rpow_of_pos hD]
  have hmul : ENNReal.ofReal (Real.exp (η - Real.log T.defectO / p)) * S
      = ENNReal.ofReal (Real.exp η) := by
    rw [hSofReal, ← ENNReal.ofReal_mul (Real.exp_nonneg _), hreal]
  calc ENNReal.ofReal (Real.exp (η - Real.log T.defectO / p))
      = ENNReal.ofReal (Real.exp (η - Real.log T.defectO / p)) * (S * S⁻¹) := by
        rw [ENNReal.mul_inv_cancel hS0 hSt, mul_one]
    _ = (ENNReal.ofReal (Real.exp (η - Real.log T.defectO / p)) * S) * S⁻¹ := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (Real.exp η) * S⁻¹ := by rw [hmul]
    _ ≤ (S * T.valInf) * S⁻¹ := mul_le_mul' (h.trans (valP_le p hp T)) le_rfl
    _ = T.valInf * (S * S⁻¹) := by rw [mul_comm S, mul_assoc]
    _ = T.valInf := by rw [ENNReal.mul_inv_cancel hS0 hSt, mul_one]

theorem soft_of_hard {p : ℝ} (hp : 0 < p) {T : RedTerm} {η : ℝ}
    (h : ENNReal.ofReal (Real.exp η) ≤ T.valInf) :
    ENNReal.ofReal (Real.exp (η - Real.log T.defectC / p)) ≤ T.valP p := by
  have hip : (0 : ℝ) ≤ p⁻¹ := by positivity
  have hD : (0 : ℝ) < (T.defectC : ℝ) := by exact_mod_cast defectC_pos T
  set S : ℝ≥0∞ := (T.defectC : ℝ≥0∞) ^ p⁻¹ with hSdef
  have hS0 : S ≠ 0 := natCast_rpow_ne_zero (defectC_pos T) _
  have hSt : S ≠ ∞ := natCast_rpow_ne_top hip
  have hreal : Real.exp (η - Real.log T.defectC / p) * (T.defectC : ℝ) ^ (p⁻¹ : ℝ)
      = Real.exp η := by
    rw [Real.rpow_def_of_pos hD, Real.exp_sub, div_eq_mul_inv]
    exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
  have hSofReal : S = ENNReal.ofReal ((T.defectC : ℝ) ^ (p⁻¹ : ℝ)) := by
    rw [hSdef, ← ENNReal.ofReal_natCast T.defectC,
      ENNReal.ofReal_rpow_of_pos hD]
  have hmul : ENNReal.ofReal (Real.exp (η - Real.log T.defectC / p)) * S
      = ENNReal.ofReal (Real.exp η) := by
    rw [hSofReal, ← ENNReal.ofReal_mul (Real.exp_nonneg _), hreal]
  calc ENNReal.ofReal (Real.exp (η - Real.log T.defectC / p))
      = ENNReal.ofReal (Real.exp (η - Real.log T.defectC / p)) * (S * S⁻¹) := by
        rw [ENNReal.mul_inv_cancel hS0 hSt, mul_one]
    _ = (ENNReal.ofReal (Real.exp (η - Real.log T.defectC / p)) * S) * S⁻¹ := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (Real.exp η) * S⁻¹ := by rw [hmul]
    _ ≤ (S * T.valP p) * S⁻¹ := mul_le_mul' (h.trans (valInf_le p hp T)) le_rfl
    _ = T.valP p * (S * S⁻¹) := by rw [mul_comm S, mul_assoc]
    _ = T.valP p := by rw [ENNReal.mul_inv_cancel hS0 hSt, mul_one]

@[simp] theorem defectO_owedge_leaf {n : ℕ} (v : Fin (n + 1) → ℝ≥0∞) :
    (owedge n fun i => leaf (v i)).defectO = 1 := by
  simp [defectO, Finset.sup_const (univ_nonempty (α := Fin (n + 1)))]

noncomputable def dual : RedTerm → RedTerm
  | leaf v => leaf v⁻¹
  | tensor l r => par (dual l) (dual r)
  | par l r => tensor (dual l) (dual r)
  | oplus n c => owedge n fun i => dual (c i)
  | owedge n c => oplus n fun i => dual (c i)

@[simp] theorem defectO_dual : ∀ T : RedTerm, T.dual.defectO = T.defectC
  | leaf _ => rfl
  | tensor l r => by
      simp only [dual, defectO, defectC, defectO_dual l, defectO_dual r]
  | par l r => by
      simp only [dual, defectO, defectC, defectO_dual l, defectO_dual r]
  | oplus n c => by
      simp only [dual, defectO, defectC]
      exact Finset.sup_congr rfl fun i _ => defectO_dual (c i)
  | owedge n c => by
      simp only [dual, defectO, defectC]
      congr 1
      exact Finset.sup_congr rfl fun i _ => defectO_dual (c i)

@[simp] theorem defectC_dual : ∀ T : RedTerm, T.dual.defectC = T.defectO
  | leaf _ => rfl
  | tensor l r => by
      simp only [dual, defectO, defectC, defectC_dual l, defectC_dual r]
  | par l r => by
      simp only [dual, defectO, defectC, defectC_dual l, defectC_dual r]
  | oplus n c => by
      simp only [dual, defectO, defectC]
      congr 1
      exact Finset.sup_congr rfl fun i _ => defectC_dual (c i)
  | owedge n c => by
      simp only [dual, defectO, defectC]
      exact Finset.sup_congr rfl fun i _ => defectC_dual (c i)

@[simp] theorem valP_dual (p : ℝ) : ∀ T : RedTerm, T.dual.valP p = (T.valP p)⁻¹
  | leaf _ => rfl
  | tensor l r => by
      simp only [dual, valP, valP_dual p l, valP_dual p r, inv_inv]
  | par l r => by
      simp only [dual, valP, valP_dual p l, valP_dual p r, inv_inv]
  | oplus n c => by
      have hsum : (∑ i, (valP p ((c i).dual))⁻¹ ^ p) = ∑ i, valP p (c i) ^ p :=
        Finset.sum_congr rfl fun i _ => by rw [valP_dual p (c i), inv_inv]
      simp only [dual, valP, hsum]
  | owedge n c => by
      have hsum : (∑ i, valP p ((c i).dual) ^ p) = ∑ i, (valP p (c i))⁻¹ ^ p :=
        Finset.sum_congr rfl fun i _ => by rw [valP_dual p (c i)]
      simp only [dual, valP, hsum, inv_inv]

@[simp] theorem valInf_dual : ∀ T : RedTerm, T.dual.valInf = T.valInf⁻¹
  | leaf _ => rfl
  | tensor l r => by
      simp only [dual, valInf, valInf_dual l, valInf_dual r, inv_inv]
  | par l r => by
      simp only [dual, valInf, valInf_dual l, valInf_dual r, inv_inv]
  | oplus n c => by
      simp only [dual, valInf, ENNReal.inv_iSup]
      exact iInf_congr fun i => valInf_dual (c i)
  | owedge n c => by
      simp only [dual, valInf, ENNReal.inv_iInf]
      exact iSup_congr fun i => by rw [valInf_dual (c i)]

end RedTerm

section LSE

noncomputable def lse (p : ℝ) {n : ℕ} (s : Fin (n + 1) → ℝ) : ℝ :=
  p⁻¹ * Real.log (∑ i, Real.exp (p * s i))

variable {n : ℕ} {p : ℝ}

theorem sup'_le_lse (hp : 0 < p) (s : Fin (n + 1) → ℝ) :
    univ.sup' univ_nonempty s ≤ lse p s := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hpos : (0 : ℝ) < ∑ j, Real.exp (p * s j) :=
    lt_of_lt_of_le (Real.exp_pos _)
      (Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (mem_univ i))
  have hle : Real.exp (p * s i) ≤ ∑ j, Real.exp (p * s j) :=
    Finset.single_le_sum (f := fun j => Real.exp (p * s j))
      (fun j _ => (Real.exp_pos _).le) (mem_univ i)
  have h2 : p * s i ≤ Real.log (∑ j, Real.exp (p * s j)) := by
    calc p * s i = Real.log (Real.exp (p * s i)) := (Real.log_exp _).symm
      _ ≤ Real.log (∑ j, Real.exp (p * s j)) :=
          (Real.log_le_log_iff (Real.exp_pos _) hpos).mpr hle
  calc s i = p⁻¹ * (p * s i) := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ ≤ lse p s := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem lse_le_sup'_add (hp : 0 < p) (s : Fin (n + 1) → ℝ) :
    lse p s ≤ univ.sup' univ_nonempty s + p⁻¹ * Real.log (n + 1) := by
  set M : ℝ := univ.sup' univ_nonempty s with hM
  have h1 : (∑ j, Real.exp (p * s j)) ≤ ((n : ℝ) + 1) * Real.exp (p * M) := by
    have h := Finset.sum_le_card_nsmul univ (fun j => Real.exp (p * s j))
      (Real.exp (p * M))
      (fun j _ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Finset.le_sup' s (mem_univ j)) hp.le))
    simpa [Finset.card_univ, nsmul_eq_mul, add_comm] using h
  have hpos : (0 : ℝ) < ∑ j, Real.exp (p * s j) :=
    lt_of_lt_of_le (Real.exp_pos _)
      (Finset.single_le_sum (fun j _ => (Real.exp_pos _).le) (mem_univ 0))
  have h2 : Real.log (∑ j, Real.exp (p * s j)) ≤ Real.log ((n : ℝ) + 1) + p * M := by
    calc Real.log (∑ j, Real.exp (p * s j))
        ≤ Real.log (((n : ℝ) + 1) * Real.exp (p * M)) :=
          (Real.log_le_log_iff hpos (by positivity)).mpr h1
      _ = Real.log ((n : ℝ) + 1) + p * M := by
          rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  calc lse p s ≤ p⁻¹ * (Real.log ((n : ℝ) + 1) + p * M) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = M + p⁻¹ * Real.log ((n : ℝ) + 1) := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul, add_comm]

theorem hard_margin_of_lse_le (hp : 0 < p) {s : Fin (n + 1) → ℝ} {η : ℝ}
    (h : lse p s ≤ -η) : univ.sup' univ_nonempty s ≤ -η :=
  (sup'_le_lse hp s).trans h

theorem lse_le_of_hard_margin (hp : 0 < p) {s : Fin (n + 1) → ℝ} {η : ℝ}
    (h : univ.sup' univ_nonempty s ≤ -η) :
    lse p s ≤ -η + p⁻¹ * Real.log (n + 1) :=
  (lse_le_sup'_add hp s).trans (by linarith)

end LSE

end Qtsl.DefectBound
