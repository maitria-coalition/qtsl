import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # Glue lemmas: rational certificate data to real semantics

This module collects small alias and cast lemmas that connect certificate-side
rational data to the real-valued semantics used by the soundness theorems, and
records denotational identities for derived temporal operators.

Principal declarations:

* `sound_QSatFromRegion`: membership of an evaluation point in a region on
  which a predicate holds everywhere yields the predicate at the point;
  `sound_QSatFromRegion_sublevel` specializes the region to a rational
  polynomial sublevel set, via the cast lemmas `rootEval_eval_cast`,
  `rootEval_sublevel_iff`, and `rootEval_box_iff` (evaluation over `ℚ` agrees
  with evaluation of the coefficient-cast polynomial over `ℝ`).
* `taylorLeaf_le_exp`, `taylorLeaf_rat_le_exp`: a rational lower bound on a
  truncated exponential Taylor sum is a lower bound on `Real.exp`, since the
  remainder is nonnegative for nonnegative arguments.
* `negF_denot_subset`, `sound_NegFAlias`: paths that never satisfy a predicate
  are contained in the bounded-horizon never-satisfies event, transporting
  measure lower bounds accordingly.
* `sugarAvoid_denot`, `sugarGF_denot`, `sugarFG_denot`: denotational
  identities unfolding the avoidance, unconditional recurrence (trivial
  request), and finitely-often (empty response) sugar forms.
-/

open Filter Finset MeasureTheory

namespace Qtsl.Aliases

theorem sound_QSatFromRegion {X : Type*} {R : Set X} {sat : X → Prop} {x₀ : X}
    (hchild : ∀ x ∈ R, sat x) (heval : x₀ ∈ R) : sat x₀ :=
  hchild x₀ heval

theorem rootEval_eval_cast {σ : Type*} (P : MvPolynomial σ ℚ) (xq : σ → ℚ) :
    ((MvPolynomial.eval xq P : ℚ) : ℝ)
      = MvPolynomial.eval (fun i => (xq i : ℝ)) (MvPolynomial.map (Rat.castHom ℝ) P) := by
  rw [MvPolynomial.eval_map]
  simpa [Function.comp_def] using MvPolynomial.eval₂_comp (Rat.castHom ℝ) xq P

theorem rootEval_sublevel_iff {σ : Type*} (P : MvPolynomial σ ℚ) (xq : σ → ℚ)
    (thr : ℚ) :
    MvPolynomial.eval xq P ≤ thr
      ↔ MvPolynomial.eval (fun i => (xq i : ℝ))
          (MvPolynomial.map (Rat.castHom ℝ) P) ≤ (thr : ℝ) := by
  rw [← rootEval_eval_cast]
  exact Rat.cast_le.symm

theorem rootEval_box_iff {ι : Type*} (aq bq xq : ι → ℚ) :
    (∀ i, aq i ≤ xq i ∧ xq i ≤ bq i)
      ↔ ∀ i, ((aq i : ℝ) ≤ (xq i : ℝ) ∧ (xq i : ℝ) ≤ (bq i : ℝ)) := by
  norm_cast

theorem sound_QSatFromRegion_sublevel {σ : Type*} {sat : (σ → ℝ) → Prop}
    {P : MvPolynomial σ ℚ} {thr : ℚ} {xq : σ → ℚ}
    (hchild : ∀ x ∈ {x : σ → ℝ |
      MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P) ≤ (thr : ℝ)}, sat x)
    (heval : MvPolynomial.eval xq P ≤ thr) :
    sat (fun i => (xq i : ℝ)) :=
  sound_QSatFromRegion hchild ((rootEval_sublevel_iff P xq thr).1 heval)

theorem taylorLeaf_le_exp {q x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hq : q ≤ ∑ k ∈ range (n + 1), x ^ k / (Nat.factorial k : ℝ)) :
    q ≤ Real.exp x :=
  hq.trans (Real.sum_le_exp_of_nonneg hx _)

theorem taylorLeaf_rat_le_exp {qq θ : ℚ} {T n : ℕ} (hθ : 0 ≤ θ)
    (hleaf : qq ≤ ∑ k ∈ range (n + 1), (θ * T) ^ k / (Nat.factorial k : ℚ)) :
    (qq : ℝ) ≤ Real.exp (θ * T) := by
  have hcast : (qq : ℝ)
      ≤ ∑ k ∈ range (n + 1), ((θ : ℝ) * (T : ℝ)) ^ k / (Nat.factorial k : ℝ) := by
    have h : ((qq : ℚ) : ℝ)
        ≤ ((∑ k ∈ range (n + 1), (θ * T) ^ k / (Nat.factorial k : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.2 hleaf
    push_cast at h
    exact h
  exact taylorLeaf_le_exp
    (mul_nonneg (by exact_mod_cast hθ) (Nat.cast_nonneg T)) hcast

theorem negF_denot_subset {S : Type*} (sat : S → Prop) (T : ℕ) :
    {ω : ℕ → S | ∀ n, ¬ sat (ω n)} ⊆ {ω : ℕ → S | ¬ ∃ k ≤ T, sat (ω k)} := by
  rintro ω hω ⟨k, -, hk⟩
  exact hω k hk

theorem sound_NegFAlias {S : Type*} [MeasurableSpace S]
    (μ : Measure (ℕ → S)) {sat : S → Prop} {b : ENNReal} {T : ℕ}
    (h : b ≤ μ {ω | ∀ n, ¬ sat (ω n)}) :
    b ≤ μ {ω | ¬ ∃ k ≤ T, sat (ω k)} :=
  h.trans (measure_mono (negF_denot_subset sat T))

theorem sugarAvoid_denot {S : Type*} (B : Set S) :
    {ω : ℕ → S | ∀ n, ω n ∉ B} = {ω : ℕ → S | ∀ n, ω n ∈ Bᶜ} := rfl

theorem sugarGF_denot {S : Type*} (G : Set S) (ω : ℕ → S) :
    ((∃ᶠ n in atTop, ω n ∈ (Set.univ : Set S)) → ∃ᶠ n in atTop, ω n ∈ G)
      ↔ ∃ᶠ n in atTop, ω n ∈ G := by
  have htriv : ∃ᶠ n in atTop, ω n ∈ (Set.univ : Set S) :=
    (Eventually.of_forall fun n => Set.mem_univ (ω n)).frequently
  exact ⟨fun h => h htriv, fun h _ => h⟩

theorem sugarFG_denot {S : Type*} (B : Set S) (ω : ℕ → S) :
    ((∃ᶠ n in atTop, ω n ∈ B) → ∃ᶠ n in atTop, ω n ∈ (∅ : Set S))
      ↔ ∀ᶠ n in atTop, ω n ∉ B := by
  simp [imp_false, not_frequently]

end Qtsl.Aliases
