import QtslAux.Imprecise.TowerWitness
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # The Hurwicz criterion is not an envelope bound: inclusion witnesses

The lower and upper expectations of a finite credal set move in opposite
directions as the set grows: `lowerE` is antitone and `upperE` is monotone
along family inclusion (`lowerE_anti_of_subFam`, `upperE_mono_of_subFam`).
Consequently the truth of any single envelope bound — `lo ≤ lowerE M f`,
`upperE M f ≤ hi`, `lo ≤ upperE M f`, or `lowerE M f ≤ hi` — is antitone or
monotone along every inclusion chain of credal sets, whatever the gamble and
threshold.

The Hurwicz blend `hurwicz α M f = α * upperE M f + (1 - α) * lowerE M f`
obeys no such discipline at interior `α`.  This module exhibits a
three-element inclusion chain `M0 ⊆ M1 ⊆ M2` of credal sets on `Bool` and a
single gamble (the goal indicator) whose Hurwicz value at `α = 1/2` runs
`1/2`, `1/4`, `1/2`: the lower-bound judgment at threshold `1/2` reads true,
false, true along the chain (`hurwicz_ge_pattern`), and the upper-bound
judgment at threshold `1/4` reads false, true, false (`hurwicz_le_pattern`).
Neither pattern is antitone or monotone, so no choice of gamble and
threshold renders the interior-`α` Hurwicz judgment as any one of the four
envelope bounds; the four corollaries `hurwicz_ge_ne_*` state this
quantifier-explicitly, against every candidate gamble and threshold at once.
The dual statements against the upper-bound Hurwicz judgment follow the same
way from `hurwicz_le_pattern` and are omitted.

This is the family-inclusion face of the operator's root-only status,
complementing the record-composition face of
`QtslAux.Imprecise.TowerWitness` (`no_tower_at_half`): there the interior
blend fails to commute with kernel composition; here it fails to be an
entailment-shaped reading of the credal set at a single stage, because it
mixes a quantity that shrinks under new admitted laws with one that grows.
-/

namespace Qtsl.Imprecise

open Finset

section SubFam

variable {X : Type*} [Fintype X] {ι κ : Type*} [Fintype ι] [Nonempty ι]
  [Fintype κ] [Nonempty κ]

/-- Family inclusion: every member of `M` occurs in `M'`.  This is inclusion
of the presented credal sets; the index types are free, so repetitions and
reindexings are transparent. -/
def SubFam (M : ι → FinPMF X) (M' : κ → FinPMF X) : Prop :=
  ∀ i, ∃ j, M' j = M i

/-- The lower expectation is antitone along family inclusion: admitting more
laws can only drive the worst case down. -/
theorem lowerE_anti_of_subFam {M : ι → FinPMF X} {M' : κ → FinPMF X}
    (h : SubFam M M') (f : X → ℚ) : lowerE M' f ≤ lowerE M f :=
  le_lowerE fun i => by
    obtain ⟨j, hj⟩ := h i
    rw [← hj]
    exact lowerE_le_exp M' f j

/-- The upper expectation is monotone along family inclusion: admitting more
laws can only drive the best case up. -/
theorem upperE_mono_of_subFam {M : ι → FinPMF X} {M' : κ → FinPMF X}
    (h : SubFam M M') (f : X → ℚ) : upperE M f ≤ upperE M' f :=
  upperE_le fun i => by
    obtain ⟨j, hj⟩ := h i
    rw [← hj]
    exact exp_le_upperE M' f j

end SubFam

namespace InclusionWitness

open TowerWitness (bern)

/-- The goal indicator on a single stage. -/
def ind : Bool → ℚ := fun b => cond b 1 0

theorem exp_bern_ind (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (bern p h0 h1).exp ind = p := by
  simp [FinPMF.exp, TowerWitness.bern, ind, Fintype.univ_bool]

/-- The fair coin. -/
def phalf : FinPMF Bool := bern (1/2) (by norm_num) (by norm_num)

/-- The coin that never reaches the goal. -/
def pzero : FinPMF Bool := bern 0 (by norm_num) (by norm_num)

/-- The coin that always reaches the goal. -/
def pone : FinPMF Bool := bern 1 (by norm_num) (by norm_num)

theorem exp_phalf : phalf.exp ind = 1/2 := by
  unfold phalf; exact exp_bern_ind _ _ _

theorem exp_pzero : pzero.exp ind = 0 := by
  unfold pzero; exact exp_bern_ind _ _ _

theorem exp_pone : pone.exp ind = 1 := by
  unfold pone; exact exp_bern_ind _ _ _

/-- The singleton credal set `{1/2}`. -/
def M0 : Fin 1 → FinPMF Bool := ![phalf]

/-- The credal set `{1/2, 0}`. -/
def M1 : Fin 2 → FinPMF Bool := ![phalf, pzero]

/-- The credal set `{1/2, 0, 1}`. -/
def M2 : Fin 3 → FinPMF Bool := ![phalf, pzero, pone]

theorem subFam_M0_M1 : SubFam M0 M1 := by
  intro i
  fin_cases i
  exact ⟨0, rfl⟩

theorem subFam_M1_M2 : SubFam M1 M2 := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem lowerE_M0 : lowerE M0 ind = 1/2 :=
  le_antisymm (by simpa [M0, exp_phalf] using lowerE_le_exp M0 ind 0)
    (le_lowerE fun i => by fin_cases i; simp [M0, exp_phalf])

theorem upperE_M0 : upperE M0 ind = 1/2 :=
  le_antisymm (upperE_le fun i => by fin_cases i; simp [M0, exp_phalf])
    (by simpa [M0, exp_phalf] using exp_le_upperE M0 ind 0)

theorem lowerE_M1 : lowerE M1 ind = 0 :=
  le_antisymm (by simpa [M1, exp_pzero] using lowerE_le_exp M1 ind 1)
    (le_lowerE fun i => by
      fin_cases i <;> simp [M1, exp_phalf, exp_pzero])

theorem upperE_M1 : upperE M1 ind = 1/2 :=
  le_antisymm
    (upperE_le fun i => by
      fin_cases i <;> simp [M1, exp_phalf, exp_pzero])
    (by simpa [M1, exp_phalf] using exp_le_upperE M1 ind 0)

theorem lowerE_M2 : lowerE M2 ind = 0 :=
  le_antisymm (by simpa [M2, exp_pzero] using lowerE_le_exp M2 ind 1)
    (le_lowerE fun i => by
      fin_cases i <;> simp [M2, exp_phalf, exp_pzero, exp_pone])

theorem upperE_M2 : upperE M2 ind = 1 :=
  le_antisymm
    (upperE_le fun i => by
      fin_cases i <;> simp [M2, exp_phalf, exp_pzero, exp_pone]; norm_num)
    (by simpa [M2, exp_pone] using exp_le_upperE M2 ind 2)

theorem hurwicz_M0 : hurwicz (1/2) M0 ind = 1/2 := by
  simp only [hurwicz, lowerE_M0, upperE_M0]; norm_num

theorem hurwicz_M1 : hurwicz (1/2) M1 ind = 1/4 := by
  simp only [hurwicz, lowerE_M1, upperE_M1]; norm_num

theorem hurwicz_M2 : hurwicz (1/2) M2 ind = 1/2 := by
  simp only [hurwicz, lowerE_M2, upperE_M2]; norm_num

/-- Along the inclusion chain `M0 ⊆ M1 ⊆ M2`, the lower-bound Hurwicz
judgment `1/2 ≤ hurwicz (1/2) · ind` reads true, false, true: neither
antitone nor monotone in the credal set. -/
theorem hurwicz_ge_pattern :
    SubFam M0 M1 ∧ SubFam M1 M2 ∧
      (1/2 ≤ hurwicz (1/2) M0 ind) ∧ ¬ (1/2 ≤ hurwicz (1/2) M1 ind) ∧
      (1/2 ≤ hurwicz (1/2) M2 ind) :=
  ⟨subFam_M0_M1, subFam_M1_M2, hurwicz_M0.ge,
    by rw [hurwicz_M1]; norm_num, hurwicz_M2.ge⟩

/-- Along the same chain, the upper-bound Hurwicz judgment
`hurwicz (1/2) · ind ≤ 1/4` reads false, true, false: the dual pattern. -/
theorem hurwicz_le_pattern :
    ¬ (hurwicz (1/2) M0 ind ≤ 1/4) ∧ (hurwicz (1/2) M1 ind ≤ 1/4) ∧
      ¬ (hurwicz (1/2) M2 ind ≤ 1/4) :=
  ⟨by rw [hurwicz_M0]; norm_num, hurwicz_M1.le,
    by rw [hurwicz_M2]; norm_num⟩

/-- No gamble and threshold make the lower-prevision floor `a ≤ lowerE · g`
agree with the interior-Hurwicz lower-bound judgment across the chain: the
floor is antitone along inclusion and the Hurwicz pattern is not. -/
theorem hurwicz_ge_ne_lowerE_ge (g : Bool → ℚ) (a : ℚ) :
    ¬ (((a ≤ lowerE M0 g) ↔ (1/2 ≤ hurwicz (1/2) M0 ind)) ∧
       ((a ≤ lowerE M1 g) ↔ (1/2 ≤ hurwicz (1/2) M1 ind)) ∧
       ((a ≤ lowerE M2 g) ↔ (1/2 ≤ hurwicz (1/2) M2 ind))) := by
  rintro ⟨_, h1, h2⟩
  have hT2 : a ≤ lowerE M2 g := h2.mpr hurwicz_M2.ge
  have hT1 : (1:ℚ)/2 ≤ hurwicz (1/2) M1 ind :=
    h1.mp (hT2.trans (lowerE_anti_of_subFam subFam_M1_M2 g))
  rw [hurwicz_M1] at hT1
  norm_num at hT1

/-- No gamble and threshold make the upper-prevision ceiling
`upperE · g ≤ a` agree with the interior-Hurwicz lower-bound judgment across
the chain. -/
theorem hurwicz_ge_ne_upperE_le (g : Bool → ℚ) (a : ℚ) :
    ¬ (((upperE M0 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M0 ind)) ∧
       ((upperE M1 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M1 ind)) ∧
       ((upperE M2 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M2 ind))) := by
  rintro ⟨_, h1, h2⟩
  have hT2 : upperE M2 g ≤ a := h2.mpr hurwicz_M2.ge
  have hT1 : (1:ℚ)/2 ≤ hurwicz (1/2) M1 ind :=
    h1.mp ((upperE_mono_of_subFam subFam_M1_M2 g).trans hT2)
  rw [hurwicz_M1] at hT1
  norm_num at hT1

/-- No gamble and threshold make the upper-prevision witness bound
`a ≤ upperE · g` agree with the interior-Hurwicz lower-bound judgment across
the chain: the witness bound is monotone along inclusion and the Hurwicz
pattern is not. -/
theorem hurwicz_ge_ne_upperE_ge (g : Bool → ℚ) (a : ℚ) :
    ¬ (((a ≤ upperE M0 g) ↔ (1/2 ≤ hurwicz (1/2) M0 ind)) ∧
       ((a ≤ upperE M1 g) ↔ (1/2 ≤ hurwicz (1/2) M1 ind)) ∧
       ((a ≤ upperE M2 g) ↔ (1/2 ≤ hurwicz (1/2) M2 ind))) := by
  rintro ⟨h0, h1, _⟩
  have hT0 : a ≤ upperE M0 g := h0.mpr hurwicz_M0.ge
  have hT1 : (1:ℚ)/2 ≤ hurwicz (1/2) M1 ind :=
    h1.mp (hT0.trans (upperE_mono_of_subFam subFam_M0_M1 g))
  rw [hurwicz_M1] at hT1
  norm_num at hT1

/-- No gamble and threshold make the lower-prevision witness bound
`lowerE · g ≤ a` agree with the interior-Hurwicz lower-bound judgment across
the chain. -/
theorem hurwicz_ge_ne_lowerE_le (g : Bool → ℚ) (a : ℚ) :
    ¬ (((lowerE M0 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M0 ind)) ∧
       ((lowerE M1 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M1 ind)) ∧
       ((lowerE M2 g ≤ a) ↔ (1/2 ≤ hurwicz (1/2) M2 ind))) := by
  rintro ⟨h0, h1, _⟩
  have hT0 : lowerE M0 g ≤ a := h0.mpr hurwicz_M0.ge
  have hT1 : (1:ℚ)/2 ≤ hurwicz (1/2) M1 ind :=
    h1.mp ((lowerE_anti_of_subFam subFam_M0_M1 g).trans hT0)
  rw [hurwicz_M1] at hT1
  norm_num at hT1

end InclusionWitness

end Qtsl.Imprecise
