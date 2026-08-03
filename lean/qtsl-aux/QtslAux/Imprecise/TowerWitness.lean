import QtslAux.Imprecise.Compose

/-! # The Hurwicz criterion is not tower-consistent: explicit witnesses

This module gives concrete rational witnesses separating the root and stagewise
evaluations of the Hurwicz criterion at `α = 1/2`, complementing the endpoint
agreements `stagewiseHurwicz_zero` and `stagewiseHurwicz_one`. All computations
use Bernoulli measures `bern p` on `Bool` and the goal indicator `goalInd`.

* For the credal pair `M₁`, `K`: the composite lower and upper expectations are
  `1/8` and `13/16` (`lowerE_eq`, `upperE_eq`); the root Hurwicz value is
  `15/32` (`root_half_eq`) while the stagewise value is `14/32`
  (`stagewise_half_eq`), so `stagewise_lt_root`.
* For the pair `M₁'`, `K'` the inequality reverses: root `14/64` versus
  stagewise `15/64` (`root_lt_stagewise'`).

Together the witnesses show that for `0 < α < 1` neither inequality between the
root and stagewise Hurwicz evaluations holds in general (`no_tower_at_half`).
-/

namespace Qtsl.Imprecise.TowerWitness

open Qtsl.Imprecise

def bern (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinPMF Bool where
  prob := fun b => cond b p (1 - p)
  nonneg := fun b => by cases b <;> simpa using by linarith
  total := by simp [Fintype.univ_bool]

def goalInd : Bool × Bool → ℚ := fun xy => cond xy.2 1 0

def M₁ : Bool → FinPMF Bool := fun i =>
  bern (cond i (3/4) (1/4)) (by cases i <;> norm_num) (by cases i <;> norm_num)

def K : (x : Bool) → Bool → FinPMF Bool := fun x j =>
  cond x
    (bern (cond j 1 (1/2)) (by cases j <;> norm_num) (by cases j <;> norm_num))
    (bern (cond j (1/4) 0) (by cases j <;> norm_num) (by cases j <;> norm_num))

theorem stagewise_zero_eq : stagewiseHurwicz 0 M₁ K goalInd = 1/8 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁, K, bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem stagewise_one_eq : stagewiseHurwicz 1 M₁ K goalInd = 13/16 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁, K, bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem lowerE_eq : lowerE (compFam M₁ K) goalInd = 1/8 := by
  rw [← stagewiseHurwicz_zero]
  exact stagewise_zero_eq

theorem upperE_eq : upperE (compFam M₁ K) goalInd = 13/16 := by
  rw [← stagewiseHurwicz_one]
  exact stagewise_one_eq

theorem root_half_eq : rootHurwicz (1/2) M₁ K goalInd = 15/32 := by
  rw [rootHurwicz_eq_mix, stagewise_one_eq, stagewise_zero_eq]
  norm_num

theorem stagewise_half_eq : stagewiseHurwicz (1/2) M₁ K goalInd = 14/32 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁, K, bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem no_tower_at_half :
    stagewiseHurwicz (1/2) M₁ K goalInd ≠ rootHurwicz (1/2) M₁ K goalInd := by
  rw [stagewise_half_eq, root_half_eq]
  norm_num

theorem stagewise_lt_root :
    stagewiseHurwicz (1/2) M₁ K goalInd < rootHurwicz (1/2) M₁ K goalInd := by
  rw [stagewise_half_eq, root_half_eq]
  norm_num

def M₁' : Bool → FinPMF Bool := fun i =>
  bern (cond i (1/4) 0) (by cases i <;> norm_num) (by cases i <;> norm_num)

def K' : (x : Bool) → Bool → FinPMF Bool := fun x j =>
  cond x
    (bern (cond j (1/4) 0) (by cases j <;> norm_num) (by cases j <;> norm_num))
    (bern (1/4) (by norm_num) (by norm_num))

theorem stagewise_zero_eq' : stagewiseHurwicz 0 M₁' K' goalInd = 3/16 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁', K', bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem stagewise_one_eq' : stagewiseHurwicz 1 M₁' K' goalInd = 1/4 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁', K', bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem root_half_eq' : rootHurwicz (1/2) M₁' K' goalInd = 14/64 := by
  rw [rootHurwicz_eq_mix, stagewise_one_eq', stagewise_zero_eq']
  norm_num

theorem stagewise_half_eq' :
    stagewiseHurwicz (1/2) M₁' K' goalInd = 15/64 := by
  simp [stagewiseHurwicz, hurwicz, lowerE, upperE, M₁', K', bern, goalInd,
    FinPMF.exp, Fintype.univ_bool, Finset.inf'_insert, Finset.inf'_singleton,
    Finset.sup'_insert, Finset.sup'_singleton]
  norm_num [min_def, max_def]

theorem root_lt_stagewise' :
    rootHurwicz (1/2) M₁' K' goalInd < stagewiseHurwicz (1/2) M₁' K' goalInd := by
  rw [stagewise_half_eq', root_half_eq']
  norm_num

end Qtsl.Imprecise.TowerWitness
