import SuFunctor.Universe.Fragments
import SuFunctor.Universe.CoupledJudgment
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The Hausdorff–KL embedding of credal sets, and multiplicative-weight updating

Two embeddings turn a credal set — a set `M` of probability states; for
the classical (Cozman credal-network) reading, closed and convex, the
class the credal-body atlas places via its radial embedding
(`SuFunctor.Universe.CredalPoset`) — into a penalty functional on the
flat carrier:

* the **wall** `probWall M` (`SuFunctor.Universe.ProbCarrier`) — the
  possibilistic reading: `0` on `M`, `⊤` off it;
* the **Hausdorff–KL embedding** `hkl` / `hklSet` — the graded reading:
  `μ ↦ ⨅ ν ∈ M, D(μ ‖ ν)`, zero exactly on the set (finite stratum:
  `hkl_eq_zero_iff`) and relative-entropy-graded off it.  The scored
  state sits in the **first** KL slot, extending the precise Gibbs
  chart `D(· ‖ p)` from single reference laws to sets — the directed
  (one-sided) Hausdorff distance in relative entropy from the point
  `{μ}` to `M`; the inner minimization is Csiszár's reverse information
  projection.

The **multiplicative-weight update** `mwu L φ = φ + surprisal L·` —
add the expected negative log-likelihood, then (where a statement wants
it) renormalize — is the normative belief update on penalty
functionals; on the precise Gibbs chart it performs Bayes/Pearl
conditioning, by the Gibbs/Donsker–Varadhan variational identity.  This
module proves what it does to the two credal embeddings, and thereby
adjudicates the KL direction: **the first-slot direction is forced**.

Main results (finite outcome space `V`, likelihoods `0 ≤ L ≤ 1`, all
statements total in `ℝ≥0∞`):

* `klq_add_surprisal` (the chain-rule engine): for `Z_ν := E_ν[L] > 0`,
  `D(μ‖ν) + surprisal L μ = D(μ‖ν∗L) + negLog Z_ν` — Bayes conditioning
  plus a marginal-likelihood tilt, every `⊤`-case included;
* `mwu_hklW_eq` (the square, weighted and exact): the update of a
  *tilted* embedding is the tilted embedding of the Bayes posteriors
  with tilts incremented by `negLog Z` — exactly **likelihood updating
  of weighted sets of probabilities** in the sense of Halpern–Leung
  (arXiv:1302.5681, §likelihood updating; weights `α = e^{-t}`,
  sup-normalized weights = inf-zero tilts).  Plain credal sets are the
  tilt-zero slice: one update exits the plain class into the weighted
  class, and the weights are forced by the update, not chosen;
* `iInf_mwu_hklW`: the normalization constant is `negLog` of the best
  marginal likelihood — the Halpern–Leung weight normalizer;
* `argmin_mwu_hkl_eq_mluSet` (the argmin face): the minimum-penalty set
  of the updated embedding is the **maximum-likelihood update** of
  Gilboa–Schmeidler ("Updating ambiguous beliefs", J. Econ. Theory 59,
  1993) — condition exactly the priors of maximal marginal likelihood —
  which on belief-function credal sets is Dempster conditioning;
* `Witness.gbr_cross_sums_ne` : plain generalized-Bayes / element-wise
  conditioning of the set (the Cozman-style recipe, tilts forgotten)
  does **not** commute with the update — a two-prior three-outcome
  counterexample in exact rationals;
* `flip_add_surprisal_eq_top` / `mwu_hklFlip_eq_top` (direction
  adjudication): with the KL arguments reversed, the updated penalty is
  identically `⊤` — the vacuous, information-free belief state —
  whenever the evidence excludes mass of every element (already at
  singleton sets, where the first-slot direction is the classical
  variational identity).  The failure is properness-collapse, not a
  finite mismatch: no additive renormalization repairs it;
* `klq_add_surprisal_eq_top_of_evProb_eq_zero`: the vacuous-conditioning
  fence (evidence of zero probability under every element), stated as a
  collapse theorem rather than left tacit;
* `mwu_probWall_eq_zero_iff`: the contrast — updating the *wall*
  embedding can only intersect (kill states), never reweight: the
  possibilistic reading performs no Bayesian learning, which is exactly
  the gap the graded embedding closes.

Everything is elementary finite-sum bookkeeping over `Real.log`; the
only conventions are the standard `0 · log 0 = 0` (automatic, since
`Real.log 0 = 0`) and the `⊤`-guards written into `klq` and `negLog`.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open Finset

namespace HausdorffKL

variable {V : Type*} [Fintype V]

/-! ## Extended negative logarithm -/

/-- Extended negative logarithm: `⊤` at and below zero, `-log t`
(as an extended nonnegative real) for positive `t`.  On `(0, 1]` this
is exact surprisal; above `1` it clamps to `0` (the theorems below keep
likelihoods in `[0, 1]`, where no clamping occurs). -/
noncomputable def negLog (t : ℝ) : ℝ≥0∞ :=
  if t ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log t)

theorem negLog_of_nonpos {t : ℝ} (h : t ≤ 0) : negLog t = ⊤ := if_pos h

theorem negLog_of_pos {t : ℝ} (h : 0 < t) :
    negLog t = ENNReal.ofReal (-Real.log t) := if_neg (not_le.mpr h)

@[simp] theorem negLog_one : negLog 1 = 0 := by
  rw [negLog_of_pos one_pos, Real.log_one, neg_zero, ENNReal.ofReal_zero]

theorem negLog_lt_top {t : ℝ} (h : 0 < t) : negLog t < ⊤ := by
  rw [negLog_of_pos h]; exact ENNReal.ofReal_lt_top

theorem negLog_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < negLog t := by
  rw [negLog_of_pos h0]
  exact ENNReal.ofReal_pos.mpr (by linarith [Real.log_neg h0 h1])

/-- `negLog` is antitone on the positives. -/
theorem negLog_le_negLog {s t : ℝ} (h0 : 0 < s) (hst : s ≤ t) :
    negLog t ≤ negLog s := by
  rw [negLog_of_pos h0, negLog_of_pos (h0.trans_le hst)]
  exact ENNReal.ofReal_le_ofReal
    (neg_le_neg (Real.log_le_log h0 hst))

/-- `negLog` is injective on `(0, 1]`. -/
theorem negLog_inj {s t : ℝ} (h0s : 0 < s) (h0t : 0 < t)
    (h1s : s ≤ 1) (h1t : t ≤ 1) (h : negLog s = negLog t) : s = t := by
  rw [negLog_of_pos h0s, negLog_of_pos h0t] at h
  have hs : (0:ℝ) ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos h0s.le h1s)
  have ht : (0:ℝ) ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos h0t.le h1t)
  have hlog : Real.log s = Real.log t := by
    have := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal ht] at this
    linarith
  calc s = Real.exp (Real.log s) := (Real.exp_log h0s).symm
  _ = Real.exp (Real.log t) := by rw [hlog]
  _ = t := Real.exp_log h0t

theorem negLog_eq_zero_iff {t : ℝ} (h : 0 < t) : negLog t = 0 ↔ 1 ≤ t := by
  rw [negLog_of_pos h, ENNReal.ofReal_eq_zero, neg_nonpos]
  constructor
  · intro hlog
    calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr hlog
    _ = t := Real.exp_log h
  · exact Real.log_nonneg

/-- Surprisals multiply likelihoods: `negLog a + negLog b = negLog (a * b)`
on `(0, 1]` (in fact on the positives). -/
theorem negLog_add_negLog {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    negLog a + negLog b = negLog (a * b) := by
  rw [negLog_of_pos ha, negLog_of_pos hb, negLog_of_pos (mul_pos ha hb),
    ← ENNReal.ofReal_add (neg_nonneg.mpr (Real.log_nonpos ha.le ha1))
      (neg_nonneg.mpr (Real.log_nonpos hb.le hb1)),
    Real.log_mul ha.ne' hb.ne']
  congr 1
  ring

/-! ## Relative entropy on the flat carrier -/

/-- Absolute continuity on the finite carrier: support containment. -/
def AbsCont (μ ν : ProbState V) : Prop :=
  ∀ v, (ν : V → ℝ) v = 0 → (μ : V → ℝ) v = 0

theorem absCont_self (μ : ProbState V) : AbsCont μ μ := fun _ h => h

/-- The real-valued KL sum (meaningful under `AbsCont`; junk otherwise,
guarded by `klq`). -/
noncomputable def klReal (μ ν : ProbState V) : ℝ :=
  ∑ v, (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)

open Classical in
/-- Relative entropy `D(μ ‖ ν)` on the flat carrier, total in `ℝ≥0∞`:
`⊤` off absolute continuity, the finite KL sum otherwise. -/
noncomputable def klq (μ ν : ProbState V) : ℝ≥0∞ :=
  if AbsCont μ ν then ENNReal.ofReal (klReal μ ν) else ⊤

/-- Pointwise Gibbs bound: each KL summand dominates the mass gap. -/
private theorem term_lower_bound {μ ν : ProbState V} (h : AbsCont μ ν)
    (v : V) :
    (μ : V → ℝ) v - (ν : V → ℝ) v
      ≤ (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v) := by
  rcases (μ.nonneg v).eq_or_lt with hz | hpos
  · rw [← hz, zero_mul]
    linarith [ν.nonneg v]
  · have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (h v e)
    have hν : 0 < (ν : V → ℝ) v := (ν.nonneg v).lt_of_ne (Ne.symm hν0)
    have hlog : Real.log ((ν : V → ℝ) v / (μ : V → ℝ) v)
        ≤ (ν : V → ℝ) v / (μ : V → ℝ) v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hν hpos)
    have hflip : Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)
        = -Real.log ((ν : V → ℝ) v / (μ : V → ℝ) v) := by
      rw [← Real.log_inv, inv_div]
    have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
    have hcancel : (μ : V → ℝ) v * ((ν : V → ℝ) v / (μ : V → ℝ) v - 1)
        = (ν : V → ℝ) v - (μ : V → ℝ) v := by
      field_simp
    rw [hflip]
    nlinarith [hmul, hcancel]

/-- Gibbs' inequality on the finite carrier. -/
theorem klReal_nonneg {μ ν : ProbState V} (h : AbsCont μ ν) :
    0 ≤ klReal μ ν := by
  have h1 : ∑ v, ((μ : V → ℝ) v - (ν : V → ℝ) v) ≤ klReal μ ν :=
    Finset.sum_le_sum fun v _ => term_lower_bound h v
  have h2 : ∑ v, ((μ : V → ℝ) v - (ν : V → ℝ) v) = 0 := by
    rw [Finset.sum_sub_distrib, μ.sum_eq_one, ν.sum_eq_one, sub_self]
  linarith

theorem klReal_self (μ : ProbState V) : klReal μ μ = 0 :=
  Finset.sum_eq_zero fun v _ => by
    rcases (μ.nonneg v).eq_or_lt with hz | hpos
    · rw [← hz, zero_mul]
    · rw [div_self hpos.ne', Real.log_one, mul_zero]

@[simp] theorem klq_self (μ : ProbState V) : klq μ μ = 0 := by
  rw [klq, if_pos (absCont_self μ), klReal_self, ENNReal.ofReal_zero]

/-- Strict Gibbs: relative entropy vanishes only on the diagonal. -/
theorem klq_eq_zero_iff {μ ν : ProbState V} : klq μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h0
    by_cases hac : AbsCont μ ν
    · rw [klq, if_pos hac, ENNReal.ofReal_eq_zero] at h0
      have hkl0 : klReal μ ν = 0 := le_antisymm h0 (klReal_nonneg hac)
      have hterm : ∀ v ∈ Finset.univ,
          (0:ℝ) ≤ (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)
            - ((μ : V → ℝ) v - (ν : V → ℝ) v) :=
        fun v _ => sub_nonneg.mpr (term_lower_bound hac v)
      have hsum0 : ∑ v, ((μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)
          - ((μ : V → ℝ) v - (ν : V → ℝ) v)) = 0 := by
        rw [Finset.sum_sub_distrib]
        have h2 : ∑ v, ((μ : V → ℝ) v - (ν : V → ℝ) v) = 0 := by
          rw [Finset.sum_sub_distrib, μ.sum_eq_one, ν.sum_eq_one, sub_self]
        rw [h2, sub_zero]
        exact hkl0
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum0
      apply Subtype.ext
      funext v
      have hv := hall v (Finset.mem_univ v)
      rcases (μ.nonneg v).eq_or_lt with hz | hpos
      · rw [← hz, zero_mul, zero_sub, neg_sub, sub_zero] at hv
        rw [← hz]
        exact hv.symm
      · have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (hac v e)
        have hν : 0 < (ν : V → ℝ) v := (ν.nonneg v).lt_of_ne (Ne.symm hν0)
        by_contra hne
        have hratio : (ν : V → ℝ) v / (μ : V → ℝ) v ≠ 1 := by
          intro e
          rw [div_eq_one_iff_eq hpos.ne'] at e
          exact hne e.symm
        -- strict form of `log x ≤ x - 1` away from `x = 1`
        have hlogne : Real.log ((ν : V → ℝ) v / (μ : V → ℝ) v) ≠ 0 := by
          intro e
          apply hratio
          have := Real.exp_log (div_pos hν hpos)
          rw [e, Real.exp_zero] at this
          exact this.symm
        have hstrict : Real.log ((ν : V → ℝ) v / (μ : V → ℝ) v)
            < (ν : V → ℝ) v / (μ : V → ℝ) v - 1 := by
          have h1 := Real.add_one_lt_exp hlogne
          rw [Real.exp_log (div_pos hν hpos)] at h1
          linarith
        have hflip : Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)
            = -Real.log ((ν : V → ℝ) v / (μ : V → ℝ) v) := by
          rw [← Real.log_inv, inv_div]
        have hcancel : (μ : V → ℝ) v * ((ν : V → ℝ) v / (μ : V → ℝ) v - 1)
            = (ν : V → ℝ) v - (μ : V → ℝ) v := by
          field_simp
        have hgt : (μ : V → ℝ) v - (ν : V → ℝ) v
            < (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v) := by
          rw [hflip]
          nlinarith [mul_lt_mul_of_pos_left hstrict hpos, hcancel]
        linarith [hv, hgt]
    · rw [klq, if_neg hac] at h0
      exact absurd h0 ENNReal.top_ne_zero
  · rintro rfl
    exact klq_self μ

/-- Relative entropy from a point mass reads off one coordinate:
`D(δ_v ‖ ν) = negLog (ν v)`, walls included. -/
theorem klq_dirac [DecidableEq V] (v : V) (ν : ProbState V) :
    klq (ProbState.dirac v) ν = negLog ((ν : V → ℝ) v) := by
  rcases (ν.nonneg v).eq_or_lt with hz | hpos
  · have hν0 : (ν : V → ℝ) v = 0 := hz.symm
    have hnac : ¬ AbsCont (ProbState.dirac v) ν := by
      intro hac
      have h1 := hac v hν0
      rw [ProbState.dirac_apply_same] at h1
      norm_num at h1
    rw [klq, if_neg hnac, hν0, negLog_of_nonpos (le_refl 0)]
  · have hac : AbsCont (ProbState.dirac v) ν := by
      intro w hw
      have hne : w ≠ v := fun e => by rw [e] at hw; exact hpos.ne' hw
      exact ProbState.dirac_apply_of_ne hne
    rw [klq, if_pos hac, negLog_of_pos hpos]
    congr 1
    rw [klReal,
      Finset.sum_eq_single v
        (fun w _ hw => by rw [ProbState.dirac_apply_of_ne hw, zero_mul])
        (fun h => absurd (Finset.mem_univ v) h),
      ProbState.dirac_apply_same, one_mul, one_div, Real.log_inv]

/-! ## Expected surprisal, and the update -/

/-- Expected surprisal of a likelihood under a probability state, total
in `ℝ≥0∞` (`0 · ⊤ = 0`: zero-mass outcomes cost nothing even at zero
likelihood). -/
noncomputable def surprisal (L : V → ℝ) (μ : ProbState V) : ℝ≥0∞ :=
  ∑ v, ENNReal.ofReal ((μ : V → ℝ) v) * negLog (L v)

/-- A zero-likelihood outcome carrying positive mass walls the surprisal. -/
theorem surprisal_eq_top {L : V → ℝ} {μ : ProbState V} (v : V)
    (hL : L v ≤ 0) (hμ : 0 < (μ : V → ℝ) v) : surprisal L μ = ⊤ := by
  have hterm : ENNReal.ofReal ((μ : V → ℝ) v) * negLog (L v) = ⊤ := by
    rw [negLog_of_nonpos hL, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hμ).ne']
  refine le_antisymm le_top ?_
  rw [surprisal]
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal ((μ : V → ℝ) v) * negLog (L v) := hterm.symm
  _ ≤ ∑ w, ENNReal.ofReal ((μ : V → ℝ) w) * negLog (L w) :=
      Finset.single_le_sum
        (f := fun w => ENNReal.ofReal ((μ : V → ℝ) w) * negLog (L w))
        (fun w _ => zero_le) (Finset.mem_univ v)

/-- On supports where the likelihood is positive (and at most one), the
surprisal is the real expectation of `-log L`. -/
theorem surprisal_eq_ofReal {L : V → ℝ} {μ : ProbState V}
    (hL1 : ∀ v, L v ≤ 1) (hsupp : ∀ v, 0 < (μ : V → ℝ) v → 0 < L v) :
    surprisal L μ
      = ENNReal.ofReal (∑ v, (μ : V → ℝ) v * (-Real.log (L v))) := by
  have hnn : ∀ v ∈ (Finset.univ : Finset V),
      0 ≤ (μ : V → ℝ) v * (-Real.log (L v)) := by
    intro v _
    rcases (μ.nonneg v).eq_or_lt with hz | hpos
    · rw [← hz, zero_mul]
    · exact mul_nonneg hpos.le
        (neg_nonneg.mpr (Real.log_nonpos (hsupp v hpos).le (hL1 v)))
  rw [surprisal, ENNReal.ofReal_sum_of_nonneg hnn]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases (μ.nonneg v).eq_or_lt with hz | hpos
  · rw [← hz]
    simp
  · rw [negLog_of_pos (hsupp v hpos), ← ENNReal.ofReal_mul hpos.le]

/-- Surprisal vanishes exactly when the state is supported where the
likelihood is (at least) one. -/
theorem surprisal_eq_zero_iff {L : V → ℝ} {μ : ProbState V} :
    surprisal L μ = 0 ↔ ∀ v, 0 < (μ : V → ℝ) v → 1 ≤ L v := by
  rw [surprisal, Finset.sum_eq_zero_iff]
  constructor
  · intro h v hv
    have hterm := h v (Finset.mem_univ v)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · rw [ENNReal.ofReal_eq_zero] at h0
      linarith
    · rcases le_or_gt (L v) 0 with hL | hL
      · rw [negLog_of_nonpos hL] at h0
        exact absurd h0 ENNReal.top_ne_zero
      · exact (negLog_eq_zero_iff hL).mp h0
  · intro h v _
    rcases (μ.nonneg v).eq_or_lt with hz | hpos
    · rw [← hz, ENNReal.ofReal_zero, zero_mul]
    · rw [(negLog_eq_zero_iff (by linarith [h v hpos] : (0:ℝ) < L v)).mpr (h v hpos),
        mul_zero]

/-- The multiplicative-weight update on penalty functionals: add the
expected surprisal of the observed likelihood.  (Renormalization, where
wanted, subtracts the infimum; the argmin-face theorem below is stated
normalization-free.) -/
noncomputable def mwu (L : V → ℝ) (φ : ProbPenalty V) : ProbPenalty V :=
  fun μ => φ μ + surprisal L μ

/-! ## Evidence probability and the Bayes/Pearl posterior -/

/-- The probability of the evidence (marginal likelihood) under a state. -/
def evProb (ν : ProbState V) (L : V → ℝ) : ℝ :=
  ∑ v, (ν : V → ℝ) v * L v

theorem evProb_nonneg {ν : ProbState V} {L : V → ℝ} (hL0 : ∀ v, 0 ≤ L v) :
    0 ≤ evProb ν L :=
  Finset.sum_nonneg fun v _ => mul_nonneg (ν.nonneg v) (hL0 v)

theorem evProb_le_one {ν : ProbState V} {L : V → ℝ}
    (hL1 : ∀ v, L v ≤ 1) : evProb ν L ≤ 1 := by
  calc evProb ν L ≤ ∑ v, (ν : V → ℝ) v :=
        Finset.sum_le_sum fun v _ =>
          mul_le_of_le_one_right (ν.nonneg v) (hL1 v)
  _ = 1 := ν.sum_eq_one

/-- The Bayes/Pearl posterior: multiply by the likelihood, renormalize. -/
noncomputable def bayes (ν : ProbState V) (L : V → ℝ) (hL0 : ∀ v, 0 ≤ L v)
    (hZ : 0 < evProb ν L) : ProbState V :=
  ⟨fun v => (ν : V → ℝ) v * L v / evProb ν L,
    ⟨fun v => div_nonneg (mul_nonneg (ν.nonneg v) (hL0 v)) hZ.le, by
      have hfold : (∑ v, (ν : V → ℝ) v * L v) = evProb ν L := rfl
      simp only [div_eq_mul_inv, ← Finset.sum_mul, hfold,
        mul_inv_cancel₀ hZ.ne']⟩⟩

@[simp] theorem bayes_apply {ν : ProbState V} {L : V → ℝ}
    (hL0 : ∀ v, 0 ≤ L v) (hZ : 0 < evProb ν L) (v : V) :
    ((bayes ν L hL0 hZ : ProbState V) : V → ℝ) v
      = (ν : V → ℝ) v * L v / evProb ν L := rfl

/-- Every probability state has an atom. -/
theorem exists_pos_apply (μ : ProbState V) : ∃ v, 0 < (μ : V → ℝ) v := by
  by_contra h
  push Not at h
  have hz : ∀ v, (μ : V → ℝ) v = 0 :=
    fun v => le_antisymm (h v) (μ.nonneg v)
  have := μ.sum_eq_one
  rw [Finset.sum_eq_zero fun v _ => hz v] at this
  norm_num at this

/-! ## The two credal embeddings, and the flip -/

/-- The **weighted (tilted) Hausdorff–KL embedding** of a family of
probability states: `μ ↦ ⨅ i, D(μ ‖ ν i) + t i`.  Through weights
`α = e^{-t}` this is a Halpern–Leung weighted set of probabilities;
the plain embedding `hkl` is the tilt-zero slice. -/
noncomputable def hklW {ι : Sort*} (ν : ι → ProbState V) (t : ι → ℝ≥0∞) :
    ProbPenalty V :=
  fun μ => ⨅ i, (klq μ (ν i) + t i)

/-- The (plain) Hausdorff–KL embedding of a family: `μ ↦ ⨅ i, D(μ ‖ ν i)`. -/
noncomputable def hkl {ι : Sort*} (ν : ι → ProbState V) : ProbPenalty V :=
  hklW ν fun _ => 0

/-- The Hausdorff–KL embedding of a set of probability states. -/
noncomputable def hklSet (M : Set (ProbState V)) : ProbPenalty V :=
  fun μ => ⨅ ν ∈ M, klq μ ν

/-- The reversed-direction embedding `μ ↦ ⨅ i, D(ν i ‖ μ)` — defined in
order to be adjudicated against (`mwu_hklFlip_eq_top`). -/
noncomputable def hklFlip {ι : Sort*} (ν : ι → ProbState V) :
    ProbPenalty V :=
  fun μ => ⨅ i, klq (ν i) μ

theorem hkl_apply {ι : Sort*} (ν : ι → ProbState V) (μ : ProbState V) :
    hkl ν μ = ⨅ i, klq μ (ν i) := by
  simp [hkl, hklW]

/-- Set-form and family-form embeddings agree on ranges. -/
theorem hklSet_range {ι : Sort*} (ν : ι → ProbState V) :
    hklSet (Set.range ν) = hkl ν := by
  funext μ
  rw [hklSet, iInf_range, hkl_apply]

/-- Adding a constant passes through an infimum in `ℝ≥0∞` (both sides are
`⊤` over an empty index). -/
private theorem iInf_add_const {ι : Sort*} (f : ι → ℝ≥0∞) (a : ℝ≥0∞) :
    (⨅ i, f i) + a = ⨅ i, (f i + a) := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [add_top]
  · refine le_antisymm (le_iInf fun i => add_le_add (iInf_le f i) le_rfl) ?_
    rw [← tsub_le_iff_right]
    refine le_iInf fun i => ?_
    rw [tsub_le_iff_right]
    exact iInf_le _ i

/-- The zero set of the plain embedding is exactly the (finite) family:
the graded reading remembers the set, where the wall forgets the grading.
(For the convex hull of the family the zero set is again the *hull* only
through the set-form embedding of the hull itself — the finite family
here is the generating class of credal-network practice.) -/
theorem hkl_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (ν : ι → ProbState V) (μ : ProbState V) :
    hkl ν μ = 0 ↔ ∃ i, μ = ν i := by
  rw [hkl_apply]
  constructor
  · intro h0
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ
      (fun i => klq μ (ν i)) Finset.univ_nonempty
    have hattain : (⨅ i, klq μ (ν i)) = klq μ (ν i₁) :=
      le_antisymm (iInf_le _ _)
        (le_iInf fun j => hi₁ j (Finset.mem_univ j))
    exact ⟨i₁, klq_eq_zero_iff.mp (hattain.symm.trans h0)⟩
  · rintro ⟨i, rfl⟩
    exact le_antisymm ((iInf_le _ i).trans_eq (klq_self _)) (zero_le)

/-! ## The chain-rule engine, and the fences -/

/-- **The chain-rule engine.**  For evidence of positive probability,
updating the relative-entropy penalty toward `ν` is the relative-entropy
penalty toward the Bayes posterior, tilted by the surprisal of the
marginal likelihood — total in `ℝ≥0∞`, every wall case included.  (For
hard evidence this is the chain rule of relative entropy over the
two-cell partition; the finite-value case is the Gibbs/Donsker–Varadhan
variational identity that makes the Gibbs chart Bayesian.) -/
theorem klq_add_surprisal {μ ν : ProbState V} {L : V → ℝ}
    (hL0 : ∀ v, 0 ≤ L v) (hL1 : ∀ v, L v ≤ 1) (hZ : 0 < evProb ν L) :
    klq μ ν + surprisal L μ
      = klq μ (bayes ν L hL0 hZ) + negLog (evProb ν L) := by
  by_cases hac : AbsCont μ ν
  · by_cases hsupp : ∀ v, 0 < (μ : V → ℝ) v → 0 < L v
    · -- finite case: the real identity plus `ofReal` bookkeeping
      have hacB : AbsCont μ (bayes ν L hL0 hZ) := by
        intro v hv
        rw [bayes_apply, div_eq_zero_iff] at hv
        rcases hv with hv | hv
        · rcases mul_eq_zero.mp hv with h | h
          · exact hac v h
          · by_contra hμ
            have hpos := (μ.nonneg v).lt_of_ne (Ne.symm hμ)
            exact (hsupp v hpos).ne' h
        · exact absurd hv hZ.ne'
      have hsplit : ∀ v,
          (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v
              / ((ν : V → ℝ) v * L v / evProb ν L))
            = (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v / (ν : V → ℝ) v)
              + (μ : V → ℝ) v * (-Real.log (L v))
              + (μ : V → ℝ) v * Real.log (evProb ν L) := by
        intro v
        rcases (μ.nonneg v).eq_or_lt with hz | hpos
        · rw [← hz]
          ring
        · have hLv := hsupp v hpos
          have hν0 : (ν : V → ℝ) v ≠ 0 := fun e => hpos.ne' (hac v e)
          have hνv : 0 < (ν : V → ℝ) v := (ν.nonneg v).lt_of_ne (Ne.symm hν0)
          rw [Real.log_div hpos.ne'
              (div_ne_zero (mul_ne_zero hνv.ne' hLv.ne') hZ.ne'),
            Real.log_div (mul_ne_zero hνv.ne' hLv.ne') hZ.ne',
            Real.log_mul hνv.ne' hLv.ne',
            Real.log_div hpos.ne' hνv.ne']
          ring
      have hkey : klReal μ (bayes ν L hL0 hZ)
          = klReal μ ν + (∑ v, (μ : V → ℝ) v * (-Real.log (L v)))
            + Real.log (evProb ν L) := by
        have hunfold : klReal μ (bayes ν L hL0 hZ)
            = ∑ v, (μ : V → ℝ) v * Real.log ((μ : V → ℝ) v
                / ((ν : V → ℝ) v * L v / evProb ν L)) := by
          rw [klReal]
          exact Finset.sum_congr rfl fun v _ => by rw [bayes_apply]
        rw [hunfold, Finset.sum_congr rfl fun v _ => hsplit v,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, μ.sum_eq_one, one_mul]
        rfl
      have hsurR_nonneg : 0 ≤ ∑ v, (μ : V → ℝ) v * (-Real.log (L v)) := by
        refine Finset.sum_nonneg fun v _ => ?_
        rcases (μ.nonneg v).eq_or_lt with hz | hpos
        · rw [← hz, zero_mul]
        · exact mul_nonneg hpos.le
            (neg_nonneg.mpr (Real.log_nonpos (hsupp v hpos).le (hL1 v)))
      have hZlog : (0:ℝ) ≤ -Real.log (evProb ν L) :=
        neg_nonneg.mpr (Real.log_nonpos (evProb_nonneg hL0)
          (evProb_le_one hL1))
      rw [klq, if_pos hac, klq, if_pos hacB,
        surprisal_eq_ofReal hL1 hsupp, negLog_of_pos hZ,
        ← ENNReal.ofReal_add (klReal_nonneg hac) hsurR_nonneg,
        ← ENNReal.ofReal_add (klReal_nonneg hacB) hZlog]
      congr 1
      rw [hkey]
      ring
    · -- surprisal wall: some atom of `μ` has zero likelihood
      push Not at hsupp
      obtain ⟨v, hμv, hLv⟩ := hsupp
      have hLv0 : L v = 0 := le_antisymm hLv (hL0 v)
      rw [surprisal_eq_top v hLv hμv, add_top]
      have hnB : ¬ AbsCont μ (bayes ν L hL0 hZ) := by
        intro h
        have hb : ((bayes ν L hL0 hZ : ProbState V) : V → ℝ) v = 0 := by
          rw [bayes_apply, hLv0, mul_zero, zero_div]
        exact hμv.ne' (h v hb)
      rw [klq, if_neg hnB, top_add]
  · -- `μ` escapes the prior's support
    have hex : ∃ v, (ν : V → ℝ) v = 0 ∧ (μ : V → ℝ) v ≠ 0 := by
      by_contra h
      push Not at h
      exact hac fun v hv => h v hv
    obtain ⟨v, hνv, hμv⟩ := hex
    have hnB : ¬ AbsCont μ (bayes ν L hL0 hZ) := by
      intro h
      apply hμv
      apply h v
      rw [bayes_apply, hνv, zero_mul, zero_div]
    rw [klq, if_neg hac, top_add, klq, if_neg hnB, top_add]

/-- **The vacuous-conditioning fence.**  Evidence of probability zero
collapses the updated penalty to `⊤` at every state: some atom of `μ`
must land either outside the prior's support or on zero likelihood.
(This is the boundary case the credal-updating literature fences by
hand — regular vs natural extension; here it is a theorem.) -/
theorem klq_add_surprisal_eq_top_of_evProb_eq_zero {μ ν : ProbState V}
    {L : V → ℝ} (hL0 : ∀ v, 0 ≤ L v) (hZ : evProb ν L = 0) :
    klq μ ν + surprisal L μ = ⊤ := by
  have hall : ∀ v, (ν : V → ℝ) v * L v = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (ν.nonneg v) (hL0 v))).mp hZ
    exact fun v => h v (Finset.mem_univ v)
  obtain ⟨v₀, hv₀⟩ := exists_pos_apply μ
  rcases mul_eq_zero.mp (hall v₀) with h | h
  · have hnac : ¬ AbsCont μ ν := fun hc => hv₀.ne' (hc v₀ h)
    rw [klq, if_neg hnac, top_add]
  · rw [surprisal_eq_top v₀ h.le hv₀, add_top]

/-! ## The square: updating is Halpern–Leung likelihood reweighting -/

/-- **The square, exact at the weighted level.**  The multiplicative-
weight update of a tilted Hausdorff–KL embedding is the tilted embedding
of the Bayes posteriors, with each tilt incremented by the surprisal of
its own marginal likelihood — Halpern–Leung likelihood updating of the
weighted set.  Plain credal sets (tilt zero) exit into the weighted
class after one update: the weights are forced by the update. -/
theorem mwu_hklW_eq {ι : Sort*} {ν : ι → ProbState V} {t : ι → ℝ≥0∞}
    {L : V → ℝ} (hL0 : ∀ v, 0 ≤ L v) (hL1 : ∀ v, L v ≤ 1)
    (hZ : ∀ i, 0 < evProb (ν i) L) :
    mwu L (hklW ν t)
      = hklW (fun i => bayes (ν i) L hL0 (hZ i))
          (fun i => t i + negLog (evProb (ν i) L)) := by
  funext μ
  show (⨅ i, (klq μ (ν i) + t i)) + surprisal L μ = _
  rw [iInf_add_const]
  refine iInf_congr fun i => ?_
  rw [add_right_comm, klq_add_surprisal hL0 hL1 (hZ i)]
  ring

/-- The normalization constant of the update is the Halpern–Leung weight
normalizer: `negLog` of the best (tilt-discounted) marginal likelihood. -/
theorem iInf_mwu_hklW [Nonempty V] {ι : Sort*} {ν : ι → ProbState V}
    {t : ι → ℝ≥0∞} {L : V → ℝ} (hL0 : ∀ v, 0 ≤ L v) (hL1 : ∀ v, L v ≤ 1)
    (hZ : ∀ i, 0 < evProb (ν i) L) :
    (⨅ μ, mwu L (hklW ν t) μ)
      = ⨅ i, (t i + negLog (evProb (ν i) L)) := by
  simp only [mwu_hklW_eq hL0 hL1 hZ, hklW]
  rw [iInf_comm]
  refine iInf_congr fun i => le_antisymm ?_ (le_iInf fun μ => le_add_self)
  exact (iInf_le _ (bayes (ν i) L hL0 (hZ i))).trans_eq
    (by rw [klq_self, zero_add])

/-! ## The argmin face: Gilboa–Schmeidler maximum-likelihood updating -/

/-- The **maximum-likelihood update** of a family (Gilboa–Schmeidler;
Dempster conditioning, in the belief-function case): the Bayes posteriors
of exactly the maximal-marginal-likelihood members, positive evidence
required. -/
def mluSet {ι : Sort*} (ν : ι → ProbState V) (L : V → ℝ)
    (hL0 : ∀ v, 0 ≤ L v) : Set (ProbState V) :=
  {μ | ∃ i, ∃ hi : 0 < evProb (ν i) L,
    (∀ j, evProb (ν j) L ≤ evProb (ν i) L) ∧ μ = bayes (ν i) L hL0 hi}

/-- The argmin-flipped variant (condition the *minimal*-likelihood
members) — defined only to be refuted (`Witness.mluSet_ne_mluSetMin`). -/
def mluSetMin {ι : Sort*} (ν : ι → ProbState V) (L : V → ℝ)
    (hL0 : ∀ v, 0 ≤ L v) : Set (ProbState V) :=
  {μ | ∃ i, ∃ hi : 0 < evProb (ν i) L,
    (∀ j, evProb (ν i) L ≤ evProb (ν j) L) ∧ μ = bayes (ν i) L hL0 hi}

/-- **The argmin face of the update is maximum-likelihood updating.**
For a finite family with everywhere-positive evidence, the
minimum-penalty states of the updated Hausdorff–KL embedding are exactly
the Gilboa–Schmeidler posteriors.  Equivalently (subtraction-free
reading): after renormalizing the update to infimum zero, its zero set
is the maximum-likelihood update of the credal set. -/
theorem argmin_mwu_hkl_eq_mluSet {ι : Type*} [Fintype ι] [Nonempty ι]
    {ν : ι → ProbState V} {L : V → ℝ}
    (hL0 : ∀ v, 0 ≤ L v) (hL1 : ∀ v, L v ≤ 1)
    (hZ : ∀ i, 0 < evProb (ν i) L) :
    {μ | ∀ μ', mwu L (hkl ν) μ ≤ mwu L (hkl ν) μ'} = mluSet ν L hL0 := by
  have hZ1 : ∀ i, evProb (ν i) L ≤ 1 := fun i => evProb_le_one hL1
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => evProb (ν i) L) Finset.univ_nonempty
  have hmax' : ∀ j, evProb (ν j) L ≤ evProb (ν i₀) L :=
    fun j => hmax j (Finset.mem_univ j)
  set B : ι → ProbState V := fun i => bayes (ν i) L hL0 (hZ i) with hB
  set c : ι → ℝ≥0∞ := fun i => negLog (evProb (ν i) L) with hc
  have hF : ∀ μ, mwu L (hkl ν) μ = ⨅ i, (klq μ (B i) + c i) := by
    intro μ
    rw [hkl, mwu_hklW_eq hL0 hL1 hZ]
    simp only [hklW, zero_add, hB, hc]
  have hcmin : ∀ i, c i₀ ≤ c i :=
    fun i => negLog_le_negLog (hZ i) (hmax' i)
  have hFmin : ∀ μ, (⨅ i, c i) ≤ mwu L (hkl ν) μ := by
    intro μ
    rw [hF]
    exact le_iInf fun i => le_trans (iInf_le c i) le_add_self
  have hiInfc : (⨅ i, c i) = c i₀ :=
    le_antisymm (iInf_le _ i₀) (le_iInf hcmin)
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hargmin
    have hFB : mwu L (hkl ν) (B i₀) ≤ c i₀ := by
      rw [hF]
      exact (iInf_le _ i₀).trans_eq (by rw [klq_self, zero_add])
    have hle : mwu L (hkl ν) μ ≤ c i₀ := (hargmin (B i₀)).trans hFB
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ
      (fun i => klq μ (B i) + c i) Finset.univ_nonempty
    have hattain : mwu L (hkl ν) μ = klq μ (B i₁) + c i₁ := by
      rw [hF]
      exact le_antisymm (iInf_le _ i₁)
        (le_iInf fun j => hi₁ j (Finset.mem_univ j))
    have hchain : klq μ (B i₁) + c i₁ ≤ c i₀ := hattain ▸ hle
    have hc₁top : c i₁ ≠ ⊤ := (negLog_lt_top (hZ i₁)).ne
    have hklq0 : klq μ (B i₁) = 0 := by
      have h1 : klq μ (B i₁) + c i₁ ≤ 0 + c i₁ := by
        rw [zero_add]
        exact hchain.trans (hcmin i₁)
      have h2 := (ENNReal.add_le_add_iff_right hc₁top).mp h1
      exact le_antisymm h2 (zero_le)
    have hceq : c i₁ = c i₀ :=
      le_antisymm (le_trans le_add_self hchain) (hcmin i₁)
    have hZeq : evProb (ν i₁) L = evProb (ν i₀) L :=
      negLog_inj (hZ i₁) (hZ i₀) (hZ1 i₁) (hZ1 i₀) hceq
    exact ⟨i₁, hZ i₁, fun j => (hmax' j).trans (le_of_eq hZeq.symm),
      klq_eq_zero_iff.mp hklq0⟩
  · rintro ⟨i₁, hi₁, hmax₁, rfl⟩
    intro μ'
    have hv : mwu L (hkl ν) (bayes (ν i₁) L hL0 hi₁) ≤ c i₁ := by
      rw [hF]
      exact (iInf_le _ i₁).trans_eq (by rw [hB, klq_self, zero_add])
    have hcmin₁ : ∀ j, c i₁ ≤ c j :=
      fun j => negLog_le_negLog (hZ j) (hmax₁ j)
    calc mwu L (hkl ν) (bayes (ν i₁) L hL0 hi₁) ≤ c i₁ := hv
    _ ≤ ⨅ j, c j := le_iInf hcmin₁
    _ ≤ mwu L (hkl ν) μ' := hFmin μ'

/-! ## The direction adjudication: the flip collapses -/

/-- **The reversed direction collapses at singletons.**  If the prior
has mass on zero likelihood, then for *every* state `μ` the flipped
penalty updates to `⊤`: either `μ` misses part of the prior's support
(walling `D(ν‖μ)`) or it charges a zero-likelihood outcome (walling the
surprisal).  Contrast the first-slot direction, which stays finite and
performs Bayes (`klq_add_surprisal`). -/
theorem flip_add_surprisal_eq_top {ν : ProbState V} {L : V → ℝ}
    (h : ∃ v, L v ≤ 0 ∧ 0 < (ν : V → ℝ) v) (μ : ProbState V) :
    klq ν μ + surprisal L μ = ⊤ := by
  obtain ⟨v, hLv, hνv⟩ := h
  by_cases hμv : (μ : V → ℝ) v = 0
  · have hnac : ¬ AbsCont ν μ := fun hc => hνv.ne' (hc v hμv)
    rw [klq, if_neg hnac, top_add]
  · have hpos : 0 < (μ : V → ℝ) v := (μ.nonneg v).lt_of_ne (Ne.symm hμv)
    rw [surprisal_eq_top v hLv hpos, add_top]

/-- **The reversed-direction embedding is un-updatable**: whenever every
member of the family has mass on zero likelihood (under hard evidence:
every member gives the evidence probability `< 1`), the update of the
flipped embedding is identically `⊤` — the vacuous belief state.  No
additive renormalization repairs an identically-`⊤` functional, so the
KL direction of the Hausdorff embedding is forced by updatability. -/
theorem mwu_hklFlip_eq_top {ι : Sort*} {ν : ι → ProbState V} {L : V → ℝ}
    (h : ∀ i, ∃ v, L v ≤ 0 ∧ 0 < ((ν i : ProbState V) : V → ℝ) v)
    (μ : ProbState V) :
    mwu L (hklFlip ν) μ = ⊤ := by
  show (⨅ i, klq (ν i) μ) + surprisal L μ = ⊤
  rw [iInf_add_const, iInf_eq_top]
  exact fun i => flip_add_surprisal_eq_top (h i) μ

/-! ## The wall contrast: possibilistic updating only intersects -/

/-- Updating the **wall** embedding never reweights: the updated wall is
zero exactly on members whose support carries no surprisal — for hard
evidence, `M ∩ {μ : supp μ ⊆ E}` — i.e. the possibilistic reading can
only kill states, never condition them.  This is the gap the graded
embedding closes. -/
theorem mwu_probWall_eq_zero_iff {C : Set (ProbState V)} {L : V → ℝ}
    (μ : ProbState V) :
    mwu L (probWall C) μ = 0 ↔ μ ∈ C ∧ surprisal L μ = 0 := by
  show probWall C μ + surprisal L μ = 0 ↔ _
  constructor
  · intro h
    have hw : probWall C μ = 0 :=
      le_antisymm (h ▸ le_self_add) (zero_le)
    have hs : surprisal L μ = 0 :=
      le_antisymm (h ▸ le_add_self) (zero_le)
    refine ⟨?_, hs⟩
    by_contra hC
    rw [probWall_apply_of_not_mem hC] at hw
    exact ENNReal.top_ne_zero hw
  · rintro ⟨hC, hs⟩
    rw [probWall_apply_of_mem hC, hs, add_zero]

/-! ## Witnesses: the refutation fixtures, in exact rationals

Instance I1 (two outcomes, one prior, hard evidence on one outcome):
the direction adjudication and the normalization refutation.  Instance
I2 (evidence of probability zero): the fence refutation.  Instance I3
(three outcomes, two priors): the argmax/argmin refutation and the
generalized-Bayes square failure. -/

namespace Witness

/-- Surprisal of a point mass reads off one coordinate. -/
theorem surprisal_dirac {V : Type*} [Fintype V] [DecidableEq V]
    (L : V → ℝ) (v : V) :
    surprisal L (ProbState.dirac v) = negLog (L v) := by
  rw [surprisal, Finset.sum_eq_single v]
  · rw [ProbState.dirac_apply_same, ENNReal.ofReal_one, one_mul]
  · intro w _ hw
    rw [ProbState.dirac_apply_of_ne hw, ENNReal.ofReal_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- Infima over a two-element index are binary minima. -/
theorem iInf_fin_two (f : Fin 2 → ℝ≥0∞) : (⨅ i, f i) = f 0 ⊓ f 1 := by
  refine le_antisymm (le_inf (iInf_le f 0) (iInf_le f 1)) (le_iInf fun i => ?_)
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

/-! ### Instance I1: `V = Fin 2`, `L = 1_{0}`, prior `(1/2, 1/2)` -/

/-- The I1 prior. -/
noncomputable def ν₁2 : ProbState (Fin 2) :=
  ProbState.ofPair (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)

/-- The I1 hard evidence: the first outcome. -/
def L₁2 : Fin 2 → ℝ := ![1, 0]

theorem L₁2_nonneg : ∀ v, 0 ≤ L₁2 v := by
  intro v
  fin_cases v <;> simp [L₁2]

theorem L₁2_le_one : ∀ v, L₁2 v ≤ 1 := by
  intro v
  fin_cases v <;> simp [L₁2]

theorem evProb_I1 : evProb ν₁2 L₁2 = 1/2 := by
  rw [evProb, Fin.sum_univ_two]
  norm_num [ν₁2, L₁2]

/-- **Direction adjudication, collapse half**: on I1 the flipped
embedding updates to the vacuous state at every `μ`. -/
theorem flip_collapses :
    ∀ μ, mwu L₁2 (hklFlip fun _ : Fin 1 => ν₁2) μ = ⊤ := by
  intro μ
  refine mwu_hklFlip_eq_top (fun _ => ⟨1, ?_, ?_⟩) μ
  · norm_num [L₁2]
  · norm_num [ν₁2]

/-- **Direction adjudication, properness half**: on the same instance
the first-slot embedding updates to a finite value at the posterior. -/
theorem forward_proper :
    mwu L₁2 (hkl fun _ : Fin 1 => ν₁2) (ProbState.dirac 0) ≠ ⊤ := by
  have h : mwu L₁2 (hkl fun _ : Fin 1 => ν₁2) (ProbState.dirac 0)
      = negLog (1/2) := by
    show (hkl fun _ : Fin 1 => ν₁2) (ProbState.dirac 0)
        + surprisal L₁2 (ProbState.dirac 0) = _
    rw [hkl_apply, iInf_unique, surprisal_dirac]
    have h1 : klq (ProbState.dirac 0) ν₁2 = negLog ((ν₁2 : Fin 2 → ℝ) 0) :=
      klq_dirac 0 ν₁2
    rw [h1]
    have h2 : ((ν₁2 : Fin 2 → ℝ)) 0 = 1/2 := by simp [ν₁2]
    have h3 : L₁2 0 = 1 := by simp [L₁2]
    rw [h2, h3, negLog_one, add_zero]
  rw [h]
  exact (negLog_lt_top (by norm_num)).ne

/-- **Refutation R1 (normalization is load-bearing)**: on I1 the
*un-normalized* update has empty zero set, while the maximum-likelihood
update is nonempty — dropping the renormalization breaks the argmin-face
theorem's zero-set reading. -/
theorem unnormalized_zero_set_empty :
    (∀ μ, mwu L₁2 (hkl fun _ : Fin 1 => ν₁2) μ ≠ 0)
      ∧ (mluSet (fun _ : Fin 1 => ν₁2) L₁2 L₁2_nonneg).Nonempty := by
  constructor
  · intro μ
    have hZ : 0 < evProb ν₁2 L₁2 := by rw [evProb_I1]; norm_num
    have h : mwu L₁2 (hkl fun _ : Fin 1 => ν₁2) μ
        = klq μ (bayes ν₁2 L₁2 L₁2_nonneg hZ) + negLog (evProb ν₁2 L₁2) := by
      show (hkl fun _ : Fin 1 => ν₁2) μ + surprisal L₁2 μ = _
      rw [hkl_apply, iInf_unique]
      exact klq_add_surprisal L₁2_nonneg L₁2_le_one hZ
    rw [h]
    intro h0
    have hge : negLog (evProb ν₁2 L₁2)
        ≤ klq μ (bayes ν₁2 L₁2 L₁2_nonneg hZ) + negLog (evProb ν₁2 L₁2) :=
      le_add_self
    rw [h0, le_zero_iff, evProb_I1] at hge
    have := negLog_pos (t := 1/2) (by norm_num) (by norm_num)
    rw [hge] at this
    exact lt_irrefl 0 this
  · have hZ : 0 < evProb ν₁2 L₁2 := by rw [evProb_I1]; norm_num
    exact ⟨bayes ν₁2 L₁2 L₁2_nonneg hZ, ⟨0, hZ, fun _ => le_refl _, rfl⟩⟩

/-! ### Instance I2: evidence of probability zero -/

/-- **Refutation R2 (the fence is load-bearing)**: with evidence of
probability zero the update is identically `⊤`, its argmin set is
*everything*, and the maximum-likelihood update is empty — dropping the
positive-evidence fence breaks the argmin-face theorem. -/
theorem fenceless_argmin_univ :
    (∀ μ, mwu (fun _ => 0 : Fin 2 → ℝ) (hkl fun _ : Fin 1 => ν₁2) μ = ⊤)
      ∧ {μ | ∀ μ', mwu (fun _ => 0 : Fin 2 → ℝ) (hkl fun _ : Fin 1 => ν₁2) μ
            ≤ mwu (fun _ => 0 : Fin 2 → ℝ) (hkl fun _ : Fin 1 => ν₁2) μ'}
          = Set.univ
      ∧ mluSet (fun _ : Fin 1 => ν₁2) (fun _ => 0) (fun _ => le_refl 0)
          = ∅ := by
  have hZ0 : evProb ν₁2 (fun _ => 0 : Fin 2 → ℝ) = 0 := by
    rw [evProb]
    simp
  have htop : ∀ μ, mwu (fun _ => 0 : Fin 2 → ℝ)
      (hkl fun _ : Fin 1 => ν₁2) μ = ⊤ := by
    intro μ
    show (hkl fun _ : Fin 1 => ν₁2) μ + surprisal _ μ = ⊤
    rw [hkl_apply, iInf_unique]
    exact klq_add_surprisal_eq_top_of_evProb_eq_zero (fun _ => le_refl 0) hZ0
  refine ⟨htop, ?_, ?_⟩
  · ext μ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro μ'
    rw [htop μ, htop μ']
  · ext μ
    simp only [mluSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, hi, -, -⟩
    have hi' : (0:ℝ) < evProb ν₁2 (fun _ => 0) := hi
    rw [hZ0] at hi'
    exact lt_irrefl 0 hi'

/-! ### Instance I3: `V = Fin 3`, two priors, hard evidence on `{0, 1}` -/

/-- The I3 priors: `ν a = (1/2, 1/20, 9/20)` with evidence probability
`11/20`, and `ν b = (2/5, 1/2, 1/10)` with evidence probability `9/10`. -/
noncomputable def νa : ProbState (Fin 3) :=
  ProbState.ofTriple (1/2) (1/20) (9/20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable def νb : ProbState (Fin 3) :=
  ProbState.ofTriple (2/5) (1/2) (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable def fam : Fin 2 → ProbState (Fin 3) := ![νa, νb]

/-- The I3 hard evidence: the first two outcomes (`1` on `{0, 1}`, `0`
on `{2}`, written index-arithmetically so every coordinate evaluates
definitionally). -/
def L₃ : Fin 3 → ℝ := fun v => if v.val ≤ 1 then 1 else 0

theorem L₃_nonneg : ∀ v, 0 ≤ L₃ v := by
  intro v
  simp only [L₃]
  split <;> norm_num

theorem L₃_le_one : ∀ v, L₃ v ≤ 1 := by
  intro v
  simp only [L₃]
  split <;> norm_num

theorem evProb_νa : evProb νa L₃ = 11/20 := by
  rw [evProb, Fin.sum_univ_three,
    show ((νa : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 1/2 from rfl,
    show ((νa : ProbState (Fin 3)) : Fin 3 → ℝ) 1 = 1/20 from rfl,
    show ((νa : ProbState (Fin 3)) : Fin 3 → ℝ) 2 = 9/20 from rfl,
    show L₃ 0 = 1 from rfl, show L₃ 1 = 1 from rfl,
    show L₃ 2 = 0 from rfl]
  norm_num

theorem evProb_νb : evProb νb L₃ = 9/10 := by
  rw [evProb, Fin.sum_univ_three,
    show ((νb : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 2/5 from rfl,
    show ((νb : ProbState (Fin 3)) : Fin 3 → ℝ) 1 = 1/2 from rfl,
    show ((νb : ProbState (Fin 3)) : Fin 3 → ℝ) 2 = 1/10 from rfl,
    show L₃ 0 = 1 from rfl, show L₃ 1 = 1 from rfl,
    show L₃ 2 = 0 from rfl]
  norm_num

theorem hZa : 0 < evProb νa L₃ := by rw [evProb_νa]; norm_num

theorem hZb : 0 < evProb νb L₃ := by rw [evProb_νb]; norm_num

/-- **Refutation R3 (argmax, not argmin)**: the maximum- and minimum-
likelihood updates of the I3 family are different sets — the posterior
of the maximal-likelihood prior belongs to the first and not the second. -/
theorem mluSet_ne_mluSetMin :
    mluSet fam L₃ L₃_nonneg ≠ mluSetMin fam L₃ L₃_nonneg := by
  intro h
  have hmem : bayes νb L₃ L₃_nonneg hZb ∈ mluSet fam L₃ L₃_nonneg := by
    refine ⟨1, hZb, ?_, rfl⟩
    intro j
    fin_cases j
    · show evProb νa L₃ ≤ evProb νb L₃
      rw [evProb_νa, evProb_νb]
      norm_num
    · exact le_refl _
  rw [h] at hmem
  obtain ⟨i, hi, hmin, heq⟩ := hmem
  fin_cases i
  · -- the argmin member is `ν a`; but the posteriors differ at coordinate 0
    have h0 : ((bayes νb L₃ L₃_nonneg hZb : ProbState (Fin 3)) : Fin 3 → ℝ) 0
        = ((bayes νa L₃ L₃_nonneg hZa : ProbState (Fin 3)) : Fin 3 → ℝ) 0 :=
      congrArg (fun μ : ProbState (Fin 3) => (μ : Fin 3 → ℝ) 0) heq
    rw [bayes_apply, bayes_apply, evProb_νa, evProb_νb,
      show ((νb : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 2/5 from rfl,
      show ((νa : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 1/2 from rfl,
      show L₃ 0 = 1 from rfl] at h0
    norm_num at h0
  · -- `ν b` is not likelihood-minimal: `9/10 ≤ 11/20` is false
    have hle : evProb νb L₃ ≤ evProb νa L₃ := hmin 0
    rw [evProb_νa, evProb_νb] at hle
    norm_num at hle

/-- The generalized-Bayes posterior family of I3 (element-wise
conditioning, tilts forgotten). -/
noncomputable def gbrFam : Fin 2 → ProbState (Fin 3) :=
  ![bayes νa L₃ L₃_nonneg hZa, bayes νb L₃ L₃_nonneg hZb]

/-- **The generalized-Bayes square fails** (the recipe that forgets the
tilts): on I3, the updated embedding and the plain embedding of the
element-wise-conditioned family differ by a non-constant amount — their
cross sums over the two evidence atoms disagree, in exact rationals
through `negLog`.  (If the two functionals differed by an additive
constant, the cross sums would be equal.) -/
theorem gbr_cross_sums_ne :
    mwu L₃ (hkl fam) (ProbState.dirac 0) + hkl gbrFam (ProbState.dirac 1)
      ≠ mwu L₃ (hkl fam) (ProbState.dirac 1)
          + hkl gbrFam (ProbState.dirac 0) := by
  -- coordinate values of the four penalties, all through `klq_dirac`
  have hfam0 : ∀ w : Fin 3, klq (ProbState.dirac w) (fam 0)
      = negLog ((νa : Fin 3 → ℝ) w) := fun w => klq_dirac w νa
  have hfam1 : ∀ w : Fin 3, klq (ProbState.dirac w) (fam 1)
      = negLog ((νb : Fin 3 → ℝ) w) := fun w => klq_dirac w νb
  -- F at the two atoms
  have hF : ∀ w : Fin 3, L₃ w = 1 →
      mwu L₃ (hkl fam) (ProbState.dirac w)
        = negLog ((νa : Fin 3 → ℝ) w) ⊓ negLog ((νb : Fin 3 → ℝ) w) := by
    intro w hw
    show hkl fam (ProbState.dirac w) + surprisal L₃ (ProbState.dirac w) = _
    rw [hkl_apply, surprisal_dirac, hw, negLog_one, add_zero, iInf_fin_two,
      hfam0 w, hfam1 w]
  have hG : ∀ w : Fin 3,
      hkl gbrFam (ProbState.dirac w)
        = negLog (((gbrFam 0 : ProbState (Fin 3)) : Fin 3 → ℝ) w)
            ⊓ negLog (((gbrFam 1 : ProbState (Fin 3)) : Fin 3 → ℝ) w) := by
    intro w
    rw [hkl_apply, iInf_fin_two, klq_dirac, klq_dirac]
  -- numeric coordinates
  have hνa0 : ((νa : Fin 3 → ℝ)) 0 = 1/2 := rfl
  have hνa1 : ((νa : Fin 3 → ℝ)) 1 = 1/20 := rfl
  have hνb0 : ((νb : Fin 3 → ℝ)) 0 = 2/5 := rfl
  have hνb1 : ((νb : Fin 3 → ℝ)) 1 = 1/2 := rfl
  have hB00 : ((gbrFam 0 : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 10/11 := by
    show ((νa : Fin 3 → ℝ)) 0 * L₃ 0 / evProb νa L₃ = 10/11
    rw [hνa0, show L₃ 0 = 1 from rfl, evProb_νa]
    norm_num
  have hB01 : ((gbrFam 0 : ProbState (Fin 3)) : Fin 3 → ℝ) 1 = 1/11 := by
    show ((νa : Fin 3 → ℝ)) 1 * L₃ 1 / evProb νa L₃ = 1/11
    rw [hνa1, show L₃ 1 = 1 from rfl, evProb_νa]
    norm_num
  have hB10 : ((gbrFam 1 : ProbState (Fin 3)) : Fin 3 → ℝ) 0 = 4/9 := by
    show ((νb : Fin 3 → ℝ)) 0 * L₃ 0 / evProb νb L₃ = 4/9
    rw [hνb0, show L₃ 0 = 1 from rfl, evProb_νb]
    norm_num
  have hB11 : ((gbrFam 1 : ProbState (Fin 3)) : Fin 3 → ℝ) 1 = 5/9 := by
    show ((νb : Fin 3 → ℝ)) 1 * L₃ 1 / evProb νb L₃ = 5/9
    rw [hνb1, show L₃ 1 = 1 from rfl, evProb_νb]
    norm_num
  -- assemble the four values
  have hF0 : mwu L₃ (hkl fam) (ProbState.dirac 0) = negLog (1/2) := by
    rw [hF 0 rfl, hνa0, hνb0]
    exact inf_eq_left.mpr (negLog_le_negLog (by norm_num) (by norm_num))
  have hF1 : mwu L₃ (hkl fam) (ProbState.dirac 1) = negLog (1/2) := by
    rw [hF 1 rfl, hνa1, hνb1]
    exact inf_eq_right.mpr (negLog_le_negLog (by norm_num) (by norm_num))
  have hG0 : hkl gbrFam (ProbState.dirac 0) = negLog (10/11) := by
    rw [hG 0, hB00, hB10]
    exact inf_eq_left.mpr (negLog_le_negLog (by norm_num) (by norm_num))
  have hG1 : hkl gbrFam (ProbState.dirac 1) = negLog (5/9) := by
    rw [hG 1, hB01, hB11]
    exact inf_eq_right.mpr (negLog_le_negLog (by norm_num) (by norm_num))
  rw [hF0, hF1, hG0, hG1,
    negLog_add_negLog (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    negLog_add_negLog (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  intro h
  have := negLog_inj (s := 1/2 * (5/9)) (t := 1/2 * (10/11))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  norm_num at this

/-- **The positive instance of the argmin-face theorem**: on I3 the
argmin set of the update is exactly the singleton posterior of the
maximal-likelihood prior `ν b`. -/
theorem argmin_I3 :
    {μ | ∀ μ', mwu L₃ (hkl fam) μ ≤ mwu L₃ (hkl fam) μ'}
      = mluSet fam L₃ L₃_nonneg := by
  refine argmin_mwu_hkl_eq_mluSet L₃_nonneg L₃_le_one ?_
  intro i
  fin_cases i
  · exact hZa
  · exact hZb

end Witness

end HausdorffKL

end SuFunctor.Universe
