import SuFunctor.Adequacy.DtmcAbsorb

/-! # The alive-mass tail of a regional transfer contraction

The consumption face of the contraction strengthening of the
generator-form seam, for queries about the mass still on a region:
from a transfer contraction that holds ON a region whose complement is
closed (no re-entry), and a certificate component with a unit floor on
the region, the bare mass remaining on the region decays geometrically
— `massOn M t A ≤ cᵗ · ⟨m₀|_A, V⟩`.  This is the stored-row form of a
tail bound on a hitting/stabilization time: with `A` the not-yet-done
region, the left side at horizon `t` *is* the probability the time
exceeds `t`.

Everything here is an instance of the landed transfer-contraction
induction (`massAt_expect_le_of_contraction`) at the region-supported
observable; the two hypotheses this face adds — the unit floor and the
closed complement — are each witnessed load-bearing by a kernel-checked
countermodel below (the mutant loci travel with the module as standing
regression teeth).

* `massAt_expect_on_le_of_regionContraction` — regional decay: the
  region-supported expectation under a regional contraction with a
  closed complement.
* `dtmcAliveTail_of_regionContraction` — the alive-mass tail: the unit
  floor converts the decayed expectation into a bound on bare region
  mass.
* `aliveTail_needs_floor`, `aliveTail_needs_no_reentry` — refutations
  of the hypothesis-dropped statements at concrete chains.
-/

namespace SuFunctor
namespace Adequacy

open Finset

variable {S : Type} [Fintype S]

section AliveTail

variable [DecidableEq S]

/-- The certificate component supported on a region: `V` on `A`, zero
off it.  Passing to this observable is what reduces every regional
statement to the global contraction induction. -/
def regionObservable (A : Finset S) (V : S → ℚ) : S → ℚ :=
  fun x => if x ∈ A then V x else 0

/-- Expectation against the region-supported observable is the
region-restricted expectation. -/
theorem sum_mul_regionObservable (w : S → ℚ) (A : Finset S) (V : S → ℚ) :
    (∑ x, w x * regionObservable A V x) = ∑ x ∈ A, w x * V x := by
  simp only [regionObservable, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Regional decay**: a transfer contraction on `A` whose complement
is closed (no stored row re-enters `A`) decays the region-supported
expectation geometrically.  No sign condition on `V` — matching the
landed global form. -/
theorem massAt_expect_on_le_of_regionContraction (M : FinDTMC S)
    (A : Finset S) (V : S → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (hclosed : ∀ x ∉ A, ∀ y ∈ A, M.step x y = 0)
    (hcontr : ∀ x ∈ A, (∑ y ∈ A, M.step x y * V y) ≤ c * V x) (t : ℕ) :
    (∑ x ∈ A, massAt M t x * V x) ≤ c ^ t * ∑ x ∈ A, M.init x * V x := by
  have hsplit : ∀ x, (∑ y, M.step x y * regionObservable A V y) =
      ∑ y ∈ A, M.step x y * V y := by
    intro x
    simp only [regionObservable, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hobs : ∀ x, (∑ y, M.step x y * regionObservable A V y) ≤
      c * regionObservable A V x := by
    intro x
    rw [hsplit x]
    by_cases hx : x ∈ A
    · simpa [regionObservable, hx] using hcontr x hx
    · have hz : (∑ y ∈ A, M.step x y * V y) = 0 :=
        Finset.sum_eq_zero fun y hy => by rw [hclosed x hx y hy, zero_mul]
      simp [regionObservable, hx, hz]
  have h := massAt_expect_le_of_contraction M (regionObservable A V) hc hobs t
  simp only [massAt_zero] at h
  calc (∑ x ∈ A, massAt M t x * V x)
      = ∑ x, massAt M t x * regionObservable A V x :=
        (sum_mul_regionObservable (massAt M t) A V).symm
    _ ≤ c ^ t * ∑ x, M.init x * regionObservable A V x := h
    _ = c ^ t * ∑ x ∈ A, M.init x * V x := by
        rw [sum_mul_regionObservable]

/-- **The alive-mass tail**: with a unit floor on the region, the bare
mass remaining on `A` at horizon `t` is bounded by the decayed initial
expectation — `Pr[still on A at t] ≤ cᵗ · ⟨m₀|_A, V⟩`.  With `A` the
not-yet-absorbed (not-yet-stabilized) region and `c < 1`, this is the
geometric tail bound on the hitting time, in stored-row form. -/
theorem dtmcAliveTail_of_regionContraction (M : FinDTMC S)
    (A : Finset S) (V : S → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (hfloor : ∀ x ∈ A, 1 ≤ V x)
    (hclosed : ∀ x ∉ A, ∀ y ∈ A, M.step x y = 0)
    (hcontr : ∀ x ∈ A, (∑ y ∈ A, M.step x y * V y) ≤ c * V x) (t : ℕ) :
    massOn M t A ≤ c ^ t * ∑ x ∈ A, M.init x * V x := by
  have hfl : massOn M t A ≤ ∑ x ∈ A, massAt M t x * V x :=
    Finset.sum_le_sum fun x hx =>
      le_mul_of_one_le_right (massAt_nonneg M t x) (hfloor x hx)
  exact hfl.trans
    (massAt_expect_on_le_of_regionContraction M A V hc hclosed hcontr t)

end AliveTail

/-! ## Mutant loci as kernel-checked countermodels

The two hypotheses the alive-mass face adds to the landed induction are
each refuted when dropped — at concrete chains, checked by kernel
evaluation, so the loci are standing regression teeth rather than
one-shot throwaway edits.  (The remaining hypotheses' loci belong to
the landed global lemma and are recorded with its receipts.) -/

/-- One state, unit self-loop. -/
def unitChain : FinDTMC Unit where
  step _ _ := 1
  init _ := 1
  step_nonneg _ _ := zero_le_one
  step_row_sum _ := by simp
  init_nonneg _ := zero_le_one
  init_sum := by simp

/-- **Floor locus (IJ-m1)**: with `V = 1/2` (floor dropped) the
alive-mass conclusion is false at the unit chain — the regional
contraction holds at `c = 1`, no re-entry is vacuous, and the mutated
bound would read `1 ≤ 1/2`. -/
theorem aliveTail_needs_floor :
    ¬ (massOn unitChain 1 Finset.univ ≤
        (1 : ℚ) ^ 1 * ∑ x ∈ Finset.univ, unitChain.init x * ((1 : ℚ) / 2)) := by
  intro h
  have h1 : ∀ x, massAt unitChain 1 x = 1 := by
    intro x
    have hs := massAt_succ unitChain 0 x
    simpa [unitChain] using hs
  have h2 : massOn unitChain 1 Finset.univ = 1 := by
    simp [massOn, h1]
  have h3 : ((1 : ℚ) ^ 1 * ∑ x ∈ Finset.univ,
      unitChain.init x * ((1 : ℚ) / 2)) = 1 / 2 := by
    simp [unitChain]
  rw [h2, h3] at h
  norm_num at h

/-- Two states; the region is `{true}`, and `false` feeds it with
probability one — the closed-complement hypothesis fails. -/
def reentryChain : FinDTMC Bool where
  step _ y := if y then 1 else 0
  init x := if x then 0 else 1
  step_nonneg := by decide
  step_row_sum _ := by rw [Fintype.sum_bool]; norm_num
  init_nonneg := by decide
  init_sum := by rw [Fintype.sum_bool]; norm_num

/-- **No-re-entry locus (IJ-m2)**: dropping the closed-complement
hypothesis admits mass flowing INTO the region — at `δ_false` start,
`V ≡ 1`, `c = 1`, the mutated bound would read `1 ≤ 0` at `t = 1`
(the region-restricted initial expectation is zero while the whole
mass arrives on the region in one step). -/
theorem aliveTail_needs_no_reentry :
    ¬ (massOn reentryChain 1 {true} ≤
        (1 : ℚ) ^ 1 * ∑ x ∈ ({true} : Finset Bool),
          reentryChain.init x * (1 : ℚ)) := by
  intro h
  have h1 : massAt reentryChain 1 true = 1 := by
    have hs := massAt_succ reentryChain 0 true
    rw [Fintype.sum_bool] at hs
    simpa [reentryChain] using hs
  have h2 : massOn reentryChain 1 {true} = 1 := by
    simp [massOn, h1]
  have h3 : ((1 : ℚ) ^ 1 * ∑ x ∈ ({true} : Finset Bool),
      reentryChain.init x * (1 : ℚ)) = 0 := by
    simp [reentryChain]
  rw [h2, h3] at h
  norm_num at h

end Adequacy
end SuFunctor
