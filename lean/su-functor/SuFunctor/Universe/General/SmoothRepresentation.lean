import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Sigma-smooth functionals on metric carriers are Borel-representable

A positive, normalized, sigma-smooth linear functional on the bounded
continuous real gambles over a metric Borel carrier is integration
against a countably additive Borel probability measure.  No
separability, completeness, or local compactness is assumed of the
carrier: sigma-smoothness (continuity along pointwise-decreasing
sequences vanishing in the limit) is exactly the price of countable
additivity, and the metric structure supplies both the subordinate bump
functions and the Caratheodory measurability of Borel sets.

The construction is classical:

* every open set `U` receives a *content* — the supremum of the
  functional over gambles taking values in `[0, 1]` and vanishing off
  `U`;
* sigma-smoothness upgrades finite subadditivity of the content to
  countable subadditivity, via distance bumps
  `x ↦ min 1 ((m+1) · dist x Uᶜ)` increasing to the indicator of `U`;
* the infimum of the content over open supersets is a *metric* outer
  measure (metric-separated sets split additively, since disjoint open
  neighborhoods admit summed gambles), so Caratheodory's criterion
  measures every Borel set;
* a two-sided staircase comparison against the open superlevel sets
  `{x | k/N < g x}` identifies the functional with integration.

The empty carrier never needs a case split: normalization is
contradictory there, and no step below requires nonemptiness.
-/

namespace SuFunctor.Universe.General

open MeasureTheory Filter Set BoundedContinuousFunction

open scoped ENNReal NNReal

namespace SigmaSmoothRep

variable {X : Type*} [MetricSpace X]

/-! ## Positivity, normalization, sigma-smoothness -/

/-- Positivity of a linear functional on gambles. -/
private abbrev Pos (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ g : X →ᵇ ℝ, (∀ x, 0 ≤ g x) → 0 ≤ L g

/-- Sigma-smoothness: the functional vanishes along pointwise-decreasing
sequences tending pointwise to zero. -/
private abbrev Smooth (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ h : ℕ → (X →ᵇ ℝ), (∀ n x, h (n + 1) x ≤ h n x) →
    (∀ x, Tendsto (fun n => h n x) atTop (nhds 0)) →
    Tendsto (fun n => L (h n)) atTop (nhds 0)

section Functional

variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

private lemma L_mono (hpos : Pos L) {g g' : X →ᵇ ℝ} (h : ∀ x, g x ≤ g' x) :
    L g ≤ L g' := by
  have h0 : 0 ≤ L (g' - g) := hpos _ fun x => by
    rw [BoundedContinuousFunction.sub_apply]; linarith [h x]
  have h1 : L (g' - g) = L g' - L g := map_sub L g' g
  linarith

private lemma L_const (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (c : ℝ) :
    L (BoundedContinuousFunction.const X c) = c := by
  have h : BoundedContinuousFunction.const X c
      = c • BoundedContinuousFunction.const X (1 : ℝ) := by
    ext x
    simp [BoundedContinuousFunction.const_apply', BoundedContinuousFunction.smul_apply,
      smul_eq_mul]
  rw [h, map_smul, hone, smul_eq_mul, mul_one]

private lemma L_le_one (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1)
    {g : X →ᵇ ℝ} (hg1 : ∀ x, g x ≤ 1) : L g ≤ 1 := by
  have h := L_mono hpos (g := g) (g' := BoundedContinuousFunction.const X (1 : ℝ))
    fun x => by simpa [BoundedContinuousFunction.const_apply'] using hg1 x
  rwa [hone] at h

end Functional

/-! ## Admissible gambles and the content of a set -/

/-- A gamble is *admissible* for `U` when it takes values in `[0, 1]` and
vanishes off `U`. -/
private structure IsAdm (U : Set X) (g : X →ᵇ ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ g x
  le_one : ∀ x, g x ≤ 1
  eq_zero : ∀ x, x ∉ U → g x = 0

private lemma isAdm_zero (U : Set X) : IsAdm U (0 : X →ᵇ ℝ) :=
  ⟨fun x => by simp, fun x => by simp, fun x _ => by simp⟩

private lemma IsAdm.mono {U V : Set X} (hUV : U ⊆ V) {g : X →ᵇ ℝ} (h : IsAdm U g) :
    IsAdm V g :=
  ⟨h.nonneg, h.le_one, fun x hx => h.eq_zero x fun hxU => hx (hUV hxU)⟩

/-- The type of admissible gambles for `U`. -/
private abbrev Adm (U : Set X) : Type _ := {g : X →ᵇ ℝ // IsAdm U g}

private instance admNonempty (U : Set X) : Nonempty (Adm U) := ⟨⟨0, isAdm_zero U⟩⟩

/-- The content of a set: the supremum of the functional over admissible
gambles.  Only its restriction to open sets carries the load below. -/
private noncomputable def content (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (U : Set X) : ℝ≥0∞ :=
  ⨆ q : Adm U, ENNReal.ofReal (L q.1)

private lemma content_def (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (U : Set X) :
    content L U = ⨆ q : Adm U, ENNReal.ofReal (L q.1) := rfl

section Content

variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

private lemma le_content {U : Set X} {g : X →ᵇ ℝ} (h : IsAdm U g) :
    ENNReal.ofReal (L g) ≤ content L U := by
  rw [content_def]
  exact le_iSup (fun q : Adm U => ENNReal.ofReal (L q.1)) ⟨g, h⟩

private lemma content_mono (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) {U V : Set X} (hUV : U ⊆ V) :
    content L U ≤ content L V := by
  rw [content_def]
  exact iSup_le fun q => le_content (q.2.mono hUV)

private lemma content_le_one (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (U : Set X) :
    content L U ≤ 1 := by
  rw [content_def]
  refine iSup_le fun q => ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (L_le_one hpos hone q.2.le_one)

private lemma content_ne_top (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (U : Set X) :
    content L U ≠ ⊤ :=
  ((content_le_one hpos hone U).trans_lt ENNReal.one_lt_top).ne

private lemma content_univ (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) :
    content L (univ : Set X) = 1 := by
  refine le_antisymm (content_le_one hpos hone _) ?_
  have hadm : IsAdm (univ : Set X) (BoundedContinuousFunction.const X (1 : ℝ)) :=
    ⟨fun x => by simp [BoundedContinuousFunction.const_apply'],
     fun x => by simp [BoundedContinuousFunction.const_apply'],
     fun x hx => absurd (mem_univ x) hx⟩
  have h := le_content (L := L) hadm
  rwa [hone, ENNReal.ofReal_one] at h

private lemma content_empty (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : content L (∅ : Set X) = 0 := by
  refine le_antisymm ?_ zero_le
  rw [content_def]
  refine iSup_le fun q => ?_
  have hq : q.1 = 0 := by
    ext x
    simpa using q.2.eq_zero x (notMem_empty x)
  simp [hq]

private lemma L_le_toReal_content (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1)
    {U : Set X} {g : X →ᵇ ℝ} (h : IsAdm U g) :
    L g ≤ (content L U).toReal := by
  rcases le_total (L g) 0 with h0 | h0
  · exact h0.trans ENNReal.toReal_nonneg
  · have h1 := ENNReal.toReal_mono (content_ne_top hpos hone U) (le_content h)
    rwa [ENNReal.toReal_ofReal h0] at h1

/-- Near-optimal admissible gambles exist below the content. -/
private lemma exists_adm_near (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1)
    (U : Set X) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : X →ᵇ ℝ, IsAdm U q ∧ (content L U).toReal ≤ L q + ε := by
  by_cases h0 : content L U = 0
  · refine ⟨0, isAdm_zero U, ?_⟩
    rw [h0, map_zero]
    simpa using hε.le
  · have hne : content L U ≠ ⊤ := content_ne_top hpos hone U
    have hεne : ENNReal.ofReal ε ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hε
    have hlt : content L U - ENNReal.ofReal ε < content L U :=
      ENNReal.sub_lt_self hne h0 hεne
    rw [content_def, lt_iSup_iff] at hlt
    obtain ⟨q, hq⟩ := hlt
    refine ⟨q.1, q.2, ?_⟩
    have h2 : content L U ≤ ENNReal.ofReal (L q.1) + ENNReal.ofReal ε :=
      tsub_le_iff_right.mp hq.le
    have hadd : ENNReal.ofReal (L q.1) + ENNReal.ofReal ε ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    have h3 := ENNReal.toReal_mono hadd h2
    rwa [← ENNReal.ofReal_add (hpos q.1 q.2.nonneg) hε.le,
      ENNReal.toReal_ofReal (add_nonneg (hpos q.1 q.2.nonneg) hε.le)] at h3

/-- Contents of disjoint subsets sum below the content of a common
superset: admissible gambles with disjoint supports add. -/
private lemma content_add_content_le (hpos : Pos L) {A B U : Set X}
    (hAB : Disjoint A B) (hAU : A ⊆ U) (hBU : B ⊆ U) :
    content L A + content L B ≤ content L U := by
  rw [content_def L A, content_def L B]
  refine ENNReal.iSup_add_iSup_le fun qa qb => ?_
  rw [← ENNReal.ofReal_add (hpos qa.1 qa.2.nonneg) (hpos qb.1 qb.2.nonneg), ← map_add]
  refine le_content ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [BoundedContinuousFunction.add_apply]
    exact add_nonneg (qa.2.nonneg x) (qb.2.nonneg x)
  · rw [BoundedContinuousFunction.add_apply]
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := disjoint_left.mp hAB hxA
      have := qb.2.eq_zero x hxB
      linarith [qa.2.le_one x]
    · have := qa.2.eq_zero x hxA
      linarith [qb.2.le_one x]
  · rw [BoundedContinuousFunction.add_apply,
      qa.2.eq_zero x fun hxA => hx (hAU hxA), qb.2.eq_zero x fun hxB => hx (hBU hxB),
      add_zero]

end Content

/-! ## Distance bumps

`bump U m` is `x ↦ min 1 ((m+1) · dist x Uᶜ)`, patched to the constant
one gamble when `Uᶜ` is empty (the distance to an empty set is zero by
convention, which would break the increase to the indicator).  For `U`
open the bumps increase pointwise to the indicator of `U`. -/

open scoped Classical in
private noncomputable def bump (U : Set X) (m : ℕ) : X →ᵇ ℝ :=
  if Uᶜ.Nonempty then
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => min 1 (((m : ℝ) + 1) * Metric.infDist x Uᶜ))
      (continuous_const.min
        (continuous_const.mul (Metric.continuous_infDist_pt Uᶜ)))
      1
      (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have h1 : (0 : ℝ) ≤ min 1 (((m : ℝ) + 1) * Metric.infDist x Uᶜ) :=
            le_min zero_le_one
              (mul_nonneg (by positivity) Metric.infDist_nonneg)
          linarith
        · exact min_le_left _ _)
  else BoundedContinuousFunction.const X 1

private lemma bump_apply_of_nonempty {U : Set X} (h : Uᶜ.Nonempty) (m : ℕ) (x : X) :
    bump U m x = min 1 (((m : ℝ) + 1) * Metric.infDist x Uᶜ) := by
  classical
  simp only [bump, if_pos h]
  rfl

private lemma bump_apply_of_empty {U : Set X} (h : ¬ Uᶜ.Nonempty) (m : ℕ) (x : X) :
    bump U m x = 1 := by
  classical
  simp only [bump, if_neg h]
  rfl

private lemma bump_nonneg (U : Set X) (m : ℕ) (x : X) : 0 ≤ bump U m x := by
  by_cases h : Uᶜ.Nonempty
  · rw [bump_apply_of_nonempty h]
    exact le_min zero_le_one (mul_nonneg (by positivity) Metric.infDist_nonneg)
  · rw [bump_apply_of_empty h]
    exact zero_le_one

private lemma bump_le_one (U : Set X) (m : ℕ) (x : X) : bump U m x ≤ 1 := by
  by_cases h : Uᶜ.Nonempty
  · rw [bump_apply_of_nonempty h]
    exact min_le_left _ _
  · rw [bump_apply_of_empty h]

private lemma bump_eq_zero {U : Set X} (m : ℕ) {x : X} (hx : x ∉ U) :
    bump U m x = 0 := by
  have h : Uᶜ.Nonempty := ⟨x, hx⟩
  rw [bump_apply_of_nonempty h, Metric.infDist_zero_of_mem hx, mul_zero]
  exact min_eq_right zero_le_one

private lemma isAdm_bump (U : Set X) (m : ℕ) : IsAdm U (bump U m) :=
  ⟨bump_nonneg U m, bump_le_one U m, fun _ hx => bump_eq_zero m hx⟩

/-- Diagonal monotonicity: bumps increase along growing sets and levels. -/
private lemma bump_le_bump {U V : Set X} (hUV : U ⊆ V) {m n : ℕ} (hmn : m ≤ n) (x : X) :
    bump U m x ≤ bump V n x := by
  by_cases hV : Vᶜ.Nonempty
  · have hU : Uᶜ.Nonempty := hV.mono (compl_subset_compl.mpr hUV)
    rw [bump_apply_of_nonempty hU, bump_apply_of_nonempty hV]
    refine min_le_min le_rfl ?_
    refine mul_le_mul ?_ ?_ Metric.infDist_nonneg (by positivity)
    · have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith
    · exact Metric.infDist_le_infDist_of_subset (compl_subset_compl.mpr hUV) hV
  · rw [bump_apply_of_empty hV]
    exact bump_le_one U m x

private lemma bump_eventually_one {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∀ᶠ m : ℕ in atTop, bump U m x = 1 := by
  by_cases h : Uᶜ.Nonempty
  · have hxc : x ∉ Uᶜ := by simpa using hx
    have hd : 0 < Metric.infDist x Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos h).mp hxc
    obtain ⟨M, hM⟩ := exists_nat_ge (1 / Metric.infDist x Uᶜ)
    have h1 : (1 : ℝ) ≤ (M : ℝ) * Metric.infDist x Uᶜ := by
      rw [div_le_iff₀ hd] at hM
      exact hM
    filter_upwards [eventually_ge_atTop M] with m hm
    rw [bump_apply_of_nonempty h]
    refine min_eq_left ?_
    have h2 : (M : ℝ) ≤ (m : ℝ) + 1 := by
      have : (M : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
      linarith
    calc (1 : ℝ) ≤ (M : ℝ) * Metric.infDist x Uᶜ := h1
      _ ≤ ((m : ℝ) + 1) * Metric.infDist x Uᶜ :=
          mul_le_mul_of_nonneg_right h2 Metric.infDist_nonneg
  · filter_upwards with m
    exact bump_apply_of_empty h m x

/-! ## The sigma-smooth residual limit

The workhorse: if `b n` increases pointwise to one wherever `g` is
positive, sigma-smoothness pushes `L (g * b n)` up to `L g`. -/

section Residual

variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

private lemma tendsto_L_mul (hsm : Smooth L) (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x)
    (b : ℕ → X →ᵇ ℝ)
    (hbmono : ∀ n x, b n x ≤ b (n + 1) x)
    (hbev : ∀ x, 0 < g x → ∀ᶠ n in atTop, b n x = 1) :
    Tendsto (fun n => L (g * b n)) atTop (nhds (L g)) := by
  have happly : ∀ n x, (g - g * b n) x = g x - g x * b n x := by
    intro n x
    rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply]
  have hanti : ∀ n x, (g - g * b (n + 1)) x ≤ (g - g * b n) x := by
    intro n x
    rw [happly, happly]
    have h1 : g x * b n x ≤ g x * b (n + 1) x :=
      mul_le_mul_of_nonneg_left (hbmono n x) (hg0 x)
    linarith
  have hlim : ∀ x, Tendsto (fun n => (g - g * b n) x) atTop (nhds 0) := by
    intro x
    rcases eq_or_lt_of_le (hg0 x) with h0 | h0
    · have hz : ∀ n, (g - g * b n) x = 0 := fun n => by
        rw [happly, ← h0, zero_mul, sub_zero]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      rw [hz n]
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hbev x h0] with n hb
      rw [happly, hb, mul_one, sub_self]
  have hL := hsm (fun n => g - g * b n) hanti hlim
  have hsub : Tendsto (fun n => L g - L (g - g * b n)) atTop (nhds (L g - 0)) :=
    tendsto_const_nhds.sub hL
  rw [sub_zero] at hsub
  refine hsub.congr fun n => ?_
  rw [map_sub]
  ring

end Residual

/-! ## Subadditivity of the content on open sets -/

section Subadd

variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

/-- Finite subadditivity on opens.  The multiplicative blend
`u + w - u·w = 1 - (1-u)(1-w)` of the two bump families replaces the
lattice supremum, and sigma-smoothness recovers all of `L g` in the
limit. -/
private lemma content_union_le (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    {U W : Set X} (hU : IsOpen U) (hW : IsOpen W) :
    content L (U ∪ W) ≤ content L U + content L W := by
  rw [content_def L (U ∪ W)]
  refine iSup_le fun q => ?_
  obtain ⟨g, hg⟩ := q
  -- the blended bump family
  have hblend_mono : ∀ n x,
      (bump U n + bump W n - bump U n * bump W n) x
        ≤ (bump U (n + 1) + bump W (n + 1) - bump U (n + 1) * bump W (n + 1)) x := by
    intro n x
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.mul_apply]
    have h1 := bump_nonneg U n x
    have h2 := bump_nonneg W n x
    have h3 := bump_le_one U (n + 1) x
    have h4 := bump_le_one W (n + 1) x
    have h5 : bump U n x ≤ bump U (n + 1) x := bump_le_bump (Subset.refl U) (Nat.le_succ n) x
    have h6 : bump W n x ≤ bump W (n + 1) x := bump_le_bump (Subset.refl W) (Nat.le_succ n) x
    nlinarith [mul_le_mul (sub_le_sub_left h5 1) (sub_le_sub_left h6 1)
      (sub_nonneg.mpr h4) (sub_nonneg.mpr (h5.trans h3))]
  have hblend_ev : ∀ x, 0 < g x →
      ∀ᶠ n in atTop, (bump U n + bump W n - bump U n * bump W n) x = 1 := by
    intro x hgx
    have hxUW : x ∈ U ∪ W := by
      by_contra hxn
      have := hg.eq_zero x hxn
      linarith
    have key : ∀ n, bump U n x = 1 ∨ bump W n x = 1 →
        (bump U n + bump W n - bump U n * bump W n) x = 1 := by
      intro n hn
      rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.mul_apply]
      rcases hn with h | h <;> rw [h] <;> ring
    rcases hxUW with hxU | hxW
    · filter_upwards [bump_eventually_one hU hxU] with n hn
      exact key n (Or.inl hn)
    · filter_upwards [bump_eventually_one hW hxW] with n hn
      exact key n (Or.inr hn)
  have htend := tendsto_L_mul hsm g hg.nonneg
    (fun n => bump U n + bump W n - bump U n * bump W n)
    hblend_mono hblend_ev
  -- each blended term is bounded by the sum of the two contents
  have hbound : ∀ n, L (g * (bump U n + bump W n - bump U n * bump W n))
      ≤ (content L U).toReal + (content L W).toReal := by
    intro n
    have hexp : g * (bump U n + bump W n - bump U n * bump W n)
        = g * bump U n + g * bump W n - g * (bump U n * bump W n) := by
      rw [mul_sub, mul_add]
    have hUadm : IsAdm U (g * bump U n) := by
      refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_nonneg (hg.nonneg x) (bump_nonneg U n x)
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_le_one₀ (hg.le_one x) (bump_nonneg U n x) (bump_le_one U n x)
      · rw [BoundedContinuousFunction.mul_apply, bump_eq_zero n hx, mul_zero]
    have hWadm : IsAdm W (g * bump W n) := by
      refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_nonneg (hg.nonneg x) (bump_nonneg W n x)
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_le_one₀ (hg.le_one x) (bump_nonneg W n x) (bump_le_one W n x)
      · rw [BoundedContinuousFunction.mul_apply, bump_eq_zero n hx, mul_zero]
    have hprod : 0 ≤ L (g * (bump U n * bump W n)) := by
      refine hpos _ fun x => ?_
      rw [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.mul_apply]
      exact mul_nonneg (hg.nonneg x)
        (mul_nonneg (bump_nonneg U n x) (bump_nonneg W n x))
    have h1 : L (g * bump U n) ≤ (content L U).toReal :=
      L_le_toReal_content hpos hone hUadm
    have h2 : L (g * bump W n) ≤ (content L W).toReal :=
      L_le_toReal_content hpos hone hWadm
    calc L (g * (bump U n + bump W n - bump U n * bump W n))
        = L (g * bump U n) + L (g * bump W n) - L (g * (bump U n * bump W n)) := by
          rw [hexp, map_sub, map_add]
      _ ≤ (content L U).toReal + (content L W).toReal := by linarith
  have hle : L g ≤ (content L U).toReal + (content L W).toReal :=
    le_of_tendsto htend (Eventually.of_forall hbound)
  calc ENNReal.ofReal (L g)
      ≤ ENNReal.ofReal ((content L U).toReal + (content L W).toReal) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (content L U).toReal + ENNReal.ofReal (content L W).toReal :=
        ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = content L U + content L W := by
        rw [ENNReal.ofReal_toReal (content_ne_top hpos hone U),
          ENNReal.ofReal_toReal (content_ne_top hpos hone W)]

/-- Countable subadditivity on opens, via increasing finite unions and
the diagonal bump family. -/
private lemma content_iUnion_le (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    {U : ℕ → Set X} (hU : ∀ i, IsOpen (U i)) :
    content L (⋃ i, U i) ≤ ∑' i, content L (U i) := by
  by_cases hT : ∑' i, content L (U i) = ⊤
  · exact hT ▸ le_top
  rw [content_def L (⋃ i, U i)]
  refine iSup_le fun q => ?_
  obtain ⟨g, hg⟩ := q
  have hAopen : ∀ n, IsOpen (Set.accumulate U n) := fun n => by
    rw [Set.accumulate_def]
    exact isOpen_biUnion fun i _ => hU i
  -- finite subadditivity along the accumulation
  have hAsum : ∀ n, content L (Set.accumulate U n) ≤ ∑' i, content L (U i) := by
    intro n
    have hfin : content L (Set.accumulate U n)
        ≤ ∑ i ∈ Finset.range (n + 1), content L (U i) := by
      induction n with
      | zero =>
          rw [Set.accumulate_zero_nat, Finset.sum_range_succ, Finset.sum_range_zero,
            zero_add]
      | succ n ih =>
          rw [Set.accumulate_succ, Finset.sum_range_succ]
          exact (content_union_le hpos hone hsm (hAopen n) (hU (n + 1))).trans
            (add_le_add ih le_rfl)
    exact hfin.trans (ENNReal.sum_le_tsum _)
  -- the diagonal bump family along the accumulation
  have htend := tendsto_L_mul hsm g hg.nonneg
    (fun n => bump (Set.accumulate U n) n)
    (fun n x => bump_le_bump (Set.monotone_accumulate (Nat.le_succ n)) (Nat.le_succ n) x)
    (fun x hgx => by
      have hxU : x ∈ ⋃ i, U i := by
        by_contra hxn
        have := hg.eq_zero x hxn
        linarith
      rw [← Set.iUnion_accumulate] at hxU
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      filter_upwards [bump_eventually_one (hAopen i) hi, eventually_ge_atTop i] with n h1 h2
      have hle : bump (Set.accumulate U i) n x ≤ bump (Set.accumulate U n) n x :=
        bump_le_bump (Set.monotone_accumulate h2) le_rfl x
      have := bump_le_one (Set.accumulate U n) n x
      rw [h1] at hle
      linarith)
  have hbound : ∀ n, L (g * bump (Set.accumulate U n) n)
      ≤ (∑' i, content L (U i)).toReal := by
    intro n
    have hadm : IsAdm (Set.accumulate U n) (g * bump (Set.accumulate U n) n) := by
      refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_nonneg (hg.nonneg x) (bump_nonneg _ n x)
      · rw [BoundedContinuousFunction.mul_apply]
        exact mul_le_one₀ (hg.le_one x) (bump_nonneg _ n x) (bump_le_one _ n x)
      · rw [BoundedContinuousFunction.mul_apply, bump_eq_zero n hx, mul_zero]
    exact (L_le_toReal_content hpos hone hadm).trans
      (ENNReal.toReal_mono hT (hAsum n))
  have hle : L g ≤ (∑' i, content L (U i)).toReal :=
    le_of_tendsto htend (Eventually.of_forall hbound)
  calc ENNReal.ofReal (L g)
      ≤ ENNReal.ofReal (∑' i, content L (U i)).toReal := ENNReal.ofReal_le_ofReal hle
    _ = ∑' i, content L (U i) := ENNReal.ofReal_toReal hT

end Subadd

/-! ## The metric outer measure -/

/-- The outer regularization of the content: infimum over open supersets. -/
private noncomputable def mSet (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : Set X) (_ : IsOpen U) (_ : A ⊆ U), content L U

private lemma mSet_def (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (A : Set X) :
    mSet L A = ⨅ (U : Set X) (_ : IsOpen U) (_ : A ⊆ U), content L U := rfl

section MSet

variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

private lemma mSet_le_content {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U) :
    mSet L A ≤ content L U := by
  rw [mSet_def]
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le _ hAU))

private lemma mSet_open {U : Set X} (hU : IsOpen U) : mSet L U = content L U := by
  refine le_antisymm (mSet_le_content hU (Subset.refl U)) ?_
  rw [mSet_def]
  exact le_iInf fun V => le_iInf fun _ => le_iInf fun hUV => content_mono L hUV

private lemma mSet_mono {A B : Set X} (hAB : A ⊆ B) : mSet L A ≤ mSet L B := by
  rw [mSet_def L B]
  exact le_iInf fun U => le_iInf fun hU => le_iInf fun hBU =>
    mSet_le_content hU (hAB.trans hBU)

private lemma mSet_empty (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : mSet L (∅ : Set X) = 0 :=
  le_antisymm
    ((mSet_le_content isOpen_empty (Subset.refl _)).trans_eq (content_empty L))
    zero_le

private lemma mSet_le_one (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (A : Set X) :
    mSet L A ≤ 1 :=
  (mSet_le_content isOpen_univ (subset_univ A)).trans (content_le_one hpos hone _)

private lemma mSet_iUnion_le (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    (s : ℕ → Set X) :
    mSet L (⋃ i, s i) ≤ ∑' i, mSet L (s i) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.mpr hε.ne') ℕ
  have hchoice : ∀ i : ℕ, ∃ V : Set X,
      IsOpen V ∧ s i ⊆ V ∧ content L V ≤ mSet L (s i) + δ i := by
    intro i
    have hne : mSet L (s i) ≠ ⊤ :=
      ((mSet_le_one hpos hone (s i)).trans_lt ENNReal.one_lt_top).ne
    have hδne : (δ i : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (hδpos i).ne'
    have hlt : mSet L (s i) < mSet L (s i) + δ i := ENNReal.lt_add_right hne hδne
    rw [mSet_def, iInf_lt_iff] at hlt
    obtain ⟨V, hV⟩ := hlt
    rw [iInf_lt_iff] at hV
    obtain ⟨hVopen, hV⟩ := hV
    rw [iInf_lt_iff] at hV
    obtain ⟨hsV, hV⟩ := hV
    exact ⟨V, hVopen, hsV, hV.le⟩
  choose V hVopen hsV hVle using hchoice
  calc mSet L (⋃ i, s i)
      ≤ content L (⋃ i, V i) :=
        mSet_le_content (isOpen_iUnion hVopen) (iUnion_mono hsV)
    _ ≤ ∑' i, content L (V i) := content_iUnion_le hpos hone hsm hVopen
    _ ≤ ∑' i, (mSet L (s i) + δ i) := ENNReal.tsum_le_tsum hVle
    _ = ∑' i, mSet L (s i) + ∑' i, (δ i : ℝ≥0∞) := ENNReal.tsum_add
    _ ≤ ∑' i, mSet L (s i) + ε := add_le_add le_rfl hδsum.le

end MSet

/-- The outer measure induced by the content. -/
private noncomputable def outer (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L) :
    OuterMeasure X where
  measureOf := mSet L
  empty := mSet_empty L
  mono := fun h => mSet_mono h
  iUnion_nat := fun s _ => mSet_iUnion_le hpos hone hsm s

private lemma outer_apply (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    (A : Set X) : outer L hpos hone hsm A = mSet L A := rfl

/-- The induced outer measure is a metric outer measure: metric-separated
sets receive disjoint open neighborhoods inside any common open superset,
and admissible gambles for those neighborhoods sum. -/
private lemma outer_isMetric (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L) :
    (outer L hpos hone hsm).IsMetric := by
  intro s t hst
  refine le_antisymm (measure_union_le s t) ?_
  rw [outer_apply, outer_apply, outer_apply, mSet_def L (s ∪ t)]
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hstU => ?_
  obtain ⟨r, hr0, hr⟩ := hst
  have hUsopen : IsOpen (U ∩ {x | Metric.infEDist x s < r / 2}) :=
    hU.inter (isOpen_lt Metric.continuous_infEDist continuous_const)
  have hUtopen : IsOpen (U ∩ {x | Metric.infEDist x t < r / 2}) :=
    hU.inter (isOpen_lt Metric.continuous_infEDist continuous_const)
  have hsUs : s ⊆ U ∩ {x | Metric.infEDist x s < r / 2} := fun x hx =>
    ⟨hstU (Or.inl hx), by
      have : Metric.infEDist x s = 0 := Metric.infEDist_zero_of_mem hx
      simp only [mem_setOf_eq, this]
      exact ENNReal.half_pos hr0⟩
  have htUt : t ⊆ U ∩ {x | Metric.infEDist x t < r / 2} := fun x hx =>
    ⟨hstU (Or.inr hx), by
      have : Metric.infEDist x t = 0 := Metric.infEDist_zero_of_mem hx
      simp only [mem_setOf_eq, this]
      exact ENNReal.half_pos hr0⟩
  have hdisj : Disjoint (U ∩ {x | Metric.infEDist x s < r / 2})
      (U ∩ {x | Metric.infEDist x t < r / 2}) := by
    rw [disjoint_left]
    rintro x ⟨-, hxs⟩ ⟨-, hxt⟩
    rw [mem_setOf_eq] at hxs hxt
    obtain ⟨y, hy, hxy⟩ := Metric.infEDist_lt_iff.mp hxs
    obtain ⟨z, hz, hxz⟩ := Metric.infEDist_lt_iff.mp hxt
    have hyz : edist y z ≤ edist y x + edist x z := edist_triangle y x z
    rw [edist_comm y x] at hyz
    have hlt : edist y z < r := by
      calc edist y z ≤ edist x y + edist x z := hyz
        _ < r / 2 + r / 2 := ENNReal.add_lt_add hxy hxz
        _ = r := ENNReal.add_halves r
    exact absurd (hr y hy z hz) (not_le.mpr hlt)
  calc mSet L s + mSet L t
      ≤ content L (U ∩ {x | Metric.infEDist x s < r / 2})
        + content L (U ∩ {x | Metric.infEDist x t < r / 2}) :=
        add_le_add (mSet_le_content hUsopen hsUs) (mSet_le_content hUtopen htUt)
    _ ≤ content L U :=
        content_add_content_le hpos hdisj inter_subset_left inter_subset_left

/-! ## Auxiliary: positive part, sums applied pointwise, epsilon room -/

/-- The positive part of a gamble, packaged by hand. -/
private noncomputable def posP (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max (f x) 0)
    (f.continuous.max continuous_const) ‖f‖
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have h1 : (0 : ℝ) ≤ max (f x) 0 := le_max_right _ _
        have h2 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
        linarith
      · refine max_le ?_ (norm_nonneg f)
        calc f x ≤ |f x| := le_abs_self _
          _ = ‖f x‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖f‖ := f.norm_coe_le_norm x)

private lemma posP_apply (f : X →ᵇ ℝ) (x : X) : posP f x = max (f x) 0 := rfl

private lemma sum_apply' {ι : Type*} (s : Finset ι) (f : ι → X →ᵇ ℝ) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        BoundedContinuousFunction.add_apply, ih]

private lemma le_add_of_forall_pos {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) :
    a ≤ b := by
  by_contra hcon
  rw [not_le] at hcon
  have := h ((a - b) / 2) (by linarith)
  linarith

/-! ## Superlevel sets and the staircase count -/

/-- The open superlevel set of a gamble. -/
private def slev (g : X →ᵇ ℝ) (t : ℝ) : Set X := {x | t < g x}

private lemma isOpen_slev (g : X →ᵇ ℝ) (t : ℝ) : IsOpen (slev g t) :=
  isOpen_lt continuous_const g.continuous

/-- The staircase count: how many of the levels `1/N, …, N/N` lie
strictly below `g x`. -/
private noncomputable def cnt (g : X →ᵇ ℝ) (N : ℕ) (x : X) : ℕ :=
  ((Finset.Icc 1 N).filter fun k : ℕ => ((k : ℝ) / (N : ℝ)) < g x).card

private lemma cnt_def (g : X →ᵇ ℝ) (N : ℕ) (x : X) :
    cnt g N x
      = ((Finset.Icc 1 N).filter fun k : ℕ => ((k : ℝ) / (N : ℝ)) < g x).card := rfl

/-- Upper staircase bound, by pigeonhole: were `N·g x < cnt`, the counted
levels would all fit strictly below the count. -/
private lemma cnt_le (g : X →ᵇ ℝ) (N : ℕ) (x : X) (hx0 : 0 ≤ g x) :
    (cnt g N x : ℝ) ≤ (N : ℝ) * g x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hz : cnt g 0 x = 0 := by
      rw [cnt_def, Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
      simp
    rw [hz]
    simp
  · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    by_contra hcon
    rw [not_le] at hcon
    have hcnt_pos : 0 < cnt g N x := by
      by_contra hc0
      rw [not_lt, Nat.le_zero] at hc0
      rw [hc0] at hcon
      simp only [Nat.cast_zero] at hcon
      nlinarith
    have hsub : ((Finset.Icc 1 N).filter fun k : ℕ => ((k : ℝ) / (N : ℝ)) < g x)
        ⊆ Finset.Icc 1 (cnt g N x - 1) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]
      refine ⟨hk.1.1, ?_⟩
      have h1 : (k : ℝ) < g x * (N : ℝ) := (div_lt_iff₀ hNR).mp hk.2
      have h2 : (k : ℝ) < (cnt g N x : ℝ) := by nlinarith
      have h3 : k < cnt g N x := by exact_mod_cast h2
      omega
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcc := cnt_def g N x
    omega

/-- Lower staircase bound, by pigeonhole: were `cnt + 1 < N·g x`, the
levels `1, …, cnt+1` would all be counted. -/
private lemma le_cnt (g : X →ᵇ ℝ) (N : ℕ) (x : X) (hx1 : g x ≤ 1) :
    (N : ℝ) * g x ≤ (cnt g N x : ℝ) + 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h0 | h
    · exfalso
      subst h0
      simp only [Nat.cast_zero, zero_mul] at hcon
      have hnn : (0 : ℝ) ≤ (cnt g 0 x : ℝ) + 1 := by positivity
      linarith
    · exact_mod_cast h
  have hsub : Finset.Icc 1 (cnt g N x + 1)
      ⊆ (Finset.Icc 1 N).filter fun k : ℕ => ((k : ℝ) / (N : ℝ)) < g x := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : (k : ℝ) ≤ (cnt g N x : ℝ) + 1 := by exact_mod_cast hk.2
    have hklt : (k : ℝ) < (N : ℝ) * g x := lt_of_le_of_lt hkR hcon
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hk.1, ?_⟩, ?_⟩
    · have hNg : (N : ℝ) * g x ≤ (N : ℝ) := by nlinarith
      have h2 : (k : ℝ) < (N : ℝ) := lt_of_lt_of_le hklt hNg
      have h3 : k < N := by exact_mod_cast h2
      exact h3.le
    · rw [div_lt_iff₀ hN0]
      nlinarith
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcc := cnt_def g N x
  omega

private lemma cnt_eq_sum_ite (g : X →ᵇ ℝ) (N : ℕ) (x : X) :
    (cnt g N x : ℝ)
      = ∑ k ∈ Finset.Icc 1 N, if ((k : ℝ) / (N : ℝ)) < g x then (1 : ℝ) else 0 := by
  rw [cnt_def, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

private lemma cnt_eq_sum (g : X →ᵇ ℝ) (N : ℕ) (x : X) :
    (cnt g N x : ℝ)
      = ∑ k ∈ Finset.Icc 1 N,
          (slev g ((k : ℝ) / (N : ℝ))).indicator (fun _ => (1 : ℝ)) x := by
  rw [cnt_eq_sum_ite]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hmem : ((k : ℝ) / (N : ℝ)) < g x
  · rw [if_pos hmem, Set.indicator_of_mem (show x ∈ slev g _ from hmem)]
  · rw [if_neg hmem, Set.indicator_of_notMem (show x ∉ slev g _ from hmem)]

/-! ## The bump sum and the deficiency gamble -/

/-- The sum of the level bumps at stage `m`. -/
private noncomputable def bumpSum (g : X →ᵇ ℝ) (N m : ℕ) : X →ᵇ ℝ :=
  ∑ k ∈ Finset.Icc 1 N, bump (slev g ((k : ℝ) / (N : ℝ))) m

private lemma bumpSum_apply (g : X →ᵇ ℝ) (N m : ℕ) (x : X) :
    bumpSum g N m x
      = ∑ k ∈ Finset.Icc 1 N, bump (slev g ((k : ℝ) / (N : ℝ))) m x :=
  sum_apply' _ _ x

private lemma bumpSum_le_succ (g : X →ᵇ ℝ) (N m : ℕ) (x : X) :
    bumpSum g N m x ≤ bumpSum g N (m + 1) x := by
  rw [bumpSum_apply, bumpSum_apply]
  exact Finset.sum_le_sum fun k _ => bump_le_bump (Subset.refl _) (Nat.le_succ m) x

private lemma bumpSum_eventually (g : X →ᵇ ℝ) (N : ℕ) (x : X) :
    ∀ᶠ m in atTop, bumpSum g N m x = (cnt g N x : ℝ) := by
  have hall : ∀ᶠ m in atTop, ∀ k ∈ Finset.Icc 1 N,
      bump (slev g ((k : ℝ) / (N : ℝ))) m x
        = if ((k : ℝ) / (N : ℝ)) < g x then (1 : ℝ) else 0 := by
    rw [eventually_all_finset]
    intro k _
    by_cases hmem : ((k : ℝ) / (N : ℝ)) < g x
    · filter_upwards [bump_eventually_one (isOpen_slev g _)
        (show x ∈ slev g _ from hmem)] with m hm
      rw [hm, if_pos hmem]
    · filter_upwards with m
      rw [bump_eq_zero m (show x ∉ slev g _ from hmem), if_neg hmem]
  filter_upwards [hall] with m hm
  rw [bumpSum_apply, cnt_eq_sum_ite]
  exact Finset.sum_congr rfl hm

/-- The deficiency gamble at stage `m`: the positive part of what remains
of `g` after the slack `1/N` and the scaled bump sum. -/
private noncomputable def defic (g : X →ᵇ ℝ) (N m : ℕ) : X →ᵇ ℝ :=
  posP (g - (N : ℝ)⁻¹ • BoundedContinuousFunction.const X (1 : ℝ)
    - (N : ℝ)⁻¹ • bumpSum g N m)

private lemma defic_apply (g : X →ᵇ ℝ) (N m : ℕ) (x : X) :
    defic g N m x = max (g x - (N : ℝ)⁻¹ - (N : ℝ)⁻¹ * bumpSum g N m x) 0 := by
  have h : (g - (N : ℝ)⁻¹ • BoundedContinuousFunction.const X (1 : ℝ)
      - (N : ℝ)⁻¹ • bumpSum g N m) x
      = g x - (N : ℝ)⁻¹ - (N : ℝ)⁻¹ * bumpSum g N m x := by
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.const_apply', smul_eq_mul, mul_one]
  rw [← h]
  rfl

section MeasureSide

variable [MeasurableSpace X] [BorelSpace X]
variable {L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ}

private lemma integrable_cnt (μ : Measure X) [IsFiniteMeasure μ] (g : X →ᵇ ℝ) (N : ℕ) :
    Integrable (fun x => (cnt g N x : ℝ)) μ := by
  have h : (fun x => (cnt g N x : ℝ))
      = fun x => ∑ k ∈ Finset.Icc 1 N,
          (slev g ((k : ℝ) / (N : ℝ))).indicator (fun _ => (1 : ℝ)) x :=
    funext fun x => cnt_eq_sum g N x
  rw [h]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_const (1 : ℝ)).indicator (isOpen_slev g _).measurableSet

private lemma integral_cnt (μ : Measure X) [IsFiniteMeasure μ] (g : X →ᵇ ℝ) (N : ℕ) :
    ∫ x, (cnt g N x : ℝ) ∂μ
      = ∑ k ∈ Finset.Icc 1 N, μ.real (slev g ((k : ℝ) / (N : ℝ))) := by
  have h1 : ∫ x, (cnt g N x : ℝ) ∂μ
      = ∫ x, ∑ k ∈ Finset.Icc 1 N,
          (slev g ((k : ℝ) / (N : ℝ))).indicator (fun _ => (1 : ℝ)) x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact cnt_eq_sum g N x
  rw [h1, integral_finsetSum _ fun k _ =>
    (integrable_const (1 : ℝ)).indicator (isOpen_slev g _).measurableSet]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const (1 : ℝ) (isOpen_slev g _).measurableSet, smul_eq_mul,
    mul_one]

/-- The staircase-content bridge: on open superlevels the measure agrees
with the content, so the count integrates to the content sum. -/
private lemma integral_cnt_eq_content (μ : Measure X) [IsFiniteMeasure μ]
    (hopen : ∀ U : Set X, IsOpen U → μ U = content L U) (g : X →ᵇ ℝ) (N : ℕ) :
    ∫ x, (cnt g N x : ℝ) ∂μ
      = ∑ k ∈ Finset.Icc 1 N, (content L (slev g ((k : ℝ) / (N : ℝ)))).toReal := by
  rw [integral_cnt μ g N]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [measureReal_def, hopen _ (isOpen_slev g _)]

/-- Per-`N` upper bound: sigma-smoothness sends the deficiency to zero,
leaving `L g ≤ 1/N + ∫ g`. -/
private lemma L_le_key (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hopen : ∀ U : Set X, IsOpen U → μ U = content L U)
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    L g ≤ (N : ℝ)⁻¹ + ∫ x, g x ∂μ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set C : ℝ := ∑ k ∈ Finset.Icc 1 N, (content L (slev g ((k : ℝ) / (N : ℝ)))).toReal
    with hC
  -- the deficiency is antitone and vanishes pointwise
  have hanti : ∀ m x, defic g N (m + 1) x ≤ defic g N m x := by
    intro m x
    rw [defic_apply, defic_apply]
    have h1 : (N : ℝ)⁻¹ * bumpSum g N m x ≤ (N : ℝ)⁻¹ * bumpSum g N (m + 1) x :=
      mul_le_mul_of_nonneg_left (bumpSum_le_succ g N m x) (by positivity)
    exact max_le_max (by linarith) le_rfl
  have hlim : ∀ x, Tendsto (fun m => defic g N m x) atTop (nhds 0) := by
    intro x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [bumpSum_eventually g N x] with m hm
    rw [defic_apply, hm]
    have hle : g x - (N : ℝ)⁻¹ - (N : ℝ)⁻¹ * (cnt g N x : ℝ) ≤ 0 := by
      have h1 := le_cnt g N x (hg1 x)
      have h2 : g x ≤ ((cnt g N x : ℝ) + 1) * (N : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hNR]
        linarith
      have h3 : ((cnt g N x : ℝ) + 1) * (N : ℝ)⁻¹
          = (N : ℝ)⁻¹ * (cnt g N x : ℝ) + (N : ℝ)⁻¹ := by ring
      rw [h3] at h2
      linarith
    exact (max_eq_right hle).symm
  have hLd := hsm (fun m => defic g N m) hanti hlim
  -- the per-stage bound
  have hLm : ∀ m, L g ≤ ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ * C) + L (defic g N m) := by
    intro m
    have hpt : ∀ x, g x
        ≤ ((N : ℝ)⁻¹ • BoundedContinuousFunction.const X (1 : ℝ)
          + (N : ℝ)⁻¹ • bumpSum g N m + defic g N m) x := by
      intro x
      have hd : g x - (N : ℝ)⁻¹ - (N : ℝ)⁻¹ * bumpSum g N m x ≤ defic g N m x := by
        rw [defic_apply]
        exact le_max_left _ _
      simp only [BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.const_apply',
        smul_eq_mul, mul_one]
      linarith
    have h1 := L_mono hpos hpt
    rw [map_add, map_add, map_smul, map_smul, hone, smul_eq_mul, smul_eq_mul,
      mul_one] at h1
    have h2 : L (bumpSum g N m)
        = ∑ k ∈ Finset.Icc 1 N, L (bump (slev g ((k : ℝ) / (N : ℝ))) m) :=
      map_sum L _ _
    have h3 : ∑ k ∈ Finset.Icc 1 N, L (bump (slev g ((k : ℝ) / (N : ℝ))) m) ≤ C := by
      rw [hC]
      exact Finset.sum_le_sum fun k _ =>
        L_le_toReal_content hpos hone (isAdm_bump _ m)
    have h4 : L (bumpSum g N m) ≤ C := h2 ▸ h3
    have h5 : (N : ℝ)⁻¹ * L (bumpSum g N m) ≤ (N : ℝ)⁻¹ * C :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  -- pass to the limit in `m`
  have hfin : Tendsto (fun m => ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ * C) + L (defic g N m)) atTop
      (nhds (((N : ℝ)⁻¹ + (N : ℝ)⁻¹ * C) + 0)) := tendsto_const_nhds.add hLd
  have hle : L g ≤ ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ * C) + 0 :=
    ge_of_tendsto hfin (Eventually.of_forall hLm)
  -- compare the content sum with the integral
  have hCint : C = ∫ x, (cnt g N x : ℝ) ∂μ :=
    (integral_cnt_eq_content μ hopen g N).symm
  have hcnt_int : ∫ x, (cnt g N x : ℝ) ∂μ ≤ (N : ℝ) * ∫ x, g x ∂μ := by
    have hmono := integral_mono (integrable_cnt μ g N)
      (((g.integrable μ)).const_mul (N : ℝ)) (fun x => by
        have := cnt_le g N x (hg0 x)
        simpa using this)
    rwa [integral_const_mul] at hmono
  have hC_le : C ≤ (N : ℝ) * ∫ x, g x ∂μ := by
    rw [hCint]
    exact hcnt_int
  have h6 : (N : ℝ)⁻¹ * C ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ∫ x, g x ∂μ) :=
    mul_le_mul_of_nonneg_left hC_le (by positivity)
  have h7 : (N : ℝ)⁻¹ * ((N : ℝ) * ∫ x, g x ∂μ) = ∫ x, g x ∂μ := by
    rw [← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul]
  rw [h7] at h6
  linarith

/-- Per-`N`, per-`ε` lower bound: near-optimal admissible gambles under
each superlevel sum below `N·(L g + ε)`, and the staircase minorizes the
integral within `1/N`. -/
private lemma integral_le_key (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hopen : ∀ U : Set X, IsOpen U → μ U = content L U)
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, g x ∂μ ≤ L g + ε + (N : ℝ)⁻¹ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- choose near-optimal admissible gambles for the superlevels
  choose q hq hqle using fun k : ℕ =>
    exists_adm_near hpos hone (slev g ((k : ℝ) / (N : ℝ))) hε
  -- their sum is pointwise below `N · g`
  have hsum_pt : ∀ x, (∑ k ∈ Finset.Icc 1 N, q k) x ≤ (N : ℝ) * g x := by
    intro x
    rw [sum_apply']
    have h1 : ∑ k ∈ Finset.Icc 1 N, q k x ≤ (cnt g N x : ℝ) := by
      rw [cnt_eq_sum_ite]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hmem : ((k : ℝ) / (N : ℝ)) < g x
      · rw [if_pos hmem]
        exact (hq k).le_one x
      · rw [if_neg hmem]
        exact le_of_eq ((hq k).eq_zero x (show x ∉ slev g _ from hmem))
    exact h1.trans (cnt_le g N x (hg0 x))
  -- the content sum is bounded through the functional
  have hLsum : ∑ k ∈ Finset.Icc 1 N, (content L (slev g ((k : ℝ) / (N : ℝ)))).toReal
      ≤ (N : ℝ) * L g + (N : ℝ) * ε := by
    have h1 : ∑ k ∈ Finset.Icc 1 N, (content L (slev g ((k : ℝ) / (N : ℝ)))).toReal
        ≤ ∑ k ∈ Finset.Icc 1 N, (L (q k) + ε) :=
      Finset.sum_le_sum fun k _ => hqle k
    have h2 : ∑ k ∈ Finset.Icc 1 N, (L (q k) + ε)
        = (∑ k ∈ Finset.Icc 1 N, L (q k)) + (N : ℝ) * ε := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    have h3 : ∑ k ∈ Finset.Icc 1 N, L (q k) = L (∑ k ∈ Finset.Icc 1 N, q k) :=
      (map_sum L _ _).symm
    have h4 : L (∑ k ∈ Finset.Icc 1 N, q k) ≤ L ((N : ℝ) • g) := by
      refine L_mono hpos fun x => ?_
      rw [BoundedContinuousFunction.smul_apply, smul_eq_mul]
      exact hsum_pt x
    have h5 : L ((N : ℝ) • g) = (N : ℝ) * L g := by rw [map_smul, smul_eq_mul]
    rw [h2] at h1
    rw [h3] at h1
    rw [h5] at h4
    linarith
  -- the count majorizes `N·g - 1` in integral
  have hint : (N : ℝ) * ∫ x, g x ∂μ ≤ (∫ x, (cnt g N x : ℝ) ∂μ) + 1 := by
    have hi1 : Integrable (fun x => (cnt g N x : ℝ) + 1) μ :=
      (integrable_cnt μ g N).add (integrable_const 1)
    have hi2 : Integrable (fun x => (N : ℝ) * g x) μ :=
      (g.integrable μ).const_mul (N : ℝ)
    have hmono := integral_mono hi2 hi1 (fun x => by
      have := le_cnt g N x (hg1 x)
      simpa using this)
    rw [integral_const_mul] at hmono
    rwa [integral_add (integrable_cnt μ g N) (integrable_const 1),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      at hmono
  -- assemble and divide by `N`
  have hCint : ∫ x, (cnt g N x : ℝ) ∂μ
      = ∑ k ∈ Finset.Icc 1 N, (content L (slev g ((k : ℝ) / (N : ℝ)))).toReal :=
    integral_cnt_eq_content μ hopen g N
  have hchain : (N : ℝ) * ∫ x, g x ∂μ ≤ (N : ℝ) * L g + (N : ℝ) * ε + 1 := by
    rw [hCint] at hint
    linarith
  have hexp : (N : ℝ) * (L g + ε + (N : ℝ)⁻¹)
      = (N : ℝ) * L g + (N : ℝ) * ε + 1 := by
    rw [mul_add, mul_add, mul_inv_cancel₀ hNR.ne']
  have h2 : (N : ℝ) * ∫ x, g x ∂μ ≤ (N : ℝ) * (L g + ε + (N : ℝ)⁻¹) := by
    rw [hexp]
    exact hchain
  exact le_of_mul_le_mul_left h2 hNR

/-- The two-sided identity on `[0,1]`-valued gambles. -/
private lemma L_eq_integral_core (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hopen : ∀ U : Set X, IsOpen U → μ U = content L U)
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    L g = ∫ x, g x ∂μ := by
  refine le_antisymm ?_ ?_
  · -- L g ≤ ∫ g
    refine le_add_of_forall_pos fun η hη => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    have hkey := L_le_key hpos hone hsm μ hopen g hg0 hg1 (n + 1) (Nat.succ_pos n)
    have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ < η := by
      rw [one_div] at hn
      exact_mod_cast hn
    linarith
  · -- ∫ g ≤ L g
    refine le_add_of_forall_pos fun η hη => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hη)
    have hkey := integral_le_key hpos hone μ hopen g hg0 hg1 (n + 1) (Nat.succ_pos n)
      (half_pos hη)
    have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ < η / 2 := by
      rw [one_div] at hn
      exact_mod_cast hn
    linarith

/-- The identity extends to all gambles by an affine renormalization. -/
private lemma L_eq_integral (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hopen : ∀ U : Set X, IsOpen U → μ U = content L U)
    (g : X →ᵇ ℝ) : L g = ∫ x, g x ∂μ := by
  set c : ℝ := ‖g‖ + 1 with hc
  have hc0 : (0 : ℝ) < c := by positivity
  have h2c : (0 : ℝ) < 2 * c := by linarith
  have hb : ∀ x, |g x| ≤ ‖g‖ := fun x => by
    rw [← Real.norm_eq_abs]
    exact g.norm_coe_le_norm x
  set h : X →ᵇ ℝ := (2 * c)⁻¹ • (g + BoundedContinuousFunction.const X c) with hh
  have happ : ∀ x, h x = (2 * c)⁻¹ * (g x + c) := by
    intro x
    rw [hh]
    simp only [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply', smul_eq_mul]
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x
    rw [happ]
    have h1 := (abs_le.mp (hb x)).1
    have h2 : 0 ≤ g x + c := by
      rw [hc]
      linarith
    positivity
  have hh1 : ∀ x, h x ≤ 1 := by
    intro x
    rw [happ]
    have h1 := (abs_le.mp (hb x)).2
    have h2 : g x + c ≤ 2 * c := by
      rw [hc]
      linarith
    calc (2 * c)⁻¹ * (g x + c) ≤ (2 * c)⁻¹ * (2 * c) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := inv_mul_cancel₀ h2c.ne'
  have hcore := L_eq_integral_core hpos hone hsm μ hopen h hh0 hh1
  have hLh : L h = (2 * c)⁻¹ * (L g + c) := by
    rw [hh, map_smul, map_add, L_const hone, smul_eq_mul]
  have hIh : ∫ x, h x ∂μ = (2 * c)⁻¹ * ((∫ x, g x ∂μ) + c) := by
    have h1 : ∫ x, h x ∂μ
        = ∫ x, (2 * c)⁻¹ * ((g + BoundedContinuousFunction.const X c) x) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [happ, BoundedContinuousFunction.add_apply,
        BoundedContinuousFunction.const_apply']
    rw [h1, integral_const_mul, BoundedContinuousFunction.integral_add_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hLh, hIh] at hcore
  have hne : ((2 * c)⁻¹ : ℝ) ≠ 0 := inv_ne_zero h2c.ne'
  have := mul_left_cancel₀ hne hcore
  linarith

/-- Existence of the representing probability measure, unbundled. -/
private lemma exists_measure (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hpos : Pos L)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1) (hsm : Smooth L) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ g : X →ᵇ ℝ, L g = ∫ x, g x ∂μ := by
  have hcar : ‹MeasurableSpace X› ≤ (outer L hpos hone hsm).caratheodory :=
    le_trans (le_of_eq (BorelSpace.measurable_eq (α := X)))
      (outer_isMetric L hpos hone hsm).borel_le_caratheodory
  set μ : Measure X := (outer L hpos hone hsm).toMeasure hcar with hμ
  have hopen : ∀ U : Set X, IsOpen U → μ U = content L U := by
    intro U hU
    rw [hμ, toMeasure_apply _ _ hU.measurableSet, outer_apply]
    exact mSet_open hU
  have hprob : IsProbabilityMeasure μ :=
    ⟨by rw [hopen univ isOpen_univ, content_univ hpos hone]⟩
  haveI := hprob
  exact ⟨μ, hprob, fun g => L_eq_integral hpos hone hsm μ hopen g⟩

end MeasureSide

end SigmaSmoothRep

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A positive, normalized, sigma-smooth linear functional on bounded
continuous real gambles over a metric Borel carrier is integration
against a countably additive Borel probability measure. -/
theorem exists_probabilityMeasure_of_sigmaSmooth
    (L : (X →ᵇ ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ g : X →ᵇ ℝ, (∀ x, 0 ≤ g x) → 0 ≤ L g)
    (hone : L (BoundedContinuousFunction.const X (1 : ℝ)) = 1)
    (hsmooth : ∀ h : ℕ → (X →ᵇ ℝ), (∀ n x, h (n + 1) x ≤ h n x) →
      (∀ x, Filter.Tendsto (fun n => h n x) Filter.atTop (nhds 0)) →
      Filter.Tendsto (fun n => L (h n)) Filter.atTop (nhds 0)) :
    ∃ μ : MeasureTheory.ProbabilityMeasure X,
      ∀ g : X →ᵇ ℝ, L g = ∫ x, g x ∂(μ : MeasureTheory.Measure X) := by
  obtain ⟨μ, hμ, hrep⟩ := SigmaSmoothRep.exists_measure L hpos hone hsmooth
  exact ⟨⟨μ, hμ⟩, hrep⟩

end SuFunctor.Universe.General
