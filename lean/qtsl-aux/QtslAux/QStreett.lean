import QtslAux.Battery
import QtslAux.Excursions
import Mathlib.Probability.Martingale.Convergence

/-! # Quantitative Streett conditions for Markov chains

This module proves probability lower bounds for Streett (request–response)
acceptance conditions along the path measure of a Markov kernel `K` on a
measurable state space: with probability at least `p`, every request set
`Rq i` that is visited infinitely often is answered by infinitely many visits
to the corresponding response set `G i`.

The method localizes a per-pair supermartingale `W i` to the survival event of
a confinement region (via the indicator-localized process `loc` and the
flag-augmented observation `flagged`), applies the excursion argument on
almost-supermartingales with `ε`-decrease at request times, and combines the
pairs with a fail-closed safety battery that keeps paths confined with
probability `p`.

Principal declarations:

* `loc W A n`: the value `W (ω n)` localized to survival of `Aᶜ` up to `n`.
* `streett_pair_localized`: almost surely, a confined path that satisfies the
  request set infinitely often satisfies the response set infinitely often,
  given a bounded nonnegative `W` with supermartingale drift off `G` and
  drift `≤ W - ε` at requests.
* `sound_QStreettBundle`: the bundled bound
  `ENNReal.ofReal p ≤ pathMeasure K x {ω | ∀ i, GF-Rq i → GF-G i}` for
  countably many Streett pairs under a common confinement certificate `V₀`.
* `sound_StreettDegenerate`: the degenerate form with trivial requests
  (unconditional recurrence of every `G i`).
* `sound_QStreettBundle_tie`: transport along per-pair predicate inclusions
  (`reqSat ⊆ Rq`, `G ⊆ respSat`).
* `AbsorptionBound` and `sound_QStreettBundle_carved`: a carve-out variant in
  which each pair may also stop decreasing on a set `J i`, provided that from
  `J i` the future probability of ever hitting `Rq i` is bounded away from
  `1`; a Lévy upward argument (`ae_not_frequently_of_absorption`) shows such
  paths almost surely stop requesting.
* `supermartingale_stopped_shift`, `measure_reach_after_le`,
  `absorptionBound_of_kernel`: discharge of `AbsorptionBound` from a kernel
  drift certificate `Va` via a stopped supermartingale started at time `k` and
  a maximal (Ville-type) inequality for the shifted process.
* `sound_QStreettBundle_carved_discharged`: the carved bundle with the
  absorption side conditions replaced by the kernel-level `Va` certificates.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Finset Function Filter

namespace Qtsl.QStreett

open Qtsl.Battery

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma survive_succ_iff {A : Set S} {n : ℕ} {ω : ℕ → S} :
    ω ∈ survive A (n + 1) ↔ ω ∈ survive A n ∧ ω (n + 1) ∉ A := by
  simp only [mem_survive]
  constructor
  · exact fun h => ⟨fun k hk => h k (hk.trans n.le_succ), h (n + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hlt | rfl
    · exact h1 k (Nat.lt_succ_iff.1 hlt)
    · exact h2

omit [MeasurableSpace S] in

lemma not_mem_of_survive {A : Set S} {n : ℕ} {ω : ℕ → S} (h : ω ∈ survive A n) :
    ω n ∉ A := h n le_rfl

omit [MeasurableSpace S] in
private lemma updateFinset_eq_of_le {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S} {k : ℕ}
    (hk : k ≤ n) : updateFinset y (Iic n) u k = u ⟨k, mem_Iic.2 hk⟩ := by
  simp [updateFinset, mem_Iic, hk]

omit [MeasurableSpace S] in
private lemma updateFinset_eq_succ {y : ℕ → S} {n : ℕ} {u : Π _i : Iic n, S} :
    updateFinset y (Iic n) u (n + 1) = y (n + 1) := by
  simp [updateFinset, mem_Iic]

/-- The certificate value `W (ω n)`, localized to the survival event: it equals
`W (ω n)` while the path has avoided `A` through time `n`, and `0` afterwards. -/
noncomputable def loc (W : S → ℝ) (A : Set S) (n : ℕ) (ω : ℕ → S) : ℝ :=
  (survive A n).indicator (fun ω' => W (ω' n)) ω

omit [MeasurableSpace S] in
lemma loc_of_survive {W : S → ℝ} {A : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∈ survive A n) : loc W A n ω = W (ω n) :=
  Set.indicator_of_mem h _

omit [MeasurableSpace S] in
lemma loc_of_not_survive {W : S → ℝ} {A : Set S} {n : ℕ} {ω : ℕ → S}
    (h : ω ∉ survive A n) : loc W A n ω = 0 :=
  Set.indicator_of_notMem h _

lemma measurable_loc {W : S → ℝ} {A : Set S} (hA : MeasurableSet A)
    (hW : Measurable W) (n : ℕ) : Measurable (loc W A n) :=
  (hW.comp (measurable_pi_apply n)).indicator
    (((Filtration.piLE (X := fun _ : ℕ => S)).le n) _ (measurableSet_survive_piLE hA n))

/-- The state at time `n` paired with a survival flag: the first component is
`1` exactly while the path has avoided `A` through time `n`. Request and
response events are read off this pair via `flaggedReq` and `flaggedResp`, so
that they refer to the confined portion of the path only. -/
noncomputable def flagged (A : Set S) (n : ℕ) (ω : ℕ → S) : ℝ × S :=
  ((survive A n).indicator (fun _ => (1 : ℝ)) ω, ω n)

def flaggedReq (Rq : Set S) : Set (ℝ × S) := {q | q.1 = 1 ∧ q.2 ∈ Rq}

def flaggedResp (G : Set S) : Set (ℝ × S) := {q | q.1 ≠ 1 ∨ q.2 ∈ G}

omit [MeasurableSpace S] in
private lemma indicator_one_eq_one_iff {A : Set (ℕ → S)} {ω : ℕ → S} :
    A.indicator (fun _ => (1 : ℝ)) ω = 1 ↔ ω ∈ A := by
  by_cases h : ω ∈ A
  · simp [h]
  · simp [h]

omit [MeasurableSpace S] in
lemma flagged_mem_req_iff {A : Set S} {Rq : Set S} {n : ℕ} {ω : ℕ → S} :
    flagged A n ω ∈ flaggedReq Rq ↔ ω ∈ survive A n ∧ ω n ∈ Rq := by
  unfold flagged flaggedReq
  simp only [Set.mem_setOf_eq, indicator_one_eq_one_iff]

omit [MeasurableSpace S] in
lemma flagged_mem_resp_iff {A : Set S} {G : Set S} {n : ℕ} {ω : ℕ → S} :
    flagged A n ω ∈ flaggedResp G ↔ ω ∉ survive A n ∨ ω n ∈ G := by
  unfold flagged flaggedResp
  simp only [Set.mem_setOf_eq, ne_eq, indicator_one_eq_one_iff]

lemma measurableSet_flagged_req {A Rq : Set S} (hA : MeasurableSet A)
    (hRq : MeasurableSet Rq) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n]
      {ω | flagged A n ω ∈ flaggedReq Rq} := by
  have h : {ω : ℕ → S | flagged A n ω ∈ flaggedReq Rq}
      = survive A n ∩ (fun ω : ℕ → S => ω n) ⁻¹' Rq := by
    ext ω; exact flagged_mem_req_iff
  rw [h]
  exact (measurableSet_survive_piLE hA n).inter ((measurable_coord_piLE le_rfl) hRq)

lemma measurableSet_flagged_resp {A G : Set S} (hA : MeasurableSet A)
    (hG : MeasurableSet G) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n]
      {ω | flagged A n ω ∈ flaggedResp G} := by
  have h : {ω : ℕ → S | flagged A n ω ∈ flaggedResp G}
      = (survive A n)ᶜ ∪ (fun ω : ℕ → S => ω n) ⁻¹' G := by
    ext ω; exact flagged_mem_resp_iff
  rw [h]
  exact ((measurableSet_survive_piLE hA n).compl).union
    ((measurable_coord_piLE le_rfl) hG)

section Localized

variable {K : Kernel S S} [IsMarkovKernel K]

omit [MeasurableSpace S] in

private lemma loc_succ_patched {W : S → ℝ} {A : Set S} {n : ℕ} {ω : ℕ → S}
    (hs : ω ∈ survive A n) (y : ℕ → S) :
    loc W A (n + 1) (updateFinset y (Iic n) (Preorder.frestrictLe n ω))
      = Aᶜ.indicator W (y (n + 1)) := by
  have hagree : ∀ k ≤ n,
      updateFinset y (Iic n) (Preorder.frestrictLe n ω) k = ω k := fun k hk => by
    rw [updateFinset_eq_of_le hk]; rfl
  have hz : updateFinset y (Iic n) (Preorder.frestrictLe n ω) ∈ survive A n :=
    (survive_congr hagree).2 hs
  by_cases hy : y (n + 1) ∈ A
  · have : updateFinset y (Iic n) (Preorder.frestrictLe n ω) ∉ survive A (n + 1) := by
      rw [survive_succ_iff, updateFinset_eq_succ]
      exact fun h => h.2 hy
    rw [loc_of_not_survive this, Set.indicator_of_notMem (by simpa using hy)]
  · have : updateFinset y (Iic n) (Preorder.frestrictLe n ω) ∈ survive A (n + 1) := by
      rw [survive_succ_iff, updateFinset_eq_succ]
      exact ⟨hz, hy⟩
    rw [loc_of_survive this, updateFinset_eq_succ,
      Set.indicator_of_mem (by simpa using hy)]

private lemma condExp_loc_succ_le {W : S → ℝ} {A Dbar : Set S} {x : S}
    (hA : MeasurableSet A) (hDbar : MeasurableSet Dbar) (hW : Measurable W)
    (hW0 : ∀ y ∈ Dbar, 0 ≤ W y)
    (hint : ∀ m, Integrable (loc W A m) (pathMeasure K x)) (n : ℕ) :
    ∀ᵐ ω ∂pathMeasure K x, ω ∈ survive A n →
      K (ω n) Dbar = 1 → Integrable W (K (ω n)) →
      ((pathMeasure K x)[loc W A (n + 1) | Filtration.piLE (X := fun _ : ℕ => S) n]) ω
        ≤ ∫ z, W z ∂K (ω n) := by
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.zero_le n) (x₀ := fun _ => x) (hint (n + 1))
  filter_upwards [hcond] with ω hcondω hs hmass hWint
  have hg : Measurable (Aᶜ.indicator W) := hW.indicator hA.compl
  have hmeasl : AEStronglyMeasurable (loc W A (n + 1))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)) :=
    (measurable_loc hA hW (n + 1)).aestronglyMeasurable
  have hkey : ∫ y, loc W A (n + 1) y
      ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)
      ≤ ∫ z, W z ∂K (ω n) := by

    have h1 : ∫ y, loc W A (n + 1) y
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)
        = ∫ y : ℕ → S, Aᶜ.indicator W (y (n + 1))
          ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n
            (Preorder.frestrictLe n ω) := by
      rw [Kernel.integral_traj _ hmeasl]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => loc_succ_patched hs y)

    have h2 : ∫ y : ℕ → S, Aᶜ.indicator W (y (n + 1))
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) n (Preorder.frestrictLe n ω)
        = ∫ z, Aᶜ.indicator W z ∂K (ω n) := by
      have hmapK := DFunLike.congr_fun
        (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := mchain K) (a := n))
        (Preorder.frestrictLe n ω)
      rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
      have hcoord : (mchain K n) (Preorder.frestrictLe n ω) = K (ω n) := by
        rw [mchain_apply]; rfl
      rw [← hcoord, ← hmapK,
        integral_map_of_stronglyMeasurable (measurable_pi_apply _) hg.stronglyMeasurable]

    have h3 : ∫ z, Aᶜ.indicator W z ∂K (ω n) ≤ ∫ z, W z ∂K (ω n) := by
      have hae : ∀ᵐ z ∂K (ω n), z ∈ Dbar := by
        have h0 : K (ω n) Dbarᶜ = 0 := by
          rw [prob_compl_eq_one_sub hDbar, hmass, tsub_self]
        rw [ae_iff]
        exact h0
      refine integral_mono_ae (hWint.indicator hA.compl) hWint ?_
      filter_upwards [hae] with z hz
      by_cases hzA : z ∈ A
      · rw [Set.indicator_of_notMem (by simpa using hzA)]
        exact hW0 z hz
      · rw [Set.indicator_of_mem (by simpa using hzA)]
    rw [h1, h2]
    exact h3
  exact le_trans (le_of_eq hcondω) hkey

/-- Single Streett pair, localized to confinement. Suppose `W` is a measurable
certificate that is nonnegative and bounded by `C` on `Dbar`, has
supermartingale drift (`∫ W dK y ≤ W y`) at confined non-response states, and
strictly decreases in expectation by `ε > 0` at confined request states that
are not responses. Then almost every path of the chain from `x` that stays in
`D \ U` forever and visits the request set `Rq` infinitely often also visits
the response set `G` infinitely often: an infinite tail of unanswered requests
would drive the localized nonnegative process `loc W (U ∪ Dᶜ)` down by `ε`
infinitely often, contradicting the excursion bound for almost-supermartingales. -/
theorem streett_pair_localized {D Dbar U Rq G : Set S} {W : S → ℝ} {ε C : ℝ} {x : S}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hRq : MeasurableSet Rq) (hG : MeasurableSet G) (hW : Measurable W)
    (hε : 0 < ε) (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hW0 : ∀ y ∈ Dbar, 0 ≤ W y) (hWC : ∀ y ∈ Dbar, W y ≤ C)
    (hWint : ∀ y ∈ D, y ∉ U → y ∉ G → Integrable W (K y))
    (hWdrift : ∀ y ∈ D, y ∉ U → y ∉ G → ∫ z, W z ∂K y ≤ W y)
    (hWdriftR : ∀ y ∈ D, y ∉ U → y ∈ Rq → y ∉ G → ∫ z, W z ∂K y ≤ W y - ε) :
    ∀ᵐ ω ∂pathMeasure K x, (∀ n, ω n ∈ D \ U) →
      (∃ᶠ n in atTop, ω n ∈ Rq) → ∃ᶠ n in atTop, ω n ∈ G := by
  set A : Set S := U ∪ Dᶜ with hAdef
  have hAmeas : MeasurableSet A := hU.union hD.compl

  have hsurv_state : ∀ {n : ℕ} {ω : ℕ → S}, ω ∈ survive A n → ω n ∈ D ∧ ω n ∉ U := by
    intro n ω h
    have hnA := not_mem_of_survive h
    rw [hAdef] at hnA
    exact ⟨not_not.1 fun hD' => hnA (Or.inr hD'), fun hU' => hnA (Or.inl hU')⟩

  have hloc0 : ∀ (n : ℕ) (ω : ℕ → S), 0 ≤ loc W A n ω := by
    intro n ω
    by_cases h : ω ∈ survive A n
    · rw [loc_of_survive h]
      exact hW0 _ (hDsub (hsurv_state h).1)
    · rw [loc_of_not_survive h]
  have hlocC : ∀ (n : ℕ) (ω : ℕ → S), loc W A n ω ≤ max C 0 := by
    intro n ω
    by_cases h : ω ∈ survive A n
    · rw [loc_of_survive h]
      exact le_max_of_le_left (hWC _ (hDsub (hsurv_state h).1))
    · rw [loc_of_not_survive h]
      exact le_max_right _ _
  have hint : ∀ n, Integrable (loc W A n) (pathMeasure K x) := by
    intro n
    refine (integrable_const (max C 0)).mono'
      (measurable_loc hAmeas hW n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hloc0 n ω)]
    exact hlocC n ω

  have hresp_not : ∀ {n : ℕ} {ω : ℕ → S}, flagged A n ω ∉ flaggedResp G →
      ω ∈ survive A n ∧ ω n ∉ G := by
    intro n ω hnG
    have h' : ¬(ω ∉ survive A n ∨ ω n ∈ G) := fun h => hnG (flagged_mem_resp_iff.2 h)
    obtain ⟨h1, h2⟩ := not_or.1 h'
    exact ⟨not_not.1 h1, h2⟩

  have hK5c := Qtsl.Excursions.streett_ae_frequently_response
    (μ := pathMeasure K x) (𝒢 := Filtration.piLE (X := fun _ : ℕ => S))
    (V := loc W A) (X := flagged A) (R := flaggedReq Rq) (G := flaggedResp G)
    (ε₀ := ε) hε hint (fun n ω => hloc0 n ω)
    (fun n => measurableSet_flagged_req hAmeas hRq n)
    (fun n => measurableSet_flagged_resp hAmeas hG n)
    (fun n => by

      filter_upwards [condExp_loc_succ_le (K := K) (x := x)
        hAmeas hDbar hW hW0 hint n] with ω hω hnG
      obtain ⟨hs, hnGst⟩ := hresp_not hnG
      obtain ⟨hyD, hyU⟩ := hsurv_state hs
      rw [loc_of_survive hs]
      exact (hω hs (hR3 _ hyD hyU) (hWint _ hyD hyU hnGst)).trans
        (hWdrift _ hyD hyU hnGst))
    (fun n => by

      filter_upwards [condExp_loc_succ_le (K := K) (x := x)
        hAmeas hDbar hW hW0 hint n] with ω hω hnR hnG
      obtain ⟨hs, hnGst⟩ := hresp_not hnG
      obtain ⟨hyD, hyU⟩ := hsurv_state hs
      have hyR : ω n ∈ Rq := (flagged_mem_req_iff.1 hnR).2
      rw [loc_of_survive hs]
      exact (hω hs (hR3 _ hyD hyU) (hWint _ hyD hyU hnGst)).trans
        (hWdriftR _ hyD hyU hyR hnGst))

  filter_upwards [hK5c] with ω hω hconf hfreq
  have hsurvive : ∀ n, ω ∈ survive A n := by
    intro n k _
    rw [hAdef]
    rintro (hU' | hD')
    · exact (hconf k).2 hU'
    · exact hD' (hconf k).1
  have hfreq' : ∃ᶠ n in atTop, flagged A n ω ∈ flaggedReq Rq :=
    hfreq.mono fun n hn => flagged_mem_req_iff.2 ⟨hsurvive n, hn⟩
  exact (hω hfreq').mono fun n hn =>
    (flagged_mem_resp_iff.1 hn).resolve_left (not_not_intro (hsurvive n))

end Localized

section Bundle

variable {K : Kernel S S} [IsMarkovKernel K]
variable {D Dbar U : Set S} {V₀ : S → ℝ} {p thr : ℝ} {x : S}
variable {ι : Type*} [Countable ι]

/-- Soundness of the bundled Streett certificate. Given a fail-closed safety
battery (`V₀` with supermartingale drift on `D \ U`, floor `1` on the unsafe
set `U`, and `V₀ x ≤ thr` with `p + thr ≤ 1`) keeping paths confined to
`D \ U` with probability at least `p`, together with one localized Streett
certificate `(W i, ε i, C i)` per pair as in `streett_pair_localized`, the
path measure from `x` assigns probability at least `p` to the event that
**every** pair `i` (over a countable index type) satisfies its Streett
condition: infinitely many visits to `Rq i` imply infinitely many visits to
`G i`. -/
theorem sound_QStreettBundle {Rq G : ι → Set S} {W : ι → S → ℝ} {ε C : ι → ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y) (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → Integrable (W i) (K y))
    (hWdrift : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → ∫ z, W i z ∂K y ≤ W i y)
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∈ Rq i → y ∉ G i →
      ∫ z, W i z ∂K y ≤ W i y - ε i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ Rq i) → ∃ᶠ n in atTop, ω n ∈ G i} := by
  have hconf := sound_QSafetyBattery_failClosed hD hDbar hU hV₀ hΘ hDsub hR3 hR4
    hV₀int hV₀drift hV₀floor hV₀nonneg hx hthr
  have hpairs : ∀ᵐ ω ∂pathMeasure K x, ∀ i, (∀ n, ω n ∈ D \ U) →
      (∃ᶠ n in atTop, ω n ∈ Rq i) → ∃ᶠ n in atTop, ω n ∈ G i :=
    ae_all_iff.2 fun i => streett_pair_localized hD hDbar hU (hRq i) (hG i) (hW i)
      (hε i) hDsub hR3 (hW0 i) (hWC i) (hWint i) (hWdrift i) (hWdriftR i)
  refine hconf.trans (measure_mono_ae ?_)
  filter_upwards [hpairs] with ω hω hconfω
  exact fun i => hω i hconfω

/-- Degenerate Streett bundle: with the request set taken to be everything,
each certificate `W i` must strictly decrease in expectation at every confined
non-response state, and the conclusion strengthens to unconditional
recurrence — with probability at least `p`, every response set `G i` is
visited infinitely often. -/
theorem sound_StreettDegenerate {G : ι → Set S} {W : ι → S → ℝ} {ε C : ι → ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hG : ∀ i, MeasurableSet (G i)) (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y) (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → Integrable (W i) (K y))
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → ∫ z, W i z ∂K y ≤ W i y - ε i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∀ i, ∃ᶠ n in atTop, ω n ∈ G i} := by
  have hbundle := sound_QStreettBundle (Rq := fun _ => Set.univ) (G := G) (W := W)
    (ε := ε) (C := C) hD hDbar hU hV₀ (fun _ => MeasurableSet.univ) hG hW hΘ hDsub
    hR3 hR4 hV₀int hV₀drift hV₀floor hV₀nonneg hε hW0 hWC hWint
    (fun i y hyD hyU hyG => (hWdriftR i y hyD hyU hyG).trans
      (by linarith [(hε i).le]))
    (fun i y hyD hyU _ hyG => hWdriftR i y hyD hyU hyG) hx hthr
  refine hbundle.trans (measure_mono fun ω hω i => ?_)
  exact hω i ((Filter.Eventually.of_forall fun n => Set.mem_univ (ω n)).frequently)

omit [MeasurableSpace S] in

/-- Monotonicity of the Streett event in its data: enlarging the request set
and shrinking the response set strengthens the property, so a certified pair
`(Rqhat, Ghat)` discharges any pair `(Rq, G)` with `Rq ⊆ Rqhat` and
`Ghat ⊆ G`. -/
theorem streett_event_mono {Rq Rqhat G Ghat : Set S} (hR : Rq ⊆ Rqhat)
    (hG : Ghat ⊆ G) (ω : ℕ → S)
    (h : (∃ᶠ n in atTop, ω n ∈ Rqhat) → ∃ᶠ n in atTop, ω n ∈ Ghat) :
    (∃ᶠ n in atTop, ω n ∈ Rq) → ∃ᶠ n in atTop, ω n ∈ G :=
  fun hfreq => (h (hfreq.mono fun _ hn => hR hn)).mono fun _ hn => hG hn

/-- The Streett bundle transported to predicate form: if each request predicate
`reqSat i` implies membership in `Rq i` and each state of `G i` satisfies the
response predicate `respSat i`, then the probability bound of
`sound_QStreettBundle` applies verbatim to the predicate-level Streett event
(infinitely many `reqSat i` times imply infinitely many `respSat i` times). -/
theorem sound_QStreettBundle_tie {Rq G : ι → Set S} {W : ι → S → ℝ} {ε C : ι → ℝ}
    {reqSat respSat : ι → S → Prop}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hW : ∀ i, Measurable (W i))
    (hreq : ∀ i y, reqSat i y → y ∈ Rq i)
    (hresp : ∀ i, ∀ y ∈ G i, respSat i y)
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y) (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → Integrable (W i) (K y))
    (hWdrift : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → ∫ z, W i z ∂K y ≤ W i y)
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∈ Rq i → y ∉ G i →
      ∫ z, W i z ∂K y ≤ W i y - ε i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∀ i, (∃ᶠ n in atTop, reqSat i (ω n)) → ∃ᶠ n in atTop, respSat i (ω n)} := by
  refine (sound_QStreettBundle hD hDbar hU hV₀ hRq hG hW hΘ hDsub hR3 hR4 hV₀int
    hV₀drift hV₀floor hV₀nonneg hε hW0 hWC hWint hWdrift hWdriftR hx hthr).trans
    (measure_mono fun ω hω i hfreq => ?_)
  exact (hω i (hfreq.mono fun n hn => hreq i _ hn)).mono fun n hn => hresp i _ hn

omit [MeasurableSpace S] in

/-- A guard-collapse helper for ranking data: if `W` vanishes on a target set
`T` and `g` maps a slab into `T`, then applying `g` never increases a
nonnegative `W` on the slab. -/
theorem ranking_guard_collapse {W : S → ℝ} {T slab : Set S} {g : S → S}
    (hzero : ∀ y ∈ T, W y = 0) (himg : ∀ y ∈ slab, g y ∈ T) :
    ∀ y ∈ slab, 0 ≤ W y → W (g y) ≤ W y :=
  fun y hy h0 => (hzero _ (himg y hy)).le.trans h0

end Bundle

section Carved

variable {K : Kernel S S} [IsMarkovKernel K]

/-- The absorption side condition for the carved Streett rule: at every time
`k`, conditionally on the past, a path that has survived `A` through time `k`
and currently sits in the carve-out set `J` has probability at most `1 - γ` of
ever visiting the request set `Rq` strictly after time `k`. -/
def AbsorptionBound (K : Kernel S S) [IsMarkovKernel K] (x : S)
    (A J Rq : Set S) (γ : ℝ) : Prop :=
  ∀ k : ℕ, ∀ᵐ ω ∂pathMeasure K x, ω ∈ survive A k → ω k ∈ J →
    ((pathMeasure K x)[({ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}).indicator
        (fun _ => (1 : ℝ)) | Filtration.piLE (X := fun _ : ℕ => S) k]) ω ≤ 1 - γ

/-- Lévy upward argument for the absorption bound: almost surely, a path that
visits `J` (while surviving `A`) at infinitely many times cannot visit `Rq`
infinitely often — otherwise the conditional probabilities of the tail event
"`Rq` after now", which converge to its indicator by Lévy's upward theorem,
would be `1` in the limit yet infinitely often at most `1 - γ < 1`. -/
theorem ae_not_frequently_of_absorption {A J Rq : Set S} {γ : ℝ} {x : S}
    (hRq : MeasurableSet Rq) (hγ : 0 < γ)
    (habs : AbsorptionBound K x A J Rq γ) :
    ∀ᵐ ω ∂pathMeasure K x,
      (∃ᶠ k in atTop, ω ∈ survive A k ∧ ω k ∈ J) →
        ¬ ∃ᶠ n in atTop, ω n ∈ Rq := by
  set μ := pathMeasure K x
  set 𝓕 := Filtration.piLE (X := fun _ : ℕ => S) with h𝓕

  set E : Set (ℕ → S) := {ω | ∃ᶠ n in atTop, ω n ∈ Rq} with hE
  have hEeq : E = ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), (fun ω : ℕ → S => ω n) ⁻¹' Rq := by
    ext ω
    simp [hE, Filter.frequently_atTop]
  have hcoordSup : ∀ n : ℕ, MeasurableSet[⨆ n, 𝓕 n]
      ((fun ω : ℕ → S => ω n) ⁻¹' Rq) := fun n =>
    (le_iSup (fun n => 𝓕 n) n) _ ((measurable_coord_piLE le_rfl) hRq)
  have hEsup : MeasurableSet[⨆ n, 𝓕 n] E := by
    rw [hEeq]
    exact .iInter fun N => .iUnion fun n => .iUnion fun _ => hcoordSup n
  have hle : (⨆ n, 𝓕 n) ≤ MeasurableSpace.pi := iSup_le fun n => 𝓕.le n
  have hEmeas : MeasurableSet E := hle _ hEsup

  have hafter : ∀ k : ℕ, MeasurableSet {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq} := by
    intro k
    have h : {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}
        = ⋃ n, ⋃ (_ : k < n), (fun ω : ℕ → S => ω n) ⁻¹' Rq := by
      ext ω; simp
    rw [h]
    exact .iUnion fun n => .iUnion fun _ => (measurable_pi_apply n) hRq

  have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hEmeas
  have hlevy := hint.tendsto_ae_condExp
    (stronglyMeasurable_const.indicator hEsup)

  have hbound : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ survive A k → ω k ∈ J →
      (μ[E.indicator (fun _ => (1 : ℝ)) | 𝓕 k]) ω ≤ 1 - γ := by
    intro k
    have hmono : E.indicator (fun _ => (1 : ℝ))
        ≤ ({ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}).indicator (fun _ => (1 : ℝ)) := by
      intro ω
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω,
          Set.indicator_of_mem (show ω ∈ {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq} by
            obtain ⟨n, hn, hnR⟩ := Filter.frequently_atTop.1 hω (k + 1)
            exact ⟨n, Nat.lt_of_succ_le hn, hnR⟩)]
      · rw [Set.indicator_of_notMem hω]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hcondmono := condExp_mono (μ := μ) (m := 𝓕 k) hint
      ((integrable_const (1 : ℝ)).indicator (hafter k))
      (Filter.Eventually.of_forall hmono)
    filter_upwards [hcondmono, habs k] with ω h1 h2 hs hJ
    exact h1.trans (h2 hs hJ)

  filter_upwards [hlevy, ae_all_iff.2 hbound] with ω hlim hb hfreqJ
  intro hEω
  have hval : E.indicator (fun _ => (1 : ℝ)) ω = 1 := Set.indicator_of_mem hEω _
  have hlimval : E.indicator (fun _ => (1 : ℝ)) ω ∈ Set.Iic (1 - γ) := by
    refine isClosed_Iic.mem_of_frequently_of_tendsto ?_ hlim
    exact hfreqJ.mono fun k hk => Set.mem_Iic.2 (hb k hk.1 hk.2)
  rw [hval] at hlimval
  have h1γ : (1 : ℝ) ≤ 1 - γ := Set.mem_Iic.1 hlimval
  linarith

/-- The carved Streett bundle: each pair's drift and `ε`-decrease conditions
are only required off a carve-out set `J i`, and in exchange each `J i` must
satisfy `AbsorptionBound` with margin `γ i > 0`. The per-pair argument runs
`streett_pair_localized` with response set `G i ∪ J i`; frequent visits to
`J i` are then excluded on the frequent-request event by
`ae_not_frequently_of_absorption`, leaving frequent visits to `G i`. The
conclusion is the same probability-`p` bound on the conjunction of all Streett
conditions. -/
theorem sound_QStreettBundle_carved {D Dbar U : Set S} {V₀ : S → ℝ} {p thr : ℝ}
    {x : S} {ι : Type*} [Countable ι] {Rq G J : ι → Set S} {W : ι → S → ℝ}
    {ε C γ : ι → ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hJ : ∀ i, MeasurableSet (J i)) (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i) (hγ : ∀ i, 0 < γ i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y) (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → y ∉ J i → Integrable (W i) (K y))
    (hWdrift : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → y ∉ J i →
      ∫ z, W i z ∂K y ≤ W i y)
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∈ Rq i → y ∉ G i → y ∉ J i →
      ∫ z, W i z ∂K y ≤ W i y - ε i)
    (habs : ∀ i, AbsorptionBound K x (U ∪ Dᶜ) (J i) (Rq i) (γ i))
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ Rq i) → ∃ᶠ n in atTop, ω n ∈ G i} := by
  have hconf := sound_QSafetyBattery_failClosed hD hDbar hU hV₀ hΘ hDsub hR3 hR4
    hV₀int hV₀drift hV₀floor hV₀nonneg hx hthr

  have hpairs : ∀ᵐ ω ∂pathMeasure K x, ∀ i, (∀ n, ω n ∈ D \ U) →
      (∃ᶠ n in atTop, ω n ∈ Rq i) → ∃ᶠ n in atTop, ω n ∈ G i := by
    refine ae_all_iff.2 fun i => ?_
    have hK5c := streett_pair_localized (K := K) (x := x) hD hDbar hU (hRq i)
      ((hG i).union (hJ i)) (hW i) (hε i) hDsub hR3 (hW0 i) (hWC i)
      (fun y hyD hyU hyGJ => hWint i y hyD hyU
        (fun h => hyGJ (Or.inl h)) (fun h => hyGJ (Or.inr h)))
      (fun y hyD hyU hyGJ => hWdrift i y hyD hyU
        (fun h => hyGJ (Or.inl h)) (fun h => hyGJ (Or.inr h)))
      (fun y hyD hyU hyR hyGJ => hWdriftR i y hyD hyU hyR
        (fun h => hyGJ (Or.inl h)) (fun h => hyGJ (Or.inr h)))
    have hlevy := ae_not_frequently_of_absorption (K := K) (x := x)
      (A := U ∪ Dᶜ) (J := J i) (hRq i) (hγ i) (habs i)
    filter_upwards [hK5c, hlevy] with ω h1 h2 hconfω hfreq
    have hsurvive : ∀ n, ω ∈ survive (U ∪ Dᶜ) n := by
      intro n k _
      rintro (hU' | hD')
      · exact (hconfω k).2 hU'
      · exact hD' (hconfω k).1
    rcases Filter.frequently_or_distrib.1
        ((h1 hconfω hfreq).mono fun n hn => (Set.mem_union _ _ _).1 hn) with
      hGfreq | hJfreq
    · exact hGfreq
    · exact absurd hfreq (h2 (hJfreq.mono fun n hn => ⟨hsurvive n, hn⟩))
  refine hconf.trans (measure_mono_ae ?_)
  filter_upwards [hpairs] with ω hω hconfω
  exact fun i => hω i hconfω

end Carved

section AbsorptionDischarge

variable {K : Kernel S S} [IsMarkovKernel K]

@[reducible] def shift (k : ℕ) (ω : ℕ → S) : ℕ → S := fun n => ω (k + n)

lemma measurableSet_survive_shift_piLE {R : Set S} (hR : MeasurableSet R) (k n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) (k + n)]
      {ω : ℕ → S | shift k ω ∈ survive R n} := by
  have h : {ω : ℕ → S | shift k ω ∈ survive R n}
      = ⋂ j, ⋂ (_ : j ≤ n), (fun ω : ℕ → S => ω (k + j)) ⁻¹' Rᶜ := by
    ext ω; simp [mem_survive, shift]
  rw [h]
  exact .iInter fun j => .iInter fun hj =>
    (measurable_coord_piLE (Nat.add_le_add_left hj k)) hR.compl

lemma stronglyAdapted_stopped_shift {f : S → ℝ} {R : Set S} (hR : MeasurableSet R)
    (hf : Measurable f) (k : ℕ) :
    ∀ n, StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) (k + n)]
      (fun ω => stopped f R n (shift k ω)) := by
  intro n
  induction n with
  | zero => exact (hf.comp (measurable_coord_piLE le_rfl)).stronglyMeasurable
  | succ n ih =>
    have heq : (fun ω : ℕ → S => stopped f R (n + 1) (shift k ω))
        = ({ω : ℕ → S | shift k ω ∈ survive R n}).piecewise
            (fun ω => f (ω (k + (n + 1)))) (fun ω => stopped f R n (shift k ω)) := by
      funext ω
      by_cases h : shift k ω ∈ survive R n
      · rw [stopped_succ_of_survive h,
          Set.piecewise_eq_of_mem {ω : ℕ → S | shift k ω ∈ survive R n} _ _ h]
      · rw [stopped_succ_of_not_survive h,
          Set.piecewise_eq_of_notMem {ω : ℕ → S | shift k ω ∈ survive R n} _ _ h]
    rw [heq]
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.piecewise
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono (k + n).le_succ _
        (measurableSet_survive_shift_piLE hR k n))
      (hf.comp (measurable_coord_piLE le_rfl))
      ((ih.mono ((Filtration.piLE (X := fun _ : ℕ => S)).mono (k + n).le_succ)).measurable)

private lemma integrable_stopped_shift {f : S → ℝ} {R : Set S} {C : ℝ}
    (hR : MeasurableSet R) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (k : ℕ) (u : Π _i : Iic k, S) (n : ℕ) :
    Integrable (fun ω => stopped f R n (shift k ω))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u) := by
  refine (integrable_const C).mono'
    (((stronglyAdapted_stopped_shift hR hf k n).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).le (k + n))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (stopped_pred (fun r => 0 ≤ r) hf0 n (shift k ω))]
  exact stopped_pred (fun r => r ≤ C) hfC n (shift k ω)

private lemma integral_stopped_shift_succ_le {f : S → ℝ} {R : Set S}
    (hR : MeasurableSet R) (hf : Measurable f)
    (hdrift : ∀ y, y ∉ R → ∫ z, f z ∂K y ≤ f y) (k n : ℕ) (ω : ℕ → S) :
    ∫ y, stopped f R (n + 1) (shift k y)
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) (k + n)
          (Preorder.frestrictLe (k + n) ω)
      ≤ stopped f R n (shift k ω) := by
  have hmeas : AEStronglyMeasurable (fun y => stopped f R (n + 1) (shift k y))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) (k + n)
        (Preorder.frestrictLe (k + n) ω)) :=
    ((stronglyAdapted_stopped_shift hR hf k (n + 1)).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).le (k + (n + 1)))).aestronglyMeasurable
  rw [Kernel.integral_traj _ hmeas]

  have hagree : ∀ (y : ℕ → S) (j : ℕ), j ≤ n →
      shift k (updateFinset y (Iic (k + n)) (Preorder.frestrictLe (k + n) ω)) j
        = shift k ω j := fun y j hj => by
    show updateFinset y (Iic (k + n)) (Preorder.frestrictLe (k + n) ω) (k + j) = ω (k + j)
    rw [updateFinset_eq_of_le (Nat.add_le_add_left hj k)]; rfl
  by_cases hs : shift k ω ∈ survive R n
  ·
    have hpatch : ∀ y : ℕ → S,
        stopped f R (n + 1)
            (shift k (updateFinset y (Iic (k + n)) (Preorder.frestrictLe (k + n) ω)))
          = f (y (k + n + 1)) := fun y => by
      rw [stopped_succ_of_survive ((survive_congr (hagree y)).2 hs)]
      show f (updateFinset y (Iic (k + n)) (Preorder.frestrictLe (k + n) ω) (k + n + 1))
          = f (y (k + n + 1))
      rw [updateFinset_eq_succ]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpatch y)]
    have hstep : ∫ y : ℕ → S, f (y (k + n + 1))
        ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) (k + n)
          (Preorder.frestrictLe (k + n) ω)
        = ∫ z, f z ∂K (ω (k + n)) := by
      have hmapK := DFunLike.congr_fun
        (Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := mchain K) (a := k + n))
        (Preorder.frestrictLe (k + n) ω)
      rw [Kernel.map_apply _ (measurable_pi_apply _)] at hmapK
      have hcoord : (mchain K (k + n)) (Preorder.frestrictLe (k + n) ω) = K (ω (k + n)) := by
        rw [mchain_apply]; rfl
      rw [← hcoord, ← hmapK,
        integral_map_of_stronglyMeasurable (measurable_pi_apply _) hf.stronglyMeasurable]
    rw [hstep, stopped_of_survive hs]
    exact hdrift _ (hs n le_rfl)
  ·
    have hpatch : ∀ y : ℕ → S,
        stopped f R (n + 1)
            (shift k (updateFinset y (Iic (k + n)) (Preorder.frestrictLe (k + n) ω)))
          = stopped f R n (shift k ω) := fun y => by
      rw [stopped_succ_of_not_survive (fun h => hs ((survive_congr (hagree y)).1 h)),
        stopped_congr (hagree y)]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => hpatch y), integral_const]
    simp [measureReal_def]

def piLEShift (k : ℕ) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → S)) where
  seq n := Filtration.piLE (X := fun _ : ℕ => S) (k + n)
  mono' _ _ hmn := (Filtration.piLE (X := fun _ : ℕ => S)).mono (Nat.add_le_add_left hmn k)
  le' n := (Filtration.piLE (X := fun _ : ℕ => S)).le (k + n)

/-- A bounded nonnegative function `f` with supermartingale drift off `R`,
stopped at the first visit to `R` and evaluated along the path shifted by `k`
steps, is a supermartingale with respect to the shifted filtration
`piLEShift k` under the trajectory kernel started from any initial segment
`u` of length `k + 1`. This is the time-`k` restart of the base stopped
supermartingale, used to bound reach probabilities conditionally on the past. -/
theorem supermartingale_stopped_shift {f : S → ℝ} {R : Set S} {C : ℝ}
    (hR : MeasurableSet R) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hdrift : ∀ y, y ∉ R → ∫ z, f z ∂K y ≤ f y) (k : ℕ) (u : Π _i : Iic k, S) :
    Supermartingale (fun n ω => stopped f R n (shift k ω)) (piLEShift k)
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u) := by
  have hint : ∀ n, Integrable (fun ω => stopped f R n (shift k ω))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u) := fun n =>
    integrable_stopped_shift hR hf hf0 hfC k u n
  refine supermartingale_nat (𝒢 := piLEShift k)
    (fun n => stronglyAdapted_stopped_shift hR hf k n) hint (fun n => ?_)
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.le_add_right k n) (x₀ := u) (hint (n + 1))
  exact hcond.trans_le (Filter.Eventually.of_forall fun ω =>
    integral_stopped_shift_succ_le hR hf hdrift k n ω)

/-- Maximal (Ville-type) reach bound after time `k`: if `f` is bounded,
nonnegative, at least `1` on `R`, and has supermartingale drift off `R`, then
under the trajectory kernel from an initial segment `u` of length `k + 1` the
probability of ever visiting `R` at some time `n ≥ k` is at most
`ENNReal.ofReal (f (u k))` — the certificate value at the current state. -/
theorem measure_reach_after_le {f : S → ℝ} {R : Set S} {C : ℝ}
    (hR : MeasurableSet R) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ C)
    (hf1 : ∀ y ∈ R, 1 ≤ f y) (hdrift : ∀ y, y ∉ R → ∫ z, f z ∂K y ≤ f y)
    (k : ℕ) (u : Π _i : Iic k, S) :
    Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u {ω | ∃ n, k ≤ n ∧ ω n ∈ R}
      ≤ ENNReal.ofReal (f (u ⟨k, mem_Iic.2 le_rfl⟩)) := by
  have hbound := Qtsl.Ville.reach_avoid
    (X := fun n (ω : ℕ → S) => ω (k + n)) (B := R)
    (supermartingale_stopped_shift hR hf hf0 hfC hdrift k u)
    (fun n ω => stopped_pred (fun r => 0 ≤ r) hf0 n (shift k ω))
    (a := 1) (fun n ω hn => one_le_stopped hf1 n (shift k ω) ⟨n, le_rfl, hn⟩)
  rw [ENNReal.ofReal_one, one_mul] at hbound
  have hevent : {ω : ℕ → S | ∃ n, k ≤ n ∧ ω n ∈ R}
      = {ω : ℕ → S | ∃ n, ω (k + n) ∈ R} := by
    ext ω
    constructor
    · rintro ⟨n, hkn, hn⟩
      exact ⟨n - k, by rwa [Nat.add_sub_cancel' hkn]⟩
    · rintro ⟨n, hn⟩
      exact ⟨k + n, Nat.le_add_right k n, hn⟩
  rw [hevent]
  refine hbound.trans (le_of_eq (congrArg ENNReal.ofReal ?_))

  show (∫ ω, stopped f R 0 (shift k ω)
      ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u)
    = f (u ⟨k, mem_Iic.2 le_rfl⟩)
  have hmeas : AEStronglyMeasurable (fun ω : ℕ → S => stopped f R 0 (shift k ω))
      (Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k u) :=
    (hf.comp (measurable_pi_apply k)).aestronglyMeasurable
  rw [Kernel.integral_traj _ hmeas]
  have hval : ∀ y : ℕ → S,
      stopped f R 0 (shift k (updateFinset y (Iic k) u))
        = f (u ⟨k, mem_Iic.2 le_rfl⟩) := fun y => by
    show f (updateFinset y (Iic k) u k) = f (u ⟨k, mem_Iic.2 le_rfl⟩)
    rw [updateFinset_eq_of_le le_rfl]
  rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const]
  simp [measureReal_def]

/-- Discharge of the absorption side condition from kernel-level data: a
bounded nonnegative certificate `V` with floor `1` on the request set `Rq`,
supermartingale drift off `Rq`, and ceiling `1 - γ` on the carve-out set `J`
yields `AbsorptionBound K x A J Rq γ` — conditionally on any past ending in
`J`, the probability of ever visiting `Rq` again is at most `V ≤ 1 - γ`, by
`measure_reach_after_le`. -/
theorem absorptionBound_of_kernel {A J Rq : Set S} {V : S → ℝ} {C γ : ℝ} {x : S}
    (hRq : MeasurableSet Rq) (hV : Measurable V)
    (hV0 : ∀ y, 0 ≤ V y) (hVC : ∀ y, V y ≤ C)
    (hVfloor : ∀ y ∈ Rq, 1 ≤ V y)
    (hVdrift : ∀ y, y ∉ Rq → ∫ z, V z ∂K y ≤ V y)
    (hVJ : ∀ y ∈ J, V y ≤ 1 - γ) :
    AbsorptionBound K x A J Rq γ := by
  intro k
  have hafter : MeasurableSet {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq} := by
    have h : {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}
        = ⋃ n, ⋃ (_ : k < n), (fun ω : ℕ → S => ω n) ⁻¹' Rq := by
      ext ω; simp
    rw [h]
    exact .iUnion fun n => .iUnion fun _ => (measurable_pi_apply n) hRq
  have hint : Integrable
      (({ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}).indicator (fun _ => (1 : ℝ)))
      (pathMeasure K x) := (integrable_const (1 : ℝ)).indicator hafter
  have hcond := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := mchain K)
    (Nat.zero_le k) (x₀ := fun _ => x) hint
  filter_upwards [hcond] with ω hω _hs hJ
  have hreach : Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k
        (Preorder.frestrictLe k ω) {ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}
      ≤ ENNReal.ofReal (V (ω k)) := by
    refine (measure_mono (fun ω' => ?_)).trans
      (measure_reach_after_le hRq hV hV0 hVC hVfloor hVdrift k (Preorder.frestrictLe k ω))
    rintro ⟨n, hkn, hn⟩
    exact ⟨n, hkn.le, hn⟩
  have h1 : ∫ y, ({ω' : ℕ → S | ∃ n, k < n ∧ ω' n ∈ Rq}).indicator (fun _ => (1 : ℝ)) y
      ∂Kernel.traj (X := fun _ : ℕ => S) (κ := mchain K) k (Preorder.frestrictLe k ω)
      ≤ V (ω k) := by
    rw [integral_indicator_const (1 : ℝ) hafter, smul_eq_mul, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal (hV0 _) hreach
  exact (le_of_eq hω).trans (h1.trans (hVJ _ hJ))

/-- The fully discharged carved Streett bundle: the abstract `AbsorptionBound`
hypotheses of `sound_QStreettBundle_carved` are replaced by per-pair kernel
certificates `Va i` (bounded, nonnegative, floor `1` on `Rq i`,
supermartingale drift off `Rq i`, ceiling `1 - γ i` on `J i`), each converted
by `absorptionBound_of_kernel`. Every hypothesis is now a pointwise or
one-step-integral condition on the kernel, checkable certificate-side. -/
theorem sound_QStreettBundle_carved_discharged {D Dbar U : Set S} {V₀ : S → ℝ}
    {p thr : ℝ} {x : S} {ι : Type*} [Countable ι] {Rq G J : ι → Set S}
    {W Va : ι → S → ℝ} {ε C γ Ca : ι → ℝ}
    (hD : MeasurableSet D) (hDbar : MeasurableSet Dbar) (hU : MeasurableSet U)
    (hV₀ : Measurable V₀)
    (hRq : ∀ i, MeasurableSet (Rq i)) (hG : ∀ i, MeasurableSet (G i))
    (hJ : ∀ i, MeasurableSet (J i)) (hW : ∀ i, Measurable (W i))
    (hΘ : p + thr ≤ 1)
    (hDsub : D ⊆ Dbar)
    (hR3 : ∀ y ∈ D, y ∉ U → K y Dbar = 1)
    (hR4 : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1)
    (hV₀int : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y))
    (hV₀drift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y)
    (hV₀floor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y)
    (hV₀nonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y)
    (hε : ∀ i, 0 < ε i) (hγ : ∀ i, 0 < γ i)
    (hW0 : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y) (hWC : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i)
    (hWint : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → y ∉ J i → Integrable (W i) (K y))
    (hWdrift : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → y ∉ J i →
      ∫ z, W i z ∂K y ≤ W i y)
    (hWdriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∈ Rq i → y ∉ G i → y ∉ J i →
      ∫ z, W i z ∂K y ≤ W i y - ε i)
    (hVa : ∀ i, Measurable (Va i))
    (hVa0 : ∀ i y, 0 ≤ Va i y) (hVaC : ∀ i y, Va i y ≤ Ca i)
    (hVafloor : ∀ i, ∀ y ∈ Rq i, 1 ≤ Va i y)
    (hVadrift : ∀ i y, y ∉ Rq i → ∫ z, Va i z ∂K y ≤ Va i y)
    (hVaJ : ∀ i, ∀ y ∈ J i, Va i y ≤ 1 - γ i)
    (hx : x ∈ D) (hthr : V₀ x ≤ thr) :
    ENNReal.ofReal p ≤ pathMeasure K x
      {ω | ∀ i, (∃ᶠ n in atTop, ω n ∈ Rq i) → ∃ᶠ n in atTop, ω n ∈ G i} :=
  sound_QStreettBundle_carved hD hDbar hU hV₀ hRq hG hJ hW hΘ hDsub hR3 hR4
    hV₀int hV₀drift hV₀floor hV₀nonneg hε hγ hW0 hWC hWint hWdrift hWdriftR
    (fun i => absorptionBound_of_kernel (hRq i) (hVa i) (hVa0 i) (hVaC i)
      (hVafloor i) (hVadrift i) (hVaJ i))
    hx hthr

end AbsorptionDischarge

end Qtsl.QStreett
