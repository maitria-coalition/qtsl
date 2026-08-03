import QtslAux.QtslCompose.Presentation
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # Assume-guarantee composition

This module proves the core assume-guarantee composition theorems for a
`System n` of components wired acyclically (the `rank` function of the system
witnesses that every upstream dependency strictly decreases rank).

Each component `j` carries a conformance event `conform j` (its assumptions
hold) and a satisfaction event `sat j` (its guarantee holds); `conformExt` is
the environment's conformance event. The wiring hypothesis, used throughout,
says that external conformance together with the guarantees of all upstream
components entails component `j`'s conformance.

* `sat_of_conform`: pointwise soundness — if every component's contract
  `conform j → sat j` holds at an outcome `ω` in `conformExt`, then every
  guarantee holds at `ω`. Proved by strong induction on rank.
* `qualitative`: the almost-everywhere version, deriving an output
  specification from per-component almost-sure contracts.
* `fail_subset`: failure localization — an outcome in `conformExt` where some
  guarantee fails belongs to some component's `conform j ∩ (sat j)ᶜ` event
  (witnessed by a rank-minimal failing component).
* `fail_bound`, `fail_bound_out`: the resulting union bound — the probability
  that any guarantee (or the derived output specification) fails within
  `conformExt` is at most `∑ j, ε j`, given per-component bounds
  `μ (conform j ∩ (sat j)ᶜ) ≤ ε j`.
-/

open scoped ENNReal

open MeasureTheory

namespace Qtsl.QtslCompose

variable {n : ℕ} {Ω : Type*}

section Pointwise

variable (S : System n) (conformExt : Set Ω) (conform sat : Fin n → Set Ω)

/-- Pointwise assume-guarantee soundness. If the wiring condition `hw` holds
(external conformance plus all upstream guarantees entail each component's
conformance), and the outcome `ω` lies in the external conformance event and
satisfies every component's contract `conform j → sat j`, then every
component's guarantee holds at `ω`. The proof is strong induction on the
system's rank function. -/
theorem sat_of_conform
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ S.upstream j, sat i) ⊆ conform j)
    {ω : Ω} (h : ∀ j, ω ∈ conform j → ω ∈ sat j)
    (hext : ω ∈ conformExt) : ∀ j, ω ∈ sat j := by
  have key : ∀ N, ∀ j, S.rank j < N → ω ∈ sat j := by
    intro N
    induction N with
    | zero => exact fun j h0 => absurd h0 (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj
      have hup : ω ∈ ⋂ i ∈ S.upstream j, sat i := by
        refine Set.mem_iInter₂.2 fun i hi => ?_
        exact ih i (lt_of_lt_of_le (S.causality j i hi) (Nat.lt_succ_iff.1 hj))
      exact h j (hw j ⟨hext, hup⟩)
  exact fun j => key (S.rank j + 1) j (Nat.lt_succ_self _)

/-- Almost-everywhere assume-guarantee composition. If each component's
contract holds `μ`-almost everywhere and the joint satisfaction of all
guarantees (within external conformance) entails an output specification
`satOut`, then almost every outcome in the external conformance event
satisfies `satOut`. -/
theorem qualitative [MeasurableSpace Ω] {μ : Measure Ω}
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ S.upstream j, sat i) ⊆ conform j)
    (h : ∀ j, ∀ᵐ ω ∂μ, ω ∈ conform j → ω ∈ sat j)
    {satOut : Set Ω} (hout : conformExt ∩ (⋂ j, sat j) ⊆ satOut) :
    ∀ᵐ ω ∂μ, ω ∈ conformExt → ω ∈ satOut := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, ω ∈ conform j → ω ∈ sat j :=
    (MeasureTheory.ae_all_iff).2 h
  filter_upwards [hall] with ω hω hext
  exact hout ⟨hext,
    Set.mem_iInter.2 (sat_of_conform S conformExt conform sat hw hω hext)⟩

end Pointwise

section Failure

variable (S : System n) {conformExt : Set Ω} {conform sat : Fin n → Set Ω}

/-- Failure localization: an outcome in the external conformance event at
which some guarantee fails lies in `conform j ∩ (sat j)ᶜ` for some component
`j`. The witnessing component is one of minimal rank among those whose
guarantee fails: all of its upstream components still satisfy their
guarantees, so the wiring condition places it inside its own conformance
event. -/
theorem fail_subset
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ S.upstream j, sat i) ⊆ conform j) :
    conformExt ∩ (⋂ j, sat j)ᶜ ⊆ ⋃ j, conform j ∩ (sat j)ᶜ := by
  classical
  rintro ω ⟨hext, hn⟩
  have hex : ∃ j, ω ∉ sat j := by
    by_contra hno
    push_neg at hno
    exact hn (Set.mem_iInter.2 hno)
  obtain ⟨j₀, hj₀⟩ := hex
  have hne : (Finset.univ.filter fun j => ω ∉ sat j).Nonempty :=
    ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₀⟩⟩
  obtain ⟨jm, hjm, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun j => ω ∉ sat j) S.rank hne
  have hjmfail : ω ∉ sat jm := (Finset.mem_filter.1 hjm).2
  have hupstream : ω ∈ ⋂ i ∈ S.upstream jm, sat i := by
    refine Set.mem_iInter₂.2 fun i hi => ?_
    by_contra hifail
    have hiS : i ∈ Finset.univ.filter fun j => ω ∉ sat j :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hifail⟩
    exact absurd (S.causality jm i hi) (not_lt.2 (hmin i hiS))
  exact Set.mem_iUnion.2 ⟨jm, hw jm ⟨hext, hupstream⟩, hjmfail⟩

/-- Quantitative assume-guarantee composition (union bound): if each
component fails its contract with probability at most `ε j`, i.e.
`μ (conform j ∩ (sat j)ᶜ) ≤ ε j`, then the probability that some guarantee
fails within the external conformance event is at most `∑ j, ε j`. -/
theorem fail_bound [MeasurableSpace Ω] {μ : Measure Ω} {ε : Fin n → ℝ≥0∞}
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ S.upstream j, sat i) ⊆ conform j)
    (hε : ∀ j, μ (conform j ∩ (sat j)ᶜ) ≤ ε j) :
    μ (conformExt ∩ (⋂ j, sat j)ᶜ) ≤ ∑ j, ε j :=
  (measure_mono (fail_subset S hw)).trans
    (((measure_iUnion_le _).trans_eq (tsum_fintype _)).trans
      (Finset.sum_le_sum fun j _ => hε j))

/-- Variant of `fail_bound` for a derived output specification: if joint
satisfaction of all guarantees (within external conformance) entails
`satOut`, the probability that `satOut` fails within the external conformance
event is likewise at most `∑ j, ε j`. -/
theorem fail_bound_out [MeasurableSpace Ω] {μ : Measure Ω} {ε : Fin n → ℝ≥0∞}
    {satOut : Set Ω}
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ S.upstream j, sat i) ⊆ conform j)
    (hout : conformExt ∩ (⋂ j, sat j) ⊆ satOut)
    (hε : ∀ j, μ (conform j ∩ (sat j)ᶜ) ≤ ε j) :
    μ (conformExt ∩ satOutᶜ) ≤ ∑ j, ε j := by
  refine (measure_mono ?_).trans (fail_bound S hw hε)
  rintro ω ⟨hext, hnout⟩
  refine ⟨hext, fun hall => hnout (hout ⟨hext, hall⟩)⟩

end Failure

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.sat_of_conform
#print axioms Qtsl.QtslCompose.qualitative
#print axioms Qtsl.QtslCompose.fail_subset
#print axioms Qtsl.QtslCompose.fail_bound
#print axioms Qtsl.QtslCompose.fail_bound_out
