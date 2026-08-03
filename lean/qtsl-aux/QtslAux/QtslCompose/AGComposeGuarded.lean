import QtslAux.QtslCompose.Presentation
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # QWireComposeGuarded — the cyclic SAFETY composition rule (Rule B), event stratum

**Source spec**: the cyclic AG design (Rule B, design rounds r2→r4);
statements preregistered — committed before these proofs.

The ∀-face cyclic tier: a wired presentation admitting feedback, with the
dependency edges split into an **instantaneous** part — governed by the rank
function, exactly as in the acyclic rule — and a **guarded** part, where every
directed cycle must cross a guarded edge (delay medium with its initialization
row, or a Moore readout, at the profile tiers). The soundness engine is
McMillan's induction over time, run lexicographically with the rank induction:
prefix-indexed event families `conform sat : Fin n → ℕ → Set Ω`, wiring
squares reading instant deliveries at the current stage and guarded deliveries
at all earlier stages. The guarded intersection at `t = 0` is vacuous — that
vacuity IS the initialization row's face at this stratum: the square at the
base stage must hold on external conformance + instant deliveries alone.

## Width facts (found at proving time)

The r2 skeleton carried a prefix-monotonicity hypothesis
(`hsafety : s ≤ t → sat j t ⊆ sat j s`) on both theorems. Neither proof
consumes it: the guarded intersections are supplied directly by the outer
time induction (`sat_of_conform_guarded`) and by first-failure-stage
minimality (`fail_subset_guarded`). It is therefore NOT a hypothesis here —
prefix-monotonicity is what makes the event families a safety-face READING
(the r2 design's polarity condition, a sort premise at the rule level:
`γⱼ ForallSpec` on cycles), not what the event algebra needs. The same
narrowing as the binary width find: rule-level well-formedness, never a
soundness input.

## The battery (preregistered as M-G1/M-G2)

- `relay_refutes_unguarded` — the design's Role-1 countermodel: with the
  causality/guard kit deleted (cyclic instant wiring squares, no rank), the
  two-relay loop with guarantee "output is 0" refutes the premise-shaped
  safety rule (behaviour space collapsed to its constant-behaviour tag:
  `false` = the all-zeros behaviour, `true` = the all-ones conspiracy).
- `hw0_deleted_refuted` — the initialization face: wiring squares assumed
  only at `t > 0` (the `t = 0` face deleted) refute on a one-component
  guarded self-loop; the base case is load-bearing.

Everything here is event algebra (pure set theory + one measure-theoretic
union bound); nothing is checker-facing (cf. `lean-conventions.md`).
-/

open scoped ENNReal

open MeasureTheory

namespace Qtsl.QtslCompose

variable {n : ℕ} {Ω : Type*}

/-- A wired presentation admitting feedback: dependencies split into
instantaneous and guarded; the rank function witnesses acyclicity of the
INSTANT subgraph only. `System n` embeds as the `guarded = ∅` case
(`sat_of_conform_of_guardedFree`). -/
structure SystemG (n : ℕ) : Type where
  /-- instantaneous in-neighbours (rank-governed, as in the acyclic rule) -/
  instant : Fin n → Finset (Fin n)
  /-- guarded in-neighbours (delay media / Moore readouts at the profile
  tiers; every directed cycle crosses one of these) -/
  guarded : Fin n → Finset (Fin n)
  /-- causality rank for the instant subgraph -/
  rank : Fin n → ℕ
  /-- acyclicity of the INSTANT subgraph only — guarded edges are free -/
  causality : ∀ j, ∀ i ∈ instant j, rank i < rank j

section Pointwise

variable (S : SystemG n) (conformExt : Set Ω) (conform sat : Fin n → ℕ → Set Ω)

/-- **Cyclic conformance propagation** (the McMillan engine at the event
level; SAFETY variant, pointwise core). Wiring squares transport external
conformance + instant deliveries at the current stage + guarded deliveries at
all earlier stages into each component's conformance; components deliver on
conforming inputs; hence every component delivers at every stage. Strong
induction on the stage, then on the causality rank within it — the
`(stage, rank)`-lexicographic prefix induction the design prescribes. The
guarded intersection at `t = 0` is vacuous: the square's base-stage face is
the initialization row. -/
theorem sat_of_conform_guarded
    (hw : ∀ j t, conformExt
        ∩ (⋂ i ∈ S.instant j, sat i t)
        ∩ (⋂ i ∈ S.guarded j, ⋂ s < t, sat i s)
        ⊆ conform j t)
    {ω : Ω} (h : ∀ j t, ω ∈ conform j t → ω ∈ sat j t)
    (hext : ω ∈ conformExt) : ∀ j t, ω ∈ sat j t := by
  have key : ∀ t, (∀ s, s < t → ∀ j, ω ∈ sat j s) →
      ∀ N j, S.rank j < N → ω ∈ sat j t := by
    intro t ht N
    induction N with
    | zero => exact fun j h0 => absurd h0 (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj
      have hinst : ω ∈ ⋂ i ∈ S.instant j, sat i t :=
        Set.mem_iInter₂.2 fun i hi =>
          ih i (lt_of_lt_of_le (S.causality j i hi) (Nat.lt_succ_iff.1 hj))
      have hgrd : ω ∈ ⋂ i ∈ S.guarded j, ⋂ s < t, sat i s :=
        Set.mem_iInter₂.2 fun i _ =>
          Set.mem_iInter₂.2 fun s hs => ht s hs i
      exact h j t (hw j t ⟨⟨hext, hinst⟩, hgrd⟩)
  -- bounded induction over a stage ceiling (no strong-recursor name lottery;
  -- the r4 leg's banked idiom)
  have main : ∀ T, ∀ t, t ≤ T → ∀ j, ω ∈ sat j t := by
    intro T
    induction T with
    | zero =>
      intro t ht j
      have ht0 : t = 0 := Nat.le_zero.1 ht
      subst ht0
      exact key 0 (fun s hs => absurd hs (Nat.not_lt_zero s))
        (S.rank j + 1) j (Nat.lt_succ_self _)
    | succ T ih =>
      intro t ht j
      exact key t (fun s hs j' => ih s (by omega) j')
        (S.rank j + 1) j (Nat.lt_succ_self _)
  exact fun j t => main t t le_rfl j

end Pointwise

section Failure

variable (S : SystemG n) {conformExt : Set Ω} {conform sat : Fin n → ℕ → Set Ω}

/-- **Cyclic failure localization** (SAFETY variant; pure set algebra): within
external conformance, a failure of some guarantee at some stage localizes at
a component that failed *while conforming* — witnessed at the FIRST failing
stage, and there at a rank-minimal failing component (time-minimality first,
rank-minimality within the stage: the lexicographic order of the engine, run
backwards). -/
theorem fail_subset_guarded
    (hw : ∀ j t, conformExt
        ∩ (⋂ i ∈ S.instant j, sat i t)
        ∩ (⋂ i ∈ S.guarded j, ⋂ s < t, sat i s)
        ⊆ conform j t) :
    conformExt ∩ (⋂ j, ⋂ t, sat j t)ᶜ
      ⊆ ⋃ j, ⋃ t, conform j t ∩ (sat j t)ᶜ := by
  classical
  rintro ω ⟨hext, hn⟩
  have hex : ∃ t, ∃ j, ω ∉ sat j t := by
    by_contra hno
    push_neg at hno
    exact hn (Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun t => hno t j)
  have hbefore : ∀ s, s < Nat.find hex → ∀ j, ω ∈ sat j s := by
    intro s hs j
    by_contra hf
    exact Nat.find_min hex hs ⟨j, hf⟩
  obtain ⟨j₀, hj₀⟩ := Nat.find_spec hex
  have hne : (Finset.univ.filter fun j => ω ∉ sat j (Nat.find hex)).Nonempty :=
    ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₀⟩⟩
  obtain ⟨jm, hjm, hmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun j => ω ∉ sat j (Nat.find hex))
      S.rank hne
  have hjmfail : ω ∉ sat jm (Nat.find hex) := (Finset.mem_filter.1 hjm).2
  have hinst : ω ∈ ⋂ i ∈ S.instant jm, sat i (Nat.find hex) := by
    refine Set.mem_iInter₂.2 fun i hi => ?_
    by_contra hifail
    have hiS : i ∈ Finset.univ.filter fun j => ω ∉ sat j (Nat.find hex) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hifail⟩
    exact absurd (S.causality jm i hi) (not_lt.2 (hmin i hiS))
  have hgrd : ω ∈ ⋂ i ∈ S.guarded jm, ⋂ s < Nat.find hex, sat i s :=
    Set.mem_iInter₂.2 fun i _ =>
      Set.mem_iInter₂.2 fun s hs => hbefore s hs i
  exact Set.mem_iUnion.2 ⟨jm, Set.mem_iUnion.2
    ⟨Nat.find hex, hw jm (Nat.find hex) ⟨⟨hext, hinst⟩, hgrd⟩, hjmfail⟩⟩

/-- **QWireComposeGuarded, probabilistic form**: the union bound survives
cyclicity — per-component failure budgets over all stages compose additively
(first-failure localization keeps every component's budget chargeable to its
own conforming-failure event). -/
theorem fail_bound_guarded [MeasurableSpace Ω] {μ : Measure Ω}
    {ε : Fin n → ℝ≥0∞}
    (hw : ∀ j t, conformExt
        ∩ (⋂ i ∈ S.instant j, sat i t)
        ∩ (⋂ i ∈ S.guarded j, ⋂ s < t, sat i s)
        ⊆ conform j t)
    (hε : ∀ j, μ (⋃ t, conform j t ∩ (sat j t)ᶜ) ≤ ε j) :
    μ (conformExt ∩ (⋂ j, ⋂ t, sat j t)ᶜ) ≤ ∑ j, ε j :=
  (measure_mono (fail_subset_guarded S hw)).trans
    (((measure_iUnion_le _).trans_eq (tsum_fintype _)).trans
      (Finset.sum_le_sum fun j _ => hε j))

end Failure

section Recovery

/-- **The acyclic recovery**: `System n` embeds as the `guarded = ∅` case
with stage-constant event families — `sat_of_conform`'s statement is
reproduced from the guarded engine on the nose. -/
theorem sat_of_conform_of_guardedFree (Sys : System n) (conformExt : Set Ω)
    (conform sat : Fin n → Set Ω)
    (hw : ∀ j, conformExt ∩ (⋂ i ∈ Sys.upstream j, sat i) ⊆ conform j)
    {ω : Ω} (h : ∀ j, ω ∈ conform j → ω ∈ sat j) (hext : ω ∈ conformExt) :
    ∀ j, ω ∈ sat j := by
  intro j
  refine sat_of_conform_guarded
    ⟨Sys.upstream, fun _ => ∅, Sys.rank, Sys.causality⟩ conformExt
    (fun j _ => conform j) (fun j _ => sat j)
    (fun j t => ?_) (fun j t => h j) hext j 0
  intro ω' hω'
  exact hw j ⟨hω'.1.1, hω'.1.2⟩

end Recovery

/-! ## The battery (preregistered as M-G1/M-G2) -/

section Battery

/-- **M-G1 (the well-foundedness kit deleted): the premise-shaped cyclic
safety rule is UNSOUND without it** — the design's Role-1 two-relay
loop. Behaviour space collapsed to the constant-behaviour tag
(`Ω' = Bool`: `false` = all-zeros, `true` = all-ones); guarantees "output is
0" read as `sat j = {false}`; the cyclic wiring squares
(`upstream = ![{1}, {0}]`, no rank condition) hold, every component delivers
on conforming inputs, external conformance is total — and the all-ones
conspiracy `ω = true` refutes the conclusion. The acyclic rule cannot even
express this instance (its causality certificate makes the two-cycle
unrepresentable); the guarded rule prices it correctly (a guard + its
initialization row would collapse the loop to all-zeros). -/
theorem relay_refutes_unguarded :
    ¬ (∀ (Ω' : Type) (upstream : Fin 2 → Finset (Fin 2))
        (conformExt : Set Ω') (conform sat : Fin 2 → Set Ω'),
        (∀ j, conformExt ∩ (⋂ i ∈ upstream j, sat i) ⊆ conform j) →
        ∀ ω, (∀ j, ω ∈ conform j → ω ∈ sat j) → ω ∈ conformExt →
        ∀ j, ω ∈ sat j) := by
  intro hrule
  have h := hrule Bool ![{1}, {0}] Set.univ
    (fun _ => {b | b = false}) (fun _ => {b | b = false})
    (fun j => by
      rintro b ⟨-, hb⟩
      have h1 : (1 - j : Fin 2) ∈ (![{1}, {0}] : Fin 2 → Finset (Fin 2)) j := by
        fin_cases j <;> decide
      exact Set.mem_iInter₂.1 hb _ h1)
    true (fun j hb => hb) (Set.mem_univ _) 0
  simpa using h

/-- **M-G2 (the initialization face deleted): wiring squares assumed only at
`t > 0` are UNSOUND** — a one-component guarded self-loop whose guarantee
fails already at stage 0: with the base-stage square gone, the guarded
intersection `⋂ s < t, sat s` is empty at every `t > 0` (stage 0 already
failed), so the `t > 0` squares hold vacuously, every delivery implication
holds vacuously, and the conclusion still demands stage-0 delivery. The
`t = 0` square — the initialization row's face — is exactly what refuses
this instance. -/
theorem hw0_deleted_refuted :
    ¬ (∀ (Ω' : Type) (S : SystemG 1) (conformExt : Set Ω')
        (conform sat : Fin 1 → ℕ → Set Ω'),
        (∀ j t, 0 < t → conformExt
            ∩ (⋂ i ∈ S.instant j, sat i t)
            ∩ (⋂ i ∈ S.guarded j, ⋂ s < t, sat i s)
            ⊆ conform j t) →
        ∀ ω, (∀ j t, ω ∈ conform j t → ω ∈ sat j t) → ω ∈ conformExt →
        ∀ j t, ω ∈ sat j t) := by
  intro hrule
  have h := hrule Unit
    ⟨fun _ => ∅, fun _ => {0}, fun _ => 0,
      fun j i hi => absurd hi (Finset.notMem_empty i)⟩
    Set.univ (fun _ _ => ∅) (fun _ _ => ∅)
    (fun j t ht => by
      rintro ω ⟨⟨-, -⟩, hg⟩
      have h0 : (0 : Fin 1) ∈ ({0} : Finset (Fin 1)) := Finset.mem_singleton_self _
      have := Set.mem_iInter₂.1 (Set.mem_iInter₂.1 hg 0 h0) 0 ht
      exact this)
    () (fun j t hc => absurd hc (Set.notMem_empty _)) (Set.mem_univ _) 0 0
  exact Set.notMem_empty _ h

end Battery

end Qtsl.QtslCompose

/-! ## Axiom receipts -/

#print axioms Qtsl.QtslCompose.sat_of_conform_guarded
#print axioms Qtsl.QtslCompose.fail_subset_guarded
#print axioms Qtsl.QtslCompose.fail_bound_guarded
#print axioms Qtsl.QtslCompose.sat_of_conform_of_guardedFree
#print axioms Qtsl.QtslCompose.relay_refutes_unguarded
#print axioms Qtsl.QtslCompose.hw0_deleted_refuted
