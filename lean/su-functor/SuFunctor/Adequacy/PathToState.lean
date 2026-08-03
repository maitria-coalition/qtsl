import SuFunctor.Adequacy.SpecBehavioral
import SuFunctor.Universe.FellTopology

/-! # Path-to-state re-anchoring: rooted regions, and the recursion that closes

Branching-time logics form *state* predicates from *path* judgments —
`A ψ`, `E ψ`, `P_{≥p}[ψ]` read at a state — by re-anchoring the path
object at each root.  This module records the two kernel-checked facts
that locate how far the semantic universe supports that move, one per
tier.

* **At the behavioral tier the nesting recursion closes.**  The rooted
  region `probThresholdSet K p E = {x | p ≤ pathMeasure K x E}` of a
  measurable path event is itself measurable
  (`measurableSet_probThresholdSet`): the rooted path law is a kernel
  read at the constant-history injection, so its evaluation on a fixed
  measurable event is a measurable function of the root
  (`measurable_pathMeasure_apply`).  Consequently a threshold region
  can feed back into path events as a region atom — the second-level
  event reading the region at a tick is again measurable
  (`measurableSet_atTick_probThresholdSet`) — and the doubly-nested
  region is again a region (`measurableSet_probThresholdSet_nested`).
  Iterating the same two lemmas closes every finite nesting depth:
  nothing in the measurable structure obstructs branching-time nesting
  for precise Markov-kernel profiles.

* **At the record-carrier tier, rooting is a closed condition.**  The
  records through a fixed ambient point form a Fell-closed class
  (`isClosed_through`): rootedness is hitting a compact singleton, so
  conditioning a belief state on rootedness is conjunction with the
  wall of a closed record class — the rooted family stays inside the
  universe pointwise in the root.  The regularity of the family *in*
  the root has a closed graph (`isClosed_mem_graph`, over a locally
  compact ambient: the miss face supplies a compact separator) — the
  outer-semicontinuity half of the hemicontinuity dictionary that the
  window-carrier module records as deliberately not formalized; the
  lower half, and the per-face semicontinuity of rooted envelopes, are
  the genuine open side conditions and are *not* claimed here.

Axiom receipts at the bottom; expected closure ⊆ [propext,
Classical.choice, Quot.sound], zero sorryAx. -/

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace SuFunctor.Universe

open Qtsl.Battery

section Behavioral

variable {S : Type*} [MeasurableSpace S]
variable (K : Kernel S S) [IsMarkovKernel K]

/-- Evaluation of the rooted path law on a fixed measurable event is a
measurable function of the root: the trajectory law is a kernel, read
at the (measurable) constant-history injection. -/
theorem measurable_pathMeasure_apply {E : Set (ℕ → S)}
    (hE : MeasurableSet E) :
    Measurable fun x => pathMeasure K x E := by
  unfold pathMeasure
  exact (Kernel.measurable_coe _ hE).comp
    (measurable_pi_lambda _ fun _ => measurable_id)

/-- **The rooted region of a measurable path event is measurable.**
The state-formula reading of the probability-threshold former is a
citizen of the behavioral tier's measurable structure. -/
theorem measurableSet_probThresholdSet {E : Set (ℕ → S)}
    (hE : MeasurableSet E) (p : ℝ) :
    MeasurableSet (probThresholdSet K p E) :=
  measurableSet_le measurable_const (measurable_pathMeasure_apply K hE)

/-- The second-level event: at tick `n` the path sits inside the
rooted region of `(p, E)`.  Measurable because the region is. -/
theorem measurableSet_atTick_probThresholdSet {E : Set (ℕ → S)}
    (hE : MeasurableSet E) (p : ℝ) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | ω n ∈ probThresholdSet K p E} :=
  measurable_pi_apply n (measurableSet_probThresholdSet K hE p)

/-- **Branching-time nesting closes at the behavioral tier**: the
doubly-nested threshold region — the roots from which, with
probability at least `q`, the tick-`n` state lies inside the
`(p, E)`-rooted region — is again a measurable region, by the same
two lemmas.  Iterating closes every finite nesting depth. -/
theorem measurableSet_probThresholdSet_nested {E : Set (ℕ → S)}
    (hE : MeasurableSet E) (p q : ℝ) (n : ℕ) :
    MeasurableSet (probThresholdSet K q
      {ω : ℕ → S | ω n ∈ probThresholdSet K p E}) :=
  measurableSet_probThresholdSet K
    (measurableSet_atTick_probThresholdSet K hE p n) q

end Behavioral

section RecordCarrier

variable {α : Type*} [TopologicalSpace α]

/-- **Rootedness is Fell-closed**: the class of closed sets through a
fixed ambient point is closed in the Fell hyperspace — hitting a
compact singleton.  Conditioning on the root is therefore conjunction
with the wall of a closed record class, pointwise in the root. -/
theorem isClosed_through (y : α) :
    IsClosed {F : FellCloseds α | y ∈ (F : Set α)} := by
  have h : {F : FellCloseds α | y ∈ (F : Set α)}
      = {F : FellCloseds α | ((F : Set α) ∩ {y}).Nonempty} := by
    ext F
    simp [Set.inter_singleton_nonempty]
  rw [h]
  exact FellCloseds.isClosed_inter_nonempty_of_isCompact isCompact_singleton

/-- **The rooted family has a closed graph**: the membership relation
between ambient points and closed sets is closed over a locally
compact ambient.  Local compactness feeds the miss face a compact
separator around any non-member.  This is the outer-semicontinuity
half of the root-regularity dictionary. -/
theorem isClosed_mem_graph [LocallyCompactSpace α] :
    IsClosed {p : α × FellCloseds α | p.1 ∈ (p.2 : Set α)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨y, F⟩ (hyF : y ∉ (F : Set α))
  obtain ⟨K, hKmem, hKsub, hKcpt⟩ :=
    local_compact_nhds (F.isClosed.isOpen_compl.mem_nhds hyF)
  rw [nhds_prod_eq]
  refine Filter.mem_of_superset
    (Filter.prod_mem_prod hKmem
      ((FellCloseds.isOpen_disjoint_of_isCompact hKcpt).mem_nhds ?_)) ?_
  · exact Set.disjoint_left.mpr fun a haF haK => hKsub haK haF
  · rintro ⟨y', F'⟩ ⟨hy', hF'⟩
    exact fun hmem => Set.disjoint_left.mp hF' hmem hy'

end RecordCarrier

end SuFunctor.Universe

#print axioms SuFunctor.Universe.measurable_pathMeasure_apply
#print axioms SuFunctor.Universe.measurableSet_probThresholdSet
#print axioms SuFunctor.Universe.measurableSet_probThresholdSet_nested
#print axioms SuFunctor.Universe.isClosed_through
#print axioms SuFunctor.Universe.isClosed_mem_graph
