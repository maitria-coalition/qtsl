import SuFunctor.Universe.FellRecordLocus
import Mathlib.Topology.Semicontinuity.Defs

/-! # The interior-pair record locus: closedness at general causal supports

Over a general causal support the record class does **not** bundle per
timeline: two-point specimens over the Minkowski cone order refute
Fell-closedness of the chain-quantified record class (the companion
witness module `FellPairWitness` carries them).  The closed object is
the **interior-pair locus**: speed bounds demanded over pairs of stages
in the *interior* of the comparability relation — on a bicontinuous
site, exactly the chronological pairs — against a two-stage duration.
Closedness consumes precisely two site hypotheses:

* **(S1) chronology is open** — the constraining relation
  `Chron ⊆ T × T` is open in the stage topology;
* **(S2) pair-duration is upper semicontinuous on chronological
  pairs** — `δ₂` is `UpperSemicontinuousOn` the set of `Chron` pairs.

The development is a **one-parameter generalization of the landed
speed-graph stratum** (`FellRecordLocus`): the cone condition's defect
`(univ, dist)` — every pair constrained, against the timeline
pseudo-metric — generalizes to `(Chron, δ₂)`, and the defect-openness
step (`isOpen_lt` over a continuous defect) generalizes to the
`{f < g}`-open lemma for `f` upper semicontinuous on an open relation
and `g` continuous (`isOpen_pairViolation`).  Everything else is
consumed unchanged:

* **closedness** (`isClosed_pairLocus`) is the same pure hit-face
  margin argument — a violating pair persists on a product-open
  rectangle, two hit demands through the rectangle's sides avoid the
  locus; no compactness of anything, and the stage space needs only a
  topology (the pseudo-metric of the landed statement was the
  classical instantiation, not structure);
* **compactness comes free** (`isCompact_pairLocus`), the hyperspace
  being compact over every ambient;
* **locality** (`isPairGraph_iff_forall_clip`) consumes directedness
  exactly once — a violating pair's two points are collected into a
  single cover member — and the `IsLocalLocus` subsheaf package
  (closed subsheaf, glue, descent homeomorphism) instantiates verbatim
  (`pairLocus_isLocalLocus`, `glue_mem_pairLocus`,
  `pairLocusHomeomorph`): clips leave `Chron` and `δ₂` untouched
  because both live on the stage space, and subwindow inclusions
  respect them;
* **the degeneracy check** (`pairLocus_trivial_eq_speedLocus`,
  `isClosed_speedLocus_via_pairLocus`): at `Chron := ⊤` and
  `δ₂ := dist` the locus *is* the landed `speedLocus` and the two site
  hypotheses discharge by `isOpen_univ` and continuity, recovering
  `isClosed_speedLocus` exactly — the generalization is conservative
  over the classical column.

The two hypotheses are load-bearing, not artifacts of the proof: the
witness module refutes closedness when `Chron` is the (non-open) causal
order itself — a spacelike stage-pair Fell-converging onto a null pair
awakens a zero-duration constraint no approximant felt, and a merging
spacelike pair defeats single-valuedness through the equal-stage face —
and when `δ₂` fails upper semicontinuity with `Chron` still open.
Boundary-of-comparability conditions (null pairs, equal stages) are
deliberately *not* constrained here; they ride certified strata in the
manner of the Zeno pattern, not the topology.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter
open scoped NNReal

/-! ## The per-pair condition -/

section PairGraph

variable {β T E : Type*} [PseudoMetricSpace E]

/-- The **interior-pair condition**: every two members of `A` whose
stages are related by `Chron` have states within `c` times the
two-stage duration `δ₂` of their stages.  `τ` charts the stage space,
`σ` the state space, as in the landed cone condition; `Chron` is the
constraining stage relation (chronology, on a causal site — the
*interior* of comparability, never comparability itself) and `δ₂` the
two-stage duration.  At `Chron := ⊤`, `δ₂ := dist` this is literally
`IsSpeedGraph` (`isPairGraph_trivial_iff`).  Pairwise, hence
hereditary; reflexive `Chron` pairs subsume single-valuedness whenever
`δ₂` vanishes on them. -/
def IsPairGraph (τ : β → T) (σ : β → E) (c : ℝ≥0)
    (Chron : T → T → Prop) (δ₂ : T → T → ℝ) (A : Set β) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, Chron (τ p) (τ q) →
    dist (σ p) (σ q) ≤ (c : ℝ) * δ₂ (τ p) (τ q)

variable {τ : β → T} {σ : β → E} {c : ℝ≥0} {Chron : T → T → Prop}
  {δ₂ : T → T → ℝ}

/-- The interior-pair condition is hereditary: subsets of pair graphs
are pair graphs. -/
theorem IsPairGraph.mono {A B : Set β} (hAB : A ⊆ B)
    (h : IsPairGraph τ σ c Chron δ₂ B) : IsPairGraph τ σ c Chron δ₂ A :=
  fun p hp q hq => h p (hAB hp) q (hAB hq)

/-- The empty record satisfies the interior-pair condition: total
escape is citizenship. -/
theorem isPairGraph_empty : IsPairGraph τ σ c Chron δ₂ (∅ : Set β) :=
  fun p hp => absurd hp (notMem_empty p)

/-- A single stage satisfies the interior-pair condition, under the
honest side condition on the reflexive pair: the scaled duration of a
`Chron`-reflexive stage must be nonnegative.  Free for irreflexive
chronologies (`isPairGraph_singleton_of_irrefl`) and for the
degenerate `(⊤, dist)` instantiation; not free for arbitrary signed
`δ₂`. -/
theorem isPairGraph_singleton {x : β}
    (hx : Chron (τ x) (τ x) → 0 ≤ (c : ℝ) * δ₂ (τ x) (τ x)) :
    IsPairGraph τ σ c Chron δ₂ {x} := by
  intro p hp q hq
  rw [mem_singleton_iff] at hp hq
  subst hp
  subst hq
  intro hc
  simpa using hx hc

/-- For an irreflexive chronology — every strict-cone chronology, the
classical `<` — singleton citizenship is unconditional. -/
theorem isPairGraph_singleton_of_irrefl (hirr : ∀ t, ¬ Chron t t)
    (x : β) : IsPairGraph τ σ c Chron δ₂ {x} :=
  isPairGraph_singleton fun hc => absurd hc (hirr _)

variable [TopologicalSpace β]

variable (τ σ c Chron δ₂) in
/-- The **interior-pair record locus**: the closed sets satisfying the
interior-pair condition, as a class of the Fell hyperspace. -/
def pairLocus : Set (FellCloseds β) :=
  {G | IsPairGraph τ σ c Chron δ₂ (G : Set β)}

@[simp]
theorem mem_pairLocus {G : FellCloseds β} :
    G ∈ pairLocus τ σ c Chron δ₂
      ↔ IsPairGraph τ σ c Chron δ₂ (G : Set β) := Iff.rfl

/-- The empty record is a citizen of the interior-pair locus. -/
theorem bot_mem_pairLocus : (⊥ : FellCloseds β) ∈ pairLocus τ σ c Chron δ₂ := by
  rw [mem_pairLocus, FellCloseds.coe_bot]
  exact isPairGraph_empty

/-! ### The violation set is open: `{USC < LSC}` over an open relation -/

section Closedness

variable [TopologicalSpace T]

/-- Scaling an upper semicontinuous function by a nonnegative constant
preserves upper semicontinuity (real-valued, on a set). -/
theorem upperSemicontinuousOn_const_mul {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} (hf : UpperSemicontinuousOn f s) {a : ℝ}
    (ha : 0 ≤ a) : UpperSemicontinuousOn (fun x => a * f x) s := by
  rcases ha.eq_or_lt with rfl | ha'
  · have heq : (fun x => (0 : ℝ) * f x) = fun _ => (0 : ℝ) := by
      funext x
      ring
    rw [heq]
    intro x _ y hy
    exact Eventually.of_forall fun _ => hy
  · intro x hx y hy
    have hfx : f x < y / a := (lt_div_iff₀' ha').mpr hy
    filter_upwards [hf x hx _ hfx] with z hz
    exact (lt_div_iff₀' ha').mp hz

/-- **The violation set is open**: pairs of the ambient whose stages
are chronologically related and whose states exceed the scaled
duration form an open set of `β × β`.  This is the defect-openness
step of the closedness theorem, generalized from `isOpen_lt` over a
continuous defect to the `{f < g}`-open pattern for `f` upper
semicontinuous on an open relation and `g` continuous: the relation's
openness converts the within-filter of (S2) into a full neighborhood
filter, and a margin `m` strictly between the scaled duration and the
state distance persists on the intersection of the three demands. -/
theorem isOpen_pairViolation (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) (hChron : IsOpen {r : T × T | Chron r.1 r.2})
    (hδ : UpperSemicontinuousOn (fun r : T × T => δ₂ r.1 r.2)
      {r : T × T | Chron r.1 r.2}) :
    IsOpen {r : β × β | Chron (τ r.1) (τ r.2) ∧
      (c : ℝ) * δ₂ (τ r.1) (τ r.2) < dist (σ r.1) (σ r.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨p, q⟩ ⟨hc, hv⟩
  have hττ : Continuous fun r : β × β => ((τ r.1, τ r.2) : T × T) :=
    (hτ.comp continuous_fst).prodMk (hτ.comp continuous_snd)
  have hg : UpperSemicontinuousOn
      (fun r : T × T => (c : ℝ) * δ₂ r.1 r.2) {r : T × T | Chron r.1 r.2} :=
    upperSemicontinuousOn_const_mul hδ c.coe_nonneg
  obtain ⟨m, hm₁, hm₂⟩ := exists_between hv
  have hmemS : ((τ p, τ q) : T × T) ∈ {r : T × T | Chron r.1 r.2} := hc
  have hev₁ : ∀ᶠ rt : T × T in 𝓝 (τ p, τ q),
      (c : ℝ) * δ₂ rt.1 rt.2 < m := by
    have h := hg _ hmemS m hm₁
    rwa [hChron.nhdsWithin_eq hmemS] at h
  have hev₂ : ∀ᶠ rt : T × T in 𝓝 (τ p, τ q), Chron rt.1 rt.2 :=
    hChron.eventually_mem hmemS
  have hdist : Continuous fun r : β × β => dist (σ r.1) (σ r.2) :=
    (hσ.comp continuous_fst).dist (hσ.comp continuous_snd)
  have hev₃ : ∀ᶠ r : β × β in 𝓝 (p, q), m < dist (σ r.1) (σ r.2) :=
    (isOpen_lt continuous_const hdist).eventually_mem hm₂
  filter_upwards [(hττ.tendsto (p, q)).eventually hev₁,
    (hττ.tendsto (p, q)).eventually hev₂, hev₃] with r h₁ h₂ h₃
  exact ⟨h₂, h₁.trans h₃⟩

/-! ### Closedness: the hit-face margin argument, generalized -/

/-- **The interior-pair locus is closed** — the general-support
replacement for the per-timeline bundle form, consuming exactly the
two site hypotheses (S1) `Chron` open and (S2) `δ₂` upper
semicontinuous on it.  The proof is the landed hit-face margin
argument verbatim: a violating pair persists on a product-open
rectangle around it (`isOpen_pairViolation` supplying what continuity
of the defect supplied classically), and the two hit demands through
the rectangle's sides are a Fell neighborhood avoiding the locus.  No
compactness — of the ambient, the graphs, or the demands —
anywhere. -/
theorem isClosed_pairLocus (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) (hChron : IsOpen {r : T × T | Chron r.1 r.2})
    (hδ : UpperSemicontinuousOn (fun r : T × T => δ₂ r.1 r.2)
      {r : T × T | Chron r.1 r.2}) :
    IsClosed (pairLocus τ σ c Chron δ₂) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro G hG
  obtain ⟨p, hpG, q, hqG, hchron, hviol⟩ :
      ∃ p ∈ (G : Set β), ∃ q ∈ (G : Set β), Chron (τ p) (τ q) ∧
        (c : ℝ) * δ₂ (τ p) (τ q) < dist (σ p) (σ q) := by
    simpa [pairLocus, IsPairGraph, not_forall, Classical.not_imp,
      not_le] using hG
  obtain ⟨Vp, Vq, hVp, hVq, hpVp, hqVq, hsub⟩ :=
    isOpen_prod_iff.mp (isOpen_pairViolation hτ hσ c hChron hδ) p q
      ⟨hchron, hviol⟩
  refine ⟨{H : FellCloseds β | ((H : Set β) ∩ Vp).Nonempty}
      ∩ {H : FellCloseds β | ((H : Set β) ∩ Vq).Nonempty},
    ?_, ?_, ⟨p, hpG, hpVp⟩, ⟨q, hqG, hqVq⟩⟩
  · -- every member of the double hit demand carries a violating pair
    rintro H ⟨⟨p', hp'H, hp'V⟩, ⟨q', hq'H, hq'V⟩⟩ hHmem
    have hviol' := hsub (mk_mem_prod hp'V hq'V)
    exact absurd (hHmem p' hp'H q' hq'H hviol'.1) (not_le.mpr hviol'.2)
  · exact (FellCloseds.isOpen_inter_nonempty_of_isOpen hVp).inter
      (FellCloseds.isOpen_inter_nonempty_of_isOpen hVq)

/-- **Compactness comes free** for the interior-pair locus: closed in
the hypothesis-free-compact hyperspace. -/
theorem isCompact_pairLocus (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) (hChron : IsOpen {r : T × T | Chron r.1 r.2})
    (hδ : UpperSemicontinuousOn (fun r : T × T => δ₂ r.1 r.2)
      {r : T × T | Chron r.1 r.2}) :
    IsCompact (pairLocus τ σ c Chron δ₂) :=
  (isClosed_pairLocus hτ hσ c hChron hδ).isCompact

/-- The interior-pair locus is locally closed: a citizen of the
composition tier's fibre class, as at the classical stratum. -/
theorem isLocallyClosed_pairLocus (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) (hChron : IsOpen {r : T × T | Chron r.1 r.2})
    (hδ : UpperSemicontinuousOn (fun r : T × T => δ₂ r.1 r.2)
      {r : T × T | Chron r.1 r.2}) :
    IsLocallyClosed (pairLocus τ σ c Chron δ₂) :=
  (isClosed_pairLocus hτ hσ c hChron hδ).isLocallyClosed

end Closedness

/-! ### Locality and the subsheaf package, consumed unchanged -/

variable {ι : Type*} {U : ι → Set β}

/-- **Interior-pair record-hood is a local condition** over a directed
open cover: a closed set satisfies the condition iff every clip does.
Forward is heredity; backward, a pair's two points land in two cover
members and directedness collects them into one — the single place
directedness enters, exactly as at the classical stratum.  Clips
leave `Chron` and `δ₂` untouched: both live on the stage space. -/
theorem isPairGraph_iff_forall_clip (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) (F : FellCloseds β) :
    IsPairGraph τ σ c Chron δ₂ (F : Set β)
      ↔ ∀ i, FellCloseds.clip (U i) F
          ∈ pairLocus (τ ∘ (↑)) (σ ∘ (↑)) c Chron δ₂ := by
  constructor
  · intro hF i p hp q hq hchron
    exact hF _ (FellCloseds.mem_clip.mp hp) _ (FellCloseds.mem_clip.mp hq)
      hchron
  · intro hF p hpF q hqF hchron
    obtain ⟨i, hpi⟩ := mem_iUnion.mp (hcov ▸ mem_univ p)
    obtain ⟨j, hqj⟩ := mem_iUnion.mp (hcov ▸ mem_univ q)
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact hF k ⟨p, hik hpi⟩ (FellCloseds.mem_clip.mpr hpF)
      ⟨q, hjk hqj⟩ (FellCloseds.mem_clip.mpr hqF) hchron

/-- The interior-pair loci form a local locus family over any directed
open cover: the generic subsheaf package applies unchanged. -/
theorem pairLocus_isLocalLocus (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) :
    FellCloseds.IsLocalLocus U (pairLocus τ σ c Chron δ₂)
      (fun _ => pairLocus (τ ∘ (↑)) (σ ∘ (↑)) c Chron δ₂) :=
  fun F => isPairGraph_iff_forall_clip hdir hcov F

/-- **Compatible families of interior-pair records glue to
interior-pair records**: the pair instantiation of
`IsLocalLocus.glue_mem`. -/
theorem glue_mem_pairLocus (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    (p : FellCloseds.ProjLim U)
    (hp : ∀ i, p.1 i ∈ pairLocus (τ ∘ (↑)) (σ ∘ (↑)) c Chron δ₂) :
    FellCloseds.glue U hUo hdir hcov p ∈ pairLocus τ σ c Chron δ₂ :=
  (pairLocus_isLocalLocus hdir hcov).glue_mem hUo hdir hcov p hp

/-- **The interior-pair locus is a closed subsheaf of the Fell
carrier**: the descent homeomorphism restricts to the pair loci — the
general-support story lands on the same generic interface as the
classical stratum, with `isClosed_pairLocus` supplying the closedness
leg. -/
noncomputable def pairLocusHomeomorph (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) :
    ↥(pairLocus τ σ c Chron δ₂)
      ≃ₜ ↥(FellCloseds.levelLocus U
          fun _ => pairLocus (τ ∘ (↑)) (σ ∘ (↑)) c Chron δ₂) :=
  (pairLocus_isLocalLocus hdir hcov).homeomorph hUo hdir hcov

end PairGraph

/-! ## The degeneracy check: `(⊤, dist)` recovers the landed theorem -/

section Degeneracy

variable {β T E : Type*} [PseudoMetricSpace T] [PseudoMetricSpace E]
  {τ : β → T} {σ : β → E} {c : ℝ≥0}

/-- At the trivial chronology the interior-pair condition is the cone
condition. -/
theorem isPairGraph_trivial_iff {A : Set β} :
    IsPairGraph τ σ c (fun _ _ => True) (fun s t => dist s t) A
      ↔ IsSpeedGraph τ σ c A := by
  simp [IsPairGraph, IsSpeedGraph]

variable [TopologicalSpace β]

/-- **The degeneracy identity**: at `Chron := ⊤`, `δ₂ := dist` the
interior-pair locus *is* the landed record locus. -/
theorem pairLocus_trivial_eq_speedLocus :
    pairLocus τ σ c (fun _ _ => True) (fun s t => dist s t)
      = speedLocus τ σ c := by
  ext G
  exact isPairGraph_trivial_iff

/-- **The degeneracy check**: the landed closedness theorem
(`isClosed_speedLocus`) re-derived through the generalized one — the
two site hypotheses discharge by `isOpen_univ` (every pair
constrained: the trivial relation is open) and continuity of the
timeline distance (a continuous function is upper semicontinuous).
The generalization is conservative over the classical column. -/
theorem isClosed_speedLocus_via_pairLocus (hτ : Continuous τ)
    (hσ : Continuous σ) (c : ℝ≥0) : IsClosed (speedLocus τ σ c) := by
  rw [← pairLocus_trivial_eq_speedLocus (τ := τ) (σ := σ) (c := c)]
  refine isClosed_pairLocus hτ hσ c ?_ ?_
  · exact isOpen_univ
  · intro x _ y hy
    exact ((isOpen_lt (continuous_fst.dist continuous_snd)
      continuous_const).eventually_mem hy).filter_mono nhdsWithin_le_nhds

end Degeneracy

end SuFunctor.Universe

#print axioms SuFunctor.Universe.isOpen_pairViolation
#print axioms SuFunctor.Universe.isClosed_pairLocus
#print axioms SuFunctor.Universe.isCompact_pairLocus
#print axioms SuFunctor.Universe.isLocallyClosed_pairLocus
#print axioms SuFunctor.Universe.isPairGraph_iff_forall_clip
#print axioms SuFunctor.Universe.pairLocus_isLocalLocus
#print axioms SuFunctor.Universe.glue_mem_pairLocus
#print axioms SuFunctor.Universe.pairLocusHomeomorph
#print axioms SuFunctor.Universe.pairLocus_trivial_eq_speedLocus
#print axioms SuFunctor.Universe.isClosed_speedLocus_via_pairLocus
