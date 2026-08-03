import SuFunctor.Universe.FellDescent
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sequences

/-! # The record locus: closed subsheaf of the Fell carrier

Rung D of the temporal-sheaf carrier (the design's §3.4 and the §4.1
corollary): the record locus is **closed** in the Fell hyperspace —
hence compact for free — and record-hood is a **local-plus-closed**
condition, so compatible families of clipped records glue to records
and the record loci form a closed subsheaf of the carrier, with the
descent homeomorphism restricting to them.

The development factors the corollary's sentence:

* **Generic local-plus-closed loci** (`IsLocalLocus`): over a system of
  subsets with per-level loci, a locus family *of local character* —
  membership in the ambient locus is equivalent to membership of every
  clip in its level locus — with closed levels is closed
  (`IsLocalLocus.isClosed`: the ambient locus is the intersection of
  the clip preimages, each closed by rung A's continuity), hence
  compact with no further hypotheses (`IsLocalLocus.isCompact` — the
  hyperspace is compact over every ambient, so **the speed row's
  entire job relocates to keeping the locus closed**, the design's
  §3.4 headline).  Compatible families levelwise in the loci glue into
  the ambient locus (`IsLocalLocus.glue_mem`), and the descent
  homeomorphism restricts to a homeomorphism of the locus onto the
  levelwise-locus part of the projective limit
  (`IsLocalLocus.homeomorph`) — the closed-subsheaf display.  The
  genericity is a deliberate seam: richer record strata (floor
  structure) discharge the same three obligations and inherit the
  display.

* **The record locus, speed-graph stratum** (`IsSpeedGraph`,
  `speedLocus`): the class of graphs of speed-`c` arcs, in pairwise
  *cone-condition* form — every two members' states are within `c`
  times their timeline distance — chart-parametrized (`τ` to a
  timeline, `σ` to a state space) so one definition serves the ambient
  and every subtype level uniformly.  Closedness
  (`isClosed_speedLocus`) is a pure **hit-face** argument: a violating
  pair persists on a product-open rectangle, and two hit demands
  through the rectangle's sides avoid the locus — no compactness of
  anything, at any stratum.  Locality
  (`isSpeedGraph_iff_forall_clip`) consumes directedness exactly once:
  a violating pair's two points are collected into a single cover
  member.  The empty record and the singleton record are citizens
  (`bot_mem_speedLocus`, `singleton_mem_speedLocus`) — early stop,
  late start, and total escape are citizenship, not defect — and the
  locus is locally closed (`isLocallyClosed_speedLocus`), so the
  record locus is itself a citizen of the locally-closed fibre class
  the composition tier assigns.

* **The arc reading** (`isSpeedGraph_iff_exists_lipschitzOnWith`): over
  a product ambient with complete metric state space, a closed
  cone-set *is* the graph of a `c`-Lipschitz arc over a **closed**
  sub-timeline — relative closedness of the domain is derived, not
  assumed (`isClosed_image_fst_of_isSpeedGraph`): the cone condition
  itself makes the states of a converging time sequence Cauchy.  This
  is what makes the pairwise definition the design's "graphs of
  speed-`c` arcs over relatively closed sub-timelines", unanchored and
  lifetime-windowed.

The companion witness module (`FellRecordWitness`) delimits the
hypotheses: the speed row cannot be dropped (steepening graphs converge
to a vertical fibre, which is no graph at any speed), and directedness
is load-bearing at statement level for both locality and gluing.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter
open scoped NNReal

variable {α : Type*} [TopologicalSpace α]

namespace FellCloseds

/-! ## Generic local-plus-closed loci -/

section LocalLocus

variable {ι : Type*} {U : ι → Set α} {R₀ : Set (FellCloseds α)}
  {R : ∀ i, Set (FellCloseds ↥(U i))}

/-- A locus family is *of local character* over a system of subsets
when membership in the ambient locus is equivalent to membership of
every clip in its level locus.  This is the "record-hood is a local
condition" hypothesis, isolated: instantiations discharge it (for the
speed locus, by directedness), and the subsheaf package below consumes
it. -/
def IsLocalLocus (U : ι → Set α) (R₀ : Set (FellCloseds α))
    (R : ∀ i, Set (FellCloseds ↥(U i))) : Prop :=
  ∀ F : FellCloseds α, F ∈ R₀ ↔ ∀ i, clip (U i) F ∈ R i

/-- A local locus with closed levels is closed: it is the intersection
of the clip preimages of the level loci, each closed because clipping
to an open member is continuous. -/
theorem IsLocalLocus.isClosed (hloc : IsLocalLocus U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hRcl : ∀ i, IsClosed (R i)) :
    IsClosed R₀ := by
  have heq : R₀ = ⋂ i, clip (U i) ⁻¹' R i := by
    ext F
    simpa [mem_iInter] using hloc F
  rw [heq]
  exact isClosed_iInter fun i => (hRcl i).preimage (continuous_clip (hUo i))

/-- **Compactness comes free** (the design's §3.4): a closed locus in
the hypothesis-free-compact Fell hyperspace is compact.  Over the ray,
compactness of the record class was the theorem; over the site it is a
corollary of closedness — the speed row's entire job relocates to
keeping the locus closed. -/
theorem IsLocalLocus.isCompact (hloc : IsLocalLocus U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hRcl : ∀ i, IsClosed (R i)) :
    IsCompact R₀ :=
  (hloc.isClosed hUo hRcl).isCompact

variable (U R) in
/-- The levelwise-locus part of the projective limit: compatible
families whose every member sits in its level locus. -/
def levelLocus : Set (ProjLim U) := {p | ∀ i, p.1 i ∈ R i}

@[simp]
theorem mem_levelLocus {p : ProjLim U} :
    p ∈ levelLocus U R ↔ ∀ i, p.1 i ∈ R i := Iff.rfl

/-- The levelwise locus is closed in the projective limit whenever the
level loci are closed: it is an intersection of coordinate
preimages. -/
theorem isClosed_levelLocus (hRcl : ∀ i, IsClosed (R i)) :
    IsClosed (levelLocus U R) := by
  have heq : levelLocus U R = ⋂ i, (fun p : ProjLim U => p.1 i) ⁻¹' R i := by
    ext p
    simp [levelLocus, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i =>
    (hRcl i).preimage ((continuous_apply i).comp continuous_subtype_val)

/-- The clip of a glue is the family member: the glue-trace identity of
the descent theorem, read one level at a time. -/
theorem clip_glue (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) (p : ProjLim U) (i : ι) :
    clip (U i) (glue U hUo hdir hcov p) = p.1 i :=
  congrFun (congrArg Subtype.val (toProjLim_glue U hUo hdir hcov p)) i

/-- **Gluing preserves the locus**: over a directed open cover, a
compatible family levelwise in the level loci glues into the ambient
locus — a compatible family of clipped records is locally a record
everywhere, so its glue is a record. -/
theorem IsLocalLocus.glue_mem (hloc : IsLocalLocus U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) (p : ProjLim U) (hp : p ∈ levelLocus U R) :
    glue U hUo hdir hcov p ∈ R₀ :=
  (hloc _).mpr fun i => by
    rw [clip_glue hUo hdir hcov p i]
    exact hp i

/-- The canonical map carries the ambient locus onto the levelwise
locus: forward by locality, backward through the glue. -/
theorem IsLocalLocus.image_toProjLim (hloc : IsLocalLocus U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) :
    toProjLim U '' R₀ = levelLocus U R := by
  ext p
  constructor
  · rintro ⟨F, hF, rfl⟩ i
    exact (hloc F).mp hF i
  · intro hp
    exact ⟨glue U hUo hdir hcov p, hloc.glue_mem hUo hdir hcov p hp,
      toProjLim_glue U hUo hdir hcov p⟩

/-- **The closed-subsheaf display**: the descent homeomorphism
restricts to a homeomorphism from a local locus onto the
levelwise-locus part of the projective limit.  With
`IsLocalLocus.isClosed` and `isClosed_levelLocus` this is the full
statement that a local-plus-closed locus family is a closed subsheaf
of the Fell carrier. -/
noncomputable def IsLocalLocus.homeomorph (hloc : IsLocalLocus U R₀ R)
    (hUo : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) :
    ↥R₀ ≃ₜ ↥(levelLocus U R) :=
  ((projLimHomeomorph U hUo hdir hcov).image R₀).trans
    (Homeomorph.setCongr (hloc.image_toProjLim hUo hdir hcov))

end LocalLocus

end FellCloseds

/-! ## The record locus: the speed-graph stratum -/

section SpeedGraph

variable {β : Type*} {T E : Type*}
  [PseudoMetricSpace T] [PseudoMetricSpace E]

/-- The **cone condition**: a set of a chart-carrying ambient is a
speed-`c` graph when every two of its members' states are within `c`
times their timeline distance.  `τ` charts the timeline, `σ` the
state; the chart parametrization serves the ambient (`Prod.fst`,
`Prod.snd`) and every subtype level (the charts composed with the
inclusion) uniformly.  Pairwise, hence hereditary; over a complete
metric state space it is exactly graph-hood of a `c`-Lipschitz arc
over a closed sub-timeline (`isSpeedGraph_iff_exists_lipschitzOnWith`). -/
def IsSpeedGraph (τ : β → T) (σ : β → E) (c : ℝ≥0) (A : Set β) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, dist (σ p) (σ q) ≤ (c : ℝ) * dist (τ p) (τ q)

variable {τ : β → T} {σ : β → E} {c : ℝ≥0}

/-- The cone condition is hereditary: subsets of speed graphs are
speed graphs.  Unanchored, lifetime-windowed citizenship in one line —
early stop and late start are sub-graphs. -/
theorem IsSpeedGraph.mono {A B : Set β} (hAB : A ⊆ B)
    (h : IsSpeedGraph τ σ c B) : IsSpeedGraph τ σ c A :=
  fun p hp q hq => h p (hAB hp) q (hAB hq)

/-- The empty record is a speed graph: total escape is citizenship. -/
theorem isSpeedGraph_empty : IsSpeedGraph τ σ c (∅ : Set β) :=
  fun p hp => absurd hp (notMem_empty p)

/-- A single stage is a speed graph: the minimal lifetime is
citizenship. -/
theorem isSpeedGraph_singleton (x : β) : IsSpeedGraph τ σ c {x} := by
  intro p hp q hq
  rw [mem_singleton_iff] at hp hq
  subst hp
  subst hq
  simp

variable [TopologicalSpace β]

variable (τ σ c) in
/-- The **record locus** at the speed-graph stratum: the closed sets
satisfying the cone condition, as a class of the Fell hyperspace. -/
def speedLocus : Set (FellCloseds β) :=
  {G | IsSpeedGraph τ σ c (G : Set β)}

@[simp]
theorem mem_speedLocus {G : FellCloseds β} :
    G ∈ speedLocus τ σ c ↔ IsSpeedGraph τ σ c (G : Set β) := Iff.rfl

/-- The empty record is a citizen of the record locus. -/
theorem bot_mem_speedLocus : (⊥ : FellCloseds β) ∈ speedLocus τ σ c := by
  rw [mem_speedLocus, FellCloseds.coe_bot]
  exact isSpeedGraph_empty

/-- Singleton records are citizens of the record locus. -/
theorem singleton_mem_speedLocus [T1Space β] (x : β) :
    (⟨{x}, isClosed_singleton⟩ : FellCloseds β) ∈ speedLocus τ σ c := by
  rw [mem_speedLocus, FellCloseds.coe_mk]
  exact isSpeedGraph_singleton x

/-- **The record locus is closed** (the design's §3.4, closedness
half): the complement is open by a pure hit-face argument.  A
non-graph carries a violating pair; the violation's margin persists on
a product-open rectangle around the pair by continuity of the defect,
and the two hit demands through the rectangle's sides are a Fell
neighborhood avoiding the locus.  No compactness — of the ambient, the
graphs, or the demands — anywhere. -/
theorem isClosed_speedLocus (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) : IsClosed (speedLocus τ σ c) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro G hG
  obtain ⟨p, hpG, q, hqG, hviol⟩ :
      ∃ p ∈ (G : Set β), ∃ q ∈ (G : Set β),
        (c : ℝ) * dist (τ p) (τ q) < dist (σ p) (σ q) := by
    simpa [speedLocus, IsSpeedGraph, not_forall, not_le] using hG
  have hopen : IsOpen {r : β × β |
      (c : ℝ) * dist (τ r.1) (τ r.2) < dist (σ r.1) (σ r.2)} :=
    isOpen_lt
      (continuous_const.mul ((hτ.comp continuous_fst).dist (hτ.comp continuous_snd)))
      ((hσ.comp continuous_fst).dist (hσ.comp continuous_snd))
  obtain ⟨Vp, Vq, hVp, hVq, hpVp, hqVq, hsub⟩ :=
    isOpen_prod_iff.mp hopen p q hviol
  refine ⟨{H : FellCloseds β | ((H : Set β) ∩ Vp).Nonempty}
      ∩ {H : FellCloseds β | ((H : Set β) ∩ Vq).Nonempty},
    ?_, ?_, ⟨p, hpG, hpVp⟩, ⟨q, hqG, hqVq⟩⟩
  · -- every member of the double hit demand carries a violating pair
    rintro H ⟨⟨p', hp'H, hp'V⟩, ⟨q', hq'H, hq'V⟩⟩ hHmem
    exact absurd (hHmem p' hp'H q' hq'H)
      (not_le.mpr (hsub (mk_mem_prod hp'V hq'V)))
  · exact (FellCloseds.isOpen_inter_nonempty_of_isOpen hVp).inter
      (FellCloseds.isOpen_inter_nonempty_of_isOpen hVq)

/-- **Compactness comes free** for the record locus: closed in the
hypothesis-free-compact hyperspace. -/
theorem isCompact_speedLocus (hτ : Continuous τ) (hσ : Continuous σ)
    (c : ℝ≥0) : IsCompact (speedLocus τ σ c) :=
  (isClosed_speedLocus hτ hσ c).isCompact

/-- The record locus is locally closed — the connective to the
composition tier, whose fibres are the locally closed classes of the
Fell hyperspace: the record locus is itself a citizen of that fibre
class. -/
theorem isLocallyClosed_speedLocus (hτ : Continuous τ)
    (hσ : Continuous σ) (c : ℝ≥0) :
    IsLocallyClosed (speedLocus τ σ c) :=
  (isClosed_speedLocus hτ hσ c).isLocallyClosed

/-! ### Locality and the subsheaf package -/

variable {ι : Type*} {U : ι → Set β}

/-- **Record-hood is a local condition** over a directed open cover: a
closed set satisfies the cone condition iff every clip does.  Forward
is heredity; backward, a pair's two points land in two cover members,
and **directedness collects them into one** — the single place
directedness enters record-hood. -/
theorem isSpeedGraph_iff_forall_clip (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) (F : FellCloseds β) :
    IsSpeedGraph τ σ c (F : Set β)
      ↔ ∀ i, FellCloseds.clip (U i) F
          ∈ speedLocus (τ ∘ (↑)) (σ ∘ (↑)) c := by
  constructor
  · intro hF i p hp q hq
    exact hF _ (FellCloseds.mem_clip.mp hp) _ (FellCloseds.mem_clip.mp hq)
  · intro hF p hpF q hqF
    obtain ⟨i, hpi⟩ := mem_iUnion.mp (hcov ▸ mem_univ p)
    obtain ⟨j, hqj⟩ := mem_iUnion.mp (hcov ▸ mem_univ q)
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact hF k ⟨p, hik hpi⟩ (FellCloseds.mem_clip.mpr hpF)
      ⟨q, hjk hqj⟩ (FellCloseds.mem_clip.mpr hqF)

/-- The record loci form a local locus family over any directed open
cover: the generic subsheaf package applies. -/
theorem speedLocus_isLocalLocus (hdir : Directed (· ⊆ ·) U)
    (hcov : ⋃ i, U i = univ) :
    FellCloseds.IsLocalLocus U (speedLocus τ σ c)
      (fun _ => speedLocus (τ ∘ (↑)) (σ ∘ (↑)) c) :=
  fun F => isSpeedGraph_iff_forall_clip hdir hcov F

/-- **Compatible families of records glue to records**: the record
instantiation of `IsLocalLocus.glue_mem`. -/
theorem glue_mem_speedLocus (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ)
    (p : FellCloseds.ProjLim U)
    (hp : ∀ i, p.1 i ∈ speedLocus (τ ∘ (↑)) (σ ∘ (↑)) c) :
    FellCloseds.glue U hUo hdir hcov p ∈ speedLocus τ σ c :=
  (speedLocus_isLocalLocus hdir hcov).glue_mem hUo hdir hcov p hp

/-- **The record locus is a closed subsheaf of the Fell carrier**: the
descent homeomorphism restricts to the record loci.  Together with
`isClosed_speedLocus` (each side closed, by
`FellCloseds.isClosed_levelLocus` on the limit side) this is rung D's
corollary: `𝓡 ⊆ 𝓗` as a closed subsheaf, over any directed open
cover. -/
noncomputable def speedLocusHomeomorph (hUo : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcov : ⋃ i, U i = univ) :
    ↥(speedLocus τ σ c)
      ≃ₜ ↥(FellCloseds.levelLocus U
          fun _ => speedLocus (τ ∘ (↑)) (σ ∘ (↑)) c) :=
  (speedLocus_isLocalLocus hdir hcov).homeomorph hUo hdir hcov

end SpeedGraph

/-! ## The arc reading: cone-sets are graphs of Lipschitz arcs -/

section ArcReading

variable {T : Type*} [PseudoMetricSpace T] {E : Type*} [MetricSpace E]
  {c : ℝ≥0}

/-- **The sub-timeline of a record is closed** (the "relatively closed
sub-timelines" clause, derived rather than assumed): over a complete
metric state space, the time-projection of a closed cone-set is
closed.  The cone condition itself is the mechanism: states over a
converging sequence of times are Cauchy with modulus `c`, so they
converge, and closedness of the graph collects the limit point. -/
theorem isClosed_image_fst_of_isSpeedGraph [CompleteSpace E]
    {F : FellCloseds (T × E)}
    (hF : IsSpeedGraph Prod.fst Prod.snd c (F : Set (T × E))) :
    IsClosed (Prod.fst '' (F : Set (T × E))) := by
  refine IsSeqClosed.isClosed ?_
  intro ts t hmem hlim
  choose ps hpsF hps1 using hmem
  have hct : CauchySeq ts := hlim.cauchySeq
  have hcx : CauchySeq fun n => (ps n).2 := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.mp hct (ε / ((c : ℝ) + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hcone : dist (ps m).2 (ps n).2
        ≤ (c : ℝ) * dist (ps m).1 (ps n).1 := hF _ (hpsF m) _ (hpsF n)
    have hdt : dist (ps m).1 (ps n).1 < ε / ((c : ℝ) + 1) := by
      rw [hps1 m, hps1 n]
      exact hN m hm n hn
    have hmul : (c : ℝ) * dist (ps m).1 (ps n).1
        ≤ (c : ℝ) * (ε / ((c : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hdt.le c.coe_nonneg
    have hlt : (c : ℝ) * (ε / ((c : ℝ) + 1)) < ε := by
      have h1 : (c : ℝ) * (ε / ((c : ℝ) + 1))
          < ((c : ℝ) + 1) * (ε / ((c : ℝ) + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      have h2 : ((c : ℝ) + 1) * (ε / ((c : ℝ) + 1)) = ε := by
        rw [← mul_div_assoc,
          mul_div_cancel_left₀ _ (by positivity : ((c : ℝ) + 1) ≠ 0)]
      rwa [h2] at h1
    exact (hcone.trans hmul).trans_lt hlt
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcx
  have hfst : Tendsto (fun n => (ps n).1) atTop (𝓝 t) := by
    have : (fun n => (ps n).1) = ts := funext hps1
    rwa [this]
  have htend : Tendsto ps atTop (𝓝 (t, x)) := by
    have : Tendsto (fun n => ((ps n).1, (ps n).2)) atTop (𝓝 (t, x)) :=
      hfst.prodMk_nhds hx
    simpa using this
  exact ⟨(t, x), F.isClosed.mem_of_tendsto htend (Eventually.of_forall hpsF),
    rfl⟩

open Classical in
/-- The canonical arc of a record: at each time of the sub-timeline,
the (unique) state the record carries there; junk off the
sub-timeline. -/
noncomputable def speedArc [Nonempty E] (F : FellCloseds (T × E)) :
    T → E :=
  fun t => if h : ∃ x, (t, x) ∈ F then h.choose else Classical.arbitrary E

theorem speedArc_mem [Nonempty E] {F : FellCloseds (T × E)} {t : T}
    (h : ∃ x, (t, x) ∈ F) : (t, speedArc F t) ∈ F := by
  unfold speedArc
  rw [dif_pos h]
  exact h.choose_spec

/-- States are unique per time on a record: the cone condition at a
shared time forces zero state distance. -/
theorem eq_speedArc_of_mem [Nonempty E] {F : FellCloseds (T × E)}
    (hF : IsSpeedGraph Prod.fst Prod.snd c (F : Set (T × E)))
    {t : T} {x : E} (h : (t, x) ∈ F) : x = speedArc F t := by
  have hmem : (t, speedArc F t) ∈ F := speedArc_mem ⟨x, h⟩
  have hd : dist x (speedArc F t) ≤ (c : ℝ) * dist t t := hF _ h _ hmem
  rw [dist_self, mul_zero] at hd
  exact dist_le_zero.mp hd

/-- **The arc reading** (the design's §3.4 class, pairwise form made
honest): over a complete metric state space, a closed set satisfies
the cone condition iff it is the graph of a `c`-Lipschitz arc over a
closed sub-timeline.  Unanchored and lifetime-windowed: the domain is
any closed subset of the timeline, the empty and the singleton domains
included. -/
theorem isSpeedGraph_iff_exists_lipschitzOnWith [CompleteSpace E]
    [Nonempty E] {F : FellCloseds (T × E)} :
    IsSpeedGraph Prod.fst Prod.snd c (F : Set (T × E))
      ↔ ∃ D : Set T, IsClosed D ∧ ∃ f : T → E, LipschitzOnWith c f D ∧
          (F : Set (T × E)) = (fun t => (t, f t)) '' D := by
  constructor
  · intro hF
    refine ⟨Prod.fst '' (F : Set (T × E)),
      isClosed_image_fst_of_isSpeedGraph hF, speedArc F, ?_, ?_⟩
    · rw [lipschitzOnWith_iff_dist_le_mul]
      rintro t ⟨p, hpF, rfl⟩ t' ⟨q, hqF, rfl⟩
      have h1 : (p.1, speedArc F p.1) ∈ F := speedArc_mem ⟨p.2, hpF⟩
      have h2 : (q.1, speedArc F q.1) ∈ F := speedArc_mem ⟨q.2, hqF⟩
      exact hF _ h1 _ h2
    · ext ⟨t, x⟩
      constructor
      · intro h
        refine ⟨t, ⟨(t, x), h, rfl⟩, ?_⟩
        show (t, speedArc F t) = (t, x)
        rw [← eq_speedArc_of_mem hF h]
      · rintro ⟨t', ⟨p, hpF, rfl⟩, heq⟩
        rw [← heq]
        exact speedArc_mem ⟨p.2, hpF⟩
  · rintro ⟨D, -, f, hf, heq⟩
    rw [heq]
    rintro p ⟨t, htD, rfl⟩ q ⟨t', ht'D, rfl⟩
    exact lipschitzOnWith_iff_dist_le_mul.mp hf t htD t' ht'D

end ArcReading

end SuFunctor.Universe

#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocus.isClosed
#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocus.isCompact
#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocus.glue_mem
#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocus.homeomorph
#print axioms SuFunctor.Universe.FellCloseds.isClosed_levelLocus
#print axioms SuFunctor.Universe.isClosed_speedLocus
#print axioms SuFunctor.Universe.isCompact_speedLocus
#print axioms SuFunctor.Universe.isSpeedGraph_iff_forall_clip
#print axioms SuFunctor.Universe.glue_mem_speedLocus
#print axioms SuFunctor.Universe.speedLocusHomeomorph
#print axioms SuFunctor.Universe.isClosed_image_fst_of_isSpeedGraph
#print axioms SuFunctor.Universe.isSpeedGraph_iff_exists_lipschitzOnWith
