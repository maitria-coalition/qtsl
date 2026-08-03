import SuFunctor.Universe.FellRecordLocus
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The steepening and nondirected witnesses: rung D's hypotheses are load-bearing

Refuting fixtures for the record-locus module (`FellRecordLocus`),
delimiting its two hypotheses mathematically — the weakened statements
are false, not merely unproved:

* **The speed row cannot be dropped** (the design's §3.4: the limits
  of unbounded-speed graphs are bands, not graphs).  The steepening
  family `steepGraph n` — the graph of `t ↦ (n+1)·t`, a record at its
  own speed, functional at every `n` — Fell-converges to the
  **vertical fibre** `{0} ×ˢ univ` (`tendsto_steepGraphF`), the
  minimal band: two states over one time, a graph of nothing at any
  speed.  Hence neither bare graph-hood (`not_isClosed_graphLocus`)
  nor speed-boundedness with the bound existentially absorbed
  (`not_isClosed_iUnion_speedLocus`) cuts a closed locus; only the
  fixed speed row does (`isClosed_speedLocus`).  Hit face: a fibre
  point `(0, x)` is approached along `(x/(n+1), x)`; miss face: a
  compact avoiding the fibre keeps a positive time-distance `δ` and a
  bounded state, and a steep-graph point inside it would force
  `(n+1)·δ` under that bound — granted only finitely often.

* **Directedness is load-bearing at statement level** for record
  locality and record gluing (the descent module's nondirected fixture,
  one storey up).  Over the nondirected open cover
  `{Iio 1 ×ˢ univ, Ioi 0 ×ˢ univ}` of the plane, the two-point closed
  set `{(0,0), (1,5)}` has every clip a singleton record
  (`clip_twoPointRecord_mem_speedLocus`) while being no record at
  speed `1` (`not_mem_speedLocus_twoPointRecord`): levelwise
  record-hood does not imply record-hood
  (`not_isLocalLocus_nondirected`), and the compatible family of the
  two clips — compatibility is the clip-absorption identity, no
  directedness consulted — glues to that same non-record
  (`not_isSpeedGraph_glueSet_nondirected`).  No proof of the locality
  or gluing theorems could avoid directedness.

Both witnesses live over concrete real ambients; this module therefore
imports real instances and is kept separate from the stratum-general
`FellRecordLocus`, per the house pattern.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter
open scoped NNReal

attribute [local instance] SuFunctor.Universe.fell

/-! ## The steepening witness: the speed row cannot be dropped -/

/-- The steepening family: the graph of `t ↦ (n+1)·t` over the whole
line — a record at speed `n+1`, functional at every `n`. -/
def steepGraph (n : ℕ) : Set (ℝ × ℝ) := {p | p.2 = ((n : ℝ) + 1) * p.1}

theorem mem_steepGraph {n : ℕ} {p : ℝ × ℝ} :
    p ∈ steepGraph n ↔ p.2 = ((n : ℝ) + 1) * p.1 := Iff.rfl

theorem isClosed_steepGraph (n : ℕ) : IsClosed (steepGraph n) :=
  isClosed_eq continuous_snd (continuous_const.mul continuous_fst)

/-- Each steepening stage is a record at its own speed. -/
theorem isSpeedGraph_steepGraph (n : ℕ) :
    IsSpeedGraph Prod.fst Prod.snd ((n : ℝ≥0) + 1) (steepGraph n) := by
  rintro ⟨t, x⟩ hp ⟨s, y⟩ hq
  have hp' : x = ((n : ℝ) + 1) * t := hp
  have hq' : y = ((n : ℝ) + 1) * s := hq
  subst hp'
  subst hq'
  show dist (((n : ℝ) + 1) * t) (((n : ℝ) + 1) * s)
    ≤ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) * dist t s
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  push_cast
  exact le_rfl

/-- The vertical fibre: every state over the single time `0` — the
minimal band. -/
def verticalFibre : Set (ℝ × ℝ) := {0} ×ˢ univ

theorem isClosed_verticalFibre : IsClosed verticalFibre :=
  isClosed_singleton.prod isClosed_univ

/-- The vertical fibre is a record at no speed: it carries two states
over one time. -/
theorem not_isSpeedGraph_verticalFibre (c : ℝ≥0) :
    ¬ IsSpeedGraph Prod.fst Prod.snd c verticalFibre := by
  intro h
  have hd := h (0, 0) ⟨rfl, mem_univ _⟩ (0, 1) ⟨rfl, mem_univ _⟩
  simp only [Real.dist_eq] at hd
  norm_num at hd

/-- **Fell convergence of the steepening family to the vertical
fibre**: unbounded speed exits the graph class in the limit.  Hit face
by the approach points `(x/(n+1), x)`; miss face by the positive
time-distance a compact keeps from the fibre. -/
theorem tendsto_steepGraph :
    Tendsto steepGraph atTop (𝓝 verticalFibre) := by
  refine tendsto_nhds_generateFrom_iff.mpr ?_
  rintro s (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩) hBs
  · -- miss face: `K` compact, disjoint from the fibre
    have hdisj : Disjoint verticalFibre K := hBs
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact Eventually.of_forall fun n => disjoint_empty _
    have hcont : ContinuousOn (fun p : ℝ × ℝ => |p.1|) K :=
      (continuous_abs.comp continuous_fst).continuousOn
    obtain ⟨pm, hpmK, hpm⟩ := hK.exists_isMinOn hKne hcont
    have hδpos : 0 < |pm.1| := by
      rcases eq_or_ne pm.1 0 with h0 | h0
      · exact absurd hpmK <| Set.disjoint_left.mp hdisj
          (show pm ∈ verticalFibre from ⟨mem_singleton_iff.mpr h0, mem_univ _⟩)
      · exact abs_pos.mpr h0
    obtain ⟨M, hM⟩ := (hK.image (continuous_abs.comp continuous_snd)).bddAbove
    have hev : ∀ᶠ n : ℕ in atTop, M < ((n : ℝ) + 1) * |pm.1| := by
      have hten : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * |pm.1|) atTop atTop :=
        (tendsto_atTop_add_const_right atTop 1
          tendsto_natCast_atTop_atTop).atTop_mul_const hδpos
      exact hten.eventually (eventually_gt_atTop M)
    filter_upwards [hev] with n hn
    show Disjoint (steepGraph n) K
    rw [Set.disjoint_left]
    rintro ⟨t, x⟩ hp hpK
    have hp' : x = ((n : ℝ) + 1) * t := hp
    have hxM : |x| ≤ M := hM (mem_image_of_mem _ hpK)
    have htδ : |pm.1| ≤ |t| := isMinOn_iff.mp hpm _ hpK
    have hge : ((n : ℝ) + 1) * |pm.1| ≤ |x| := by
      rw [hp', abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      exact mul_le_mul_of_nonneg_left htδ (by positivity)
    linarith
  · -- hit face: `V` open, met by the fibre at `(0, x)`
    obtain ⟨⟨t₀, x⟩, hpB, hpV⟩ := hBs
    obtain ⟨ht₀, -⟩ := hpB
    rw [mem_singleton_iff] at ht₀
    subst ht₀
    have htend : Tendsto (fun n : ℕ => ((x / ((n : ℝ) + 1), x) : ℝ × ℝ))
        atTop (𝓝 (0, x)) := by
      have hden : Tendsto (fun n : ℕ => x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul x
        simpa [div_eq_mul_inv, mul_zero] using this
      exact hden.prodMk_nhds tendsto_const_nhds
    have hV' : IsOpen V := hV
    have hev : ∀ᶠ n : ℕ in atTop,
        ((x / ((n : ℝ) + 1), x) : ℝ × ℝ) ∈ V :=
      htend.eventually (hV'.eventually_mem hpV)
    filter_upwards [hev] with n hn
    refine ⟨(x / ((n : ℝ) + 1), x), ?_, hn⟩
    show x = ((n : ℝ) + 1) * (x / ((n : ℝ) + 1))
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-- The steepening stages, at the closeds carrier. -/
def steepGraphF (n : ℕ) : FellCloseds (ℝ × ℝ) :=
  ⟨steepGraph n, isClosed_steepGraph n⟩

/-- The vertical fibre, at the closeds carrier. -/
def verticalFibreF : FellCloseds (ℝ × ℝ) :=
  ⟨verticalFibre, isClosed_verticalFibre⟩

theorem tendsto_steepGraphF :
    Tendsto steepGraphF atTop (𝓝 verticalFibreF) :=
  FellCloseds.isEmbedding_coe.isInducing.tendsto_nhds_iff.mpr
    tendsto_steepGraph

/-- The bare graph locus: functional graphs, no speed row — the
mutated design in which the speed bound is deleted outright. -/
def graphLocus : Set (FellCloseds (ℝ × ℝ)) :=
  {G | ∀ p ∈ (G : Set (ℝ × ℝ)), ∀ q ∈ (G : Set (ℝ × ℝ)),
    p.1 = q.1 → p.2 = q.2}

theorem steepGraphF_mem_graphLocus (n : ℕ) : steepGraphF n ∈ graphLocus := by
  rintro ⟨t, x⟩ hp ⟨s, y⟩ hq h
  have hp' : x = ((n : ℝ) + 1) * t := hp
  have hq' : y = ((n : ℝ) + 1) * s := hq
  have hts : t = s := h
  show x = y
  rw [hp', hq', hts]

theorem verticalFibreF_notMem_graphLocus : verticalFibreF ∉ graphLocus := by
  intro h
  have h01 : ((0, 0) : ℝ × ℝ).2 = ((0, 1) : ℝ × ℝ).2 :=
    h (0, 0) ⟨rfl, mem_univ _⟩ (0, 1) ⟨rfl, mem_univ _⟩ rfl
  norm_num at h01

/-- **Bare graph-hood is not closed**: the speed row deleted, the
locus loses the steepening limit.  (The design's §3.4: the speed row
"cannot be dropped: the zigzag witness's limits are bands, not
graphs".) -/
theorem not_isClosed_graphLocus : ¬ IsClosed graphLocus := fun h =>
  verticalFibreF_notMem_graphLocus
    (h.mem_of_tendsto tendsto_steepGraphF
      (Eventually.of_forall steepGraphF_mem_graphLocus))

/-- **The speed row survives no existential absorption**: the union of
the record loci over all speeds is not closed either — each steepening
stage is a record at its own speed, and the limit is a record at
none.  Closedness lives at fixed `c` (`isClosed_speedLocus`), exactly
as the design states the class. -/
theorem not_isClosed_iUnion_speedLocus :
    ¬ IsClosed (⋃ c : ℝ≥0,
      speedLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd c) := by
  intro h
  have hmem : ∀ n, steepGraphF n
      ∈ ⋃ c : ℝ≥0, speedLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd c :=
    fun n => mem_iUnion.mpr ⟨(n : ℝ≥0) + 1, isSpeedGraph_steepGraph n⟩
  have hlim := h.mem_of_tendsto tendsto_steepGraphF
    (Eventually.of_forall hmem)
  obtain ⟨c, hc⟩ := mem_iUnion.mp hlim
  exact not_isSpeedGraph_verticalFibre c hc

/-! ## The nondirected witness: directedness is load-bearing -/

/-- The nondirected witness cover of the plane: two overlapping open
half-plane bands, neither containing the other, no third member. -/
def nondirectedBands : Bool → Set (ℝ × ℝ)
  | false => Iio 1 ×ˢ univ
  | true => Ioi 0 ×ˢ univ

theorem isOpen_nondirectedBands (b : Bool) :
    IsOpen (nondirectedBands b) := by
  cases b
  · exact isOpen_Iio.prod isOpen_univ
  · exact isOpen_Ioi.prod isOpen_univ

theorem iUnion_nondirectedBands : ⋃ b, nondirectedBands b = univ := by
  ext ⟨t, x⟩
  simp only [mem_iUnion, mem_univ, iff_true]
  rcases lt_or_ge t 1 with h | h
  · exact ⟨false, h, mem_univ _⟩
  · exact ⟨true, lt_of_lt_of_le one_pos h, mem_univ _⟩

theorem not_directed_nondirectedBands :
    ¬ Directed (· ⊆ ·) nondirectedBands := by
  intro h
  obtain ⟨z, h0, h1⟩ := h false true
  cases z
  · have h2 : ((2 : ℝ), (0 : ℝ)) ∈ nondirectedBands false :=
      h1 (show ((2 : ℝ), (0 : ℝ)) ∈ nondirectedBands true
        from ⟨by norm_num, mem_univ _⟩)
    exact absurd h2.1 (by norm_num)
  · have h2 : ((-1 : ℝ), (0 : ℝ)) ∈ nondirectedBands true :=
      h0 (show ((-1 : ℝ), (0 : ℝ)) ∈ nondirectedBands false
        from ⟨by norm_num, mem_univ _⟩)
    exact absurd h2.1 (by norm_num)

/-- The two-point specimen: `(0,0)` and `(1,5)` — a speed-`1`
violation (state distance `5` over time distance `1`) whose two points
never share a cover member. -/
def twoPointRecord : FellCloseds (ℝ × ℝ) :=
  ⟨{((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (5 : ℝ))},
    (Set.finite_singleton _).insert _ |>.isClosed⟩

theorem not_mem_speedLocus_twoPointRecord :
    twoPointRecord ∉ speedLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1 := by
  intro h
  have hd : dist (0 : ℝ) 5 ≤ ((1 : ℝ≥0) : ℝ) * dist (0 : ℝ) 1 :=
    h ((0 : ℝ), (0 : ℝ)) (mem_insert _ _)
      ((1 : ℝ), (5 : ℝ)) (mem_insert_of_mem _ rfl)
  rw [Real.dist_eq, Real.dist_eq] at hd
  norm_num at hd

/-- Every clip of the specimen is a singleton, hence a record: the
violating pair is separated by the cover. -/
theorem clip_twoPointRecord_mem_speedLocus (b : Bool) :
    FellCloseds.clip (nondirectedBands b) twoPointRecord
      ∈ speedLocus
        (Prod.fst ∘ ((↑) : ↥(nondirectedBands b) → ℝ × ℝ))
        (Prod.snd ∘ ((↑) : ↥(nondirectedBands b) → ℝ × ℝ)) 1 := by
  have key : ∀ r : ↥(nondirectedBands b),
      r ∈ FellCloseds.clip (nondirectedBands b) twoPointRecord →
        (r : ℝ × ℝ) = (bif b then ((1 : ℝ), (5 : ℝ))
          else ((0 : ℝ), (0 : ℝ))) := by
    intro r hr
    have hrT : (r : ℝ × ℝ) ∈ twoPointRecord := FellCloseds.mem_clip.mp hr
    have hrB : (r : ℝ × ℝ) ∈ nondirectedBands b := r.2
    rcases hrT with h | h
    · -- the point `(0,0)`: excluded by the upper band
      cases b
      · exact h
      · rw [h] at hrB
        exact absurd hrB.1 (by norm_num)
    · -- the point `(1,5)`: excluded by the lower band
      rw [mem_singleton_iff] at h
      cases b
      · rw [h] at hrB
        exact absurd hrB.1 (by norm_num)
      · exact h
  intro p hp q hq
  have hpq : (p : ℝ × ℝ) = (q : ℝ × ℝ) := by
    rw [key p hp, key q hq]
  show dist ((p : ℝ × ℝ).2) ((q : ℝ × ℝ).2)
    ≤ ((1 : ℝ≥0) : ℝ) * dist ((p : ℝ × ℝ).1) ((q : ℝ × ℝ).1)
  rw [hpq, dist_self, dist_self, mul_zero]

/-- **Levelwise record-hood does not imply record-hood without
directedness**: over the nondirected bands — open, covering, only
directedness missing — the two-point specimen has every clip a record
yet is no record.  No proof of the locality theorem
(`isSpeedGraph_iff_forall_clip`) could avoid the directedness
hypothesis. -/
theorem not_isLocalLocus_nondirected :
    ¬ FellCloseds.IsLocalLocus nondirectedBands
      (speedLocus (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1)
      (fun b => speedLocus
        (Prod.fst ∘ ((↑) : ↥(nondirectedBands b) → ℝ × ℝ))
        (Prod.snd ∘ ((↑) : ↥(nondirectedBands b) → ℝ × ℝ)) 1) := by
  intro h
  exact not_mem_speedLocus_twoPointRecord
    ((h twoPointRecord).mpr fun b => clip_twoPointRecord_mem_speedLocus b)

/-- The clips of the specimen as a family: compatible by the
clip-absorption identity — compatibility never consults
directedness. -/
def nondirectedRecordFamily :
    ∀ b, FellCloseds ↥(nondirectedBands b) :=
  fun b => FellCloseds.clip (nondirectedBands b) twoPointRecord

theorem isCompatFamily_nondirectedRecordFamily :
    FellCloseds.IsCompatFamily nondirectedBands nondirectedRecordFamily :=
  fun _ _ hij => FellCloseds.clipLE_clip hij _

/-- **Levelwise records glue to a non-record without directedness**:
the compatible family of the specimen's clips — each a singleton
record — has the two-point specimen as its glued set, which is no
record.  No proof of the gluing theorem (`glue_mem_speedLocus`) could
avoid the directedness hypothesis. -/
theorem not_isSpeedGraph_glueSet_nondirected :
    ¬ IsSpeedGraph (Prod.fst : ℝ × ℝ → ℝ) Prod.snd 1
      (FellCloseds.glueSet nondirectedRecordFamily) := by
  have heq : FellCloseds.glueSet nondirectedRecordFamily
      = (twoPointRecord : Set (ℝ × ℝ)) := by
    ext p
    simp only [FellCloseds.glueSet, nondirectedRecordFamily,
      FellCloseds.coe_clip, Subtype.image_preimage_coe, mem_iUnion,
      mem_inter_iff]
    constructor
    · rintro ⟨b, -, hp⟩
      exact hp
    · intro hp
      obtain ⟨b, hb⟩ := mem_iUnion.mp
        (iUnion_nondirectedBands ▸ mem_univ p)
      exact ⟨b, hb, hp⟩
  rw [heq]
  exact not_mem_speedLocus_twoPointRecord

end SuFunctor.Universe

#print axioms SuFunctor.Universe.tendsto_steepGraph
#print axioms SuFunctor.Universe.tendsto_steepGraphF
#print axioms SuFunctor.Universe.not_isClosed_graphLocus
#print axioms SuFunctor.Universe.not_isClosed_iUnion_speedLocus
#print axioms SuFunctor.Universe.not_directed_nondirectedBands
#print axioms SuFunctor.Universe.not_isLocalLocus_nondirected
#print axioms SuFunctor.Universe.not_isSpeedGraph_glueSet_nondirected
