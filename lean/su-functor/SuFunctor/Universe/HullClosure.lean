import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Binary convex hulls of probability measures are closed

On the carrier of probability measures over a complete second-countable
metric space (with the narrow topology), the two-generator convex hull of
a pair of closed sets is closed — with *no* closure operation and *no*
tightness hypothesis on the generators (`isClosed_pairHull`,
`isClosed_binaryHull`).  The mechanism has no analogue in a general
locally convex space, where two escaping sequences can converge in sum by
cancellation: on the cone of measures, positivity (`t • a ≤ t • a + s • b`
as measures), narrow continuity of total mass, and Ulam tightness of a
single limit measure together force each arm of a converging sequence of
convex combinations to converge by itself (after passing to an
ultrafilter), except where its coefficient vanishes — and a vanishing
coefficient kills its arm outright (mass control), no limit needed.

Consequently the quasiconvex coproduct of two lower semicontinuous
penalties is *levelwise exact*: its sublevel sets are exactly the binary
hulls of the sublevel unions, with no `ε`-regularization
(`iInter_binaryHull_sublevel`, `sublevel_qCoproduct_eq`).  Here the
fixed limit point manufactures its own compactness, so not even the
generators' closedness needs help.  The coproduct is the greatest
minorant of `min σ τ` among functions with convex sublevels
(`le_qCoproduct_of_forall_mixConvex`, `qCoproduct_le_min`).

The two-generator (Carathéodory-two) form is essential and honest: for
convex generators it *is* the convex hull of the union, and the finitary
case follows by iteration, while countably infinite joins genuinely
reopen the tightness question. -/

namespace SuFunctor.Universe

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-! ## Convex combinations of probability measures -/

/-- The convex combination `t • a + (1 - t) • b` of two probability
measures, for a coefficient `t ≤ 1`. -/
noncomputable def mix (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    ProbabilityMeasure X :=
  ⟨((t : ℝ≥0∞)) • (a : Measure X) + (((1 - t : ℝ≥0) : ℝ≥0∞)) • (b : Measure X), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le ht, ENNReal.coe_one]⟩

theorem mix_toMeasure (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    (mix t ht a b : Measure X)
      = ((t : ℝ≥0∞)) • (a : Measure X)
        + (((1 - t : ℝ≥0) : ℝ≥0∞)) • (b : Measure X) := rfl

theorem mix_one (a b : ProbabilityMeasure X) : mix 1 le_rfl a b = a := by
  apply Subtype.ext
  show ((1 : ℝ≥0) : ℝ≥0∞) • (a : Measure X)
      + (((1 - 1 : ℝ≥0) : ℝ≥0∞)) • (b : Measure X) = (a : Measure X)
  simp

theorem mix_zero (ht : (0 : ℝ≥0) ≤ 1) (a b : ProbabilityMeasure X) :
    mix 0 ht a b = b := by
  apply Subtype.ext
  show ((0 : ℝ≥0) : ℝ≥0∞) • (a : Measure X)
      + (((1 - 0 : ℝ≥0) : ℝ≥0∞)) • (b : Measure X) = (b : Measure X)
  simp

/-- Positivity of the cone: each arm of a convex combination is dominated
by the combination, as measures. -/
theorem smul_le_mix_left (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    ((t : ℝ≥0∞)) • (a : Measure X) ≤ (mix t ht a b : Measure X) := by
  rw [mix_toMeasure]
  exact le_add_of_nonneg_right (Measure.zero_le _)

theorem smul_le_mix_right (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    (((1 - t : ℝ≥0) : ℝ≥0∞)) • (b : Measure X) ≤ (mix t ht a b : Measure X) := by
  rw [mix_toMeasure]
  exact le_add_of_nonneg_left (Measure.zero_le _)

theorem mix_comm (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    mix t ht a b = mix (1 - t) tsub_le_self b a := by
  apply Subtype.ext
  show ((t : ℝ≥0∞)) • (a : Measure X)
      + (((1 - t : ℝ≥0) : ℝ≥0∞)) • (b : Measure X)
    = (((1 - t : ℝ≥0) : ℝ≥0∞)) • (b : Measure X)
      + (((1 - (1 - t) : ℝ≥0) : ℝ≥0∞)) • (a : Measure X)
  rw [tsub_tsub_cancel_of_le ht, add_comm]

/-! ## The two-generator hull -/

/-- The two-generator (Carathéodory-two) convex hull: all convex
combinations of a point of `C` with a point of `D`. -/
def pairHull (C D : Set (ProbabilityMeasure X)) : Set (ProbabilityMeasure X) :=
  {μ | ∃ (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X),
    a ∈ C ∧ b ∈ D ∧ mix t ht a b = μ}

/-- The binary hull, robust to empty generators: the two-generator hull
together with the generators themselves.  For nonempty convex closed
generators this is the closed convex hull of the union. -/
def binaryHull (C D : Set (ProbabilityMeasure X)) : Set (ProbabilityMeasure X) :=
  pairHull C D ∪ C ∪ D

theorem pairHull_mono {C C' D D' : Set (ProbabilityMeasure X)}
    (hC : C ⊆ C') (hD : D ⊆ D') : pairHull C D ⊆ pairHull C' D' := by
  rintro μ ⟨t, ht, a, b, ha, hb, rfl⟩
  exact ⟨t, ht, a, b, hC ha, hD hb, rfl⟩

theorem binaryHull_mono {C C' D D' : Set (ProbabilityMeasure X)}
    (hC : C ⊆ C') (hD : D ⊆ D') : binaryHull C D ⊆ binaryHull C' D' :=
  union_subset_union (union_subset_union (pairHull_mono hC hD) hC) hD

theorem subset_binaryHull_left (C D : Set (ProbabilityMeasure X)) :
    C ⊆ binaryHull C D :=
  fun _ h => Or.inl (Or.inr h)

theorem subset_binaryHull_right (C D : Set (ProbabilityMeasure X)) :
    D ⊆ binaryHull C D :=
  fun _ h => Or.inr h

/-- Mix-convexity: closure under convex combinations. -/
def MixConvex (S : Set (ProbabilityMeasure X)) : Prop :=
  ∀ (t : ℝ≥0) (ht : t ≤ 1) a b, a ∈ S → b ∈ S → mix t ht a b ∈ S

/-- The two-generator hull is below every mix-convex superset of the
generators: it is one convex-combination step, so any convex set
containing both generators absorbs it. -/
theorem pairHull_subset_of_mixConvex {C D S : Set (ProbabilityMeasure X)}
    (hS : MixConvex S) (hC : C ⊆ S) (hD : D ⊆ S) : pairHull C D ⊆ S := by
  rintro μ ⟨t, ht, a, b, ha, hb, rfl⟩
  exact hS t ht a b (hC ha) (hD hb)

theorem binaryHull_subset_of_mixConvex {C D S : Set (ProbabilityMeasure X)}
    (hS : MixConvex S) (hC : C ⊆ S) (hD : D ⊆ S) : binaryHull C D ⊆ S :=
  union_subset (union_subset (pairHull_subset_of_mixConvex hS hC hD) hC) hD

theorem pairHull_comm (C D : Set (ProbabilityMeasure X)) :
    pairHull C D = pairHull D C := by
  ext μ
  constructor <;> rintro ⟨t, ht, a, b, ha, hb, rfl⟩
  · exact ⟨1 - t, tsub_le_self, b, a, hb, ha, (mix_comm t ht a b).symm⟩
  · exact ⟨1 - t, tsub_le_self, b, a, hb, ha, (mix_comm t ht a b).symm⟩

/-! ## Tightness bookkeeping -/

section Tight

variable [TopologicalSpace X]

/-- Tightness passes from a family of measures to arms it dominates
after scaling by coefficients bounded away from zero. -/
theorem isTightMeasureSet_of_forall_smul_le {ι : Type*}
    {x a : ι → ProbabilityMeasure X} {t : ι → ℝ≥0} {T : Set ι} {t₀ : ℝ≥0}
    (ht₀ : 0 < t₀) (hbound : ∀ i ∈ T, t₀ ≤ t i)
    (hle : ∀ i ∈ T, ((t i : ℝ≥0∞)) • (a i : Measure X) ≤ (x i : Measure X))
    (hx : IsTightMeasureSet {m | ∃ i, ((x i : ProbabilityMeasure X) : Measure X) = m}) :
    IsTightMeasureSet {m | ∃ i ∈ T, ((a i : ProbabilityMeasure X) : Measure X) = m} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hx ⊢
  intro ε hε
  have hε' : 0 < (t₀ : ℝ≥0∞) * ε :=
    ENNReal.mul_pos (by exact_mod_cast ht₀.ne') hε.ne'
  obtain ⟨K, hK, hKx⟩ := hx _ hε'
  refine ⟨K, hK, ?_⟩
  rintro m ⟨i, hiT, rfl⟩
  have h1 : (t₀ : ℝ≥0∞) * (a i : Measure X) Kᶜ
      ≤ (t i : ℝ≥0∞) * (a i : Measure X) Kᶜ :=
    mul_le_mul_left (by exact_mod_cast hbound i hiT) _
  have h2 : (t i : ℝ≥0∞) * (a i : Measure X) Kᶜ ≤ (x i : Measure X) Kᶜ := by
    have := hle i hiT
    simpa [Measure.smul_apply, smul_eq_mul] using this Kᶜ
  have h3 : (t₀ : ℝ≥0∞) * (a i : Measure X) Kᶜ ≤ (t₀ : ℝ≥0∞) * ε :=
    (h1.trans h2).trans (hKx _ ⟨i, rfl⟩)
  exact (ENNReal.mul_le_mul_iff_right
    (by exact_mod_cast ht₀.ne') ENNReal.coe_ne_top).mp h3

end Tight

/-! ## The extraction lemma and the closure theorem -/

section Polish

variable [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X]
  [BorelSpace X]

/-- A narrowly convergent sequence of probability measures is uniformly
tight, together with its limit (Ulam's theorem plus the converse
direction of Prokhorov's theorem). -/
theorem isTightMeasureSet_range_of_tendsto
    {x : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hx : Tendsto x atTop (𝓝 μ)) :
    IsTightMeasureSet {m | ∃ k, ((x k : ProbabilityMeasure X) : Measure X) = m} := by
  have hcof : Tendsto x cofinite (𝓝 μ) := by
    rwa [Nat.cofinite_eq_atTop]
  have hcomp : IsCompact (insert μ (Set.range x)) :=
    hcof.isCompact_insert_range_of_cofinite
  have hclos : IsCompact (closure (Set.range x)) :=
    hcomp.of_isClosed_subset isClosed_closure
      (closure_minimal (subset_insert _ _) hcomp.isClosed)
  have := isTightMeasureSet_of_isCompact_closure hclos
  convert this using 1
  ext m
  simp [Set.range]

omit [SecondCountableTopology X] [CompleteSpace X] in
/-- Extraction along an ultrafilter: a family of probability measures,
uniformly tight on an ultrafilter-large index set, converges along the
ultrafilter. -/
theorem exists_tendsto_of_tight {a : ℕ → ProbabilityMeasure X}
    (U : Ultrafilter ℕ) {T : Set ℕ} (hT : T ∈ U)
    (htight : IsTightMeasureSet
      {m | ∃ k ∈ T, ((a k : ProbabilityMeasure X) : Measure X) = m}) :
    ∃ α, Tendsto a (U : Filter ℕ) (𝓝 α) := by
  have himg : IsTightMeasureSet
      {m | ∃ ν ∈ a '' T, ((ν : ProbabilityMeasure X) : Measure X) = m} := by
    convert htight using 1
    ext m
    constructor
    · rintro ⟨ν, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨a k, ⟨k, hk, rfl⟩, rfl⟩
  have hclos : IsCompact (closure (a '' T)) :=
    isCompact_closure_of_isTightMeasureSet himg
  have hmem : closure (a '' T) ∈ U.map a :=
    Filter.mem_map.mpr (U.sets_of_superset hT
      fun k hk => subset_closure ⟨k, hk, rfl⟩)
  obtain ⟨α, -, hα⟩ := hclos.ultrafilter_le_nhds' (U.map a) hmem
  exact ⟨α, hα⟩

omit [SecondCountableTopology X] [CompleteSpace X] in
/-- The ultrafilter limit of a family contained in a closed set lies in
the set. -/
theorem mem_of_tendsto_ultrafilter {S : Set (ProbabilityMeasure X)}
    (hS : IsClosed S) {a : ℕ → ProbabilityMeasure X} (haS : ∀ k, a k ∈ S)
    (U : Ultrafilter ℕ) {α : ProbabilityMeasure X}
    (hα : Tendsto a (U : Filter ℕ) (𝓝 α)) : α ∈ S := by
  rw [← hS.closure_eq]
  exact mem_closure_iff_ultrafilter.mpr
    ⟨U.map a, Filter.mem_map.mpr (univ_mem' haS), hα⟩

omit [SecondCountableTopology X] [CompleteSpace X] in
/-- Vanishing coefficient kills its arm: if the coefficients tend to `0`
along the filter, the scaled finite measures tend to `0`. -/
theorem tendsto_smul_toFiniteMeasure_zero {ι : Type*} {l : Filter ι}
    {t : ι → ℝ≥0} (htt : Tendsto t l (𝓝 0)) (b : ι → ProbabilityMeasure X) :
    Tendsto (fun i => t i • (b i).toFiniteMeasure) l (𝓝 0) := by
  apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
  have hmass : ∀ i, (t i • (b i).toFiniteMeasure).mass = t i := by
    intro i
    simp [FiniteMeasure.mass]
  simpa only [hmass] using htt

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
/-- The decomposition of a mix on the finite-measure side.  (Both sides
carry the same underlying measure: the `ℝ≥0`-action on measures is
definitionally the coerced `ℝ≥0∞`-action.) -/
theorem mix_toFiniteMeasure (t : ℝ≥0) (ht : t ≤ 1) (a b : ProbabilityMeasure X) :
    (mix t ht a b).toFiniteMeasure
      = t • a.toFiniteMeasure + (1 - t) • b.toFiniteMeasure :=
  rfl

/-- **Binary hulls of closed sets of probability measures are narrowly
closed.**  No convexity, tightness, or compactness hypotheses on the
generators: the only compactness in the proof is conjured from the
convergent sequence itself via Prokhorov, and positivity of the cone
passes it to the arms. -/
theorem isClosed_pairHull {C D : Set (ProbabilityMeasure X)}
    (hC : IsClosed C) (hD : IsClosed D) : IsClosed (pairHull C D) := by
  refine IsSeqClosed.isClosed ?_
  intro x μ hx hlim
  choose t ht a b ha hb hmix using hx
  set U : Ultrafilter ℕ := Ultrafilter.of atTop with hU
  have hUle : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hxU : Tendsto x (U : Filter ℕ) (𝓝 μ) := hlim.mono_left hUle
  -- coefficient limit along the ultrafilter
  have hIcc : Icc (0 : ℝ≥0) 1 ∈ U.map t :=
    Filter.mem_map.mpr (U.sets_of_superset univ_mem
      fun k _ => ⟨zero_le, ht k⟩)
  obtain ⟨τ, hτmem, hτ⟩ :=
    (isCompact_Icc (a := (0 : ℝ≥0)) (b := 1)).ultrafilter_le_nhds' (U.map t) hIcc
  have hτle : Tendsto t (U : Filter ℕ) (𝓝 τ) := hτ
  -- tightness of the convergent sequence
  have htightx : IsTightMeasureSet
      {m | ∃ k, ((x k : ProbabilityMeasure X) : Measure X) = m} :=
    isTightMeasureSet_range_of_tendsto hlim
  -- the a-arm dominations
  have hlea : ∀ k, ((t k : ℝ≥0∞)) • (a k : Measure X) ≤ (x k : Measure X) := by
    intro k
    rw [← hmix k]
    exact smul_le_mix_left _ _ _ _
  have hleb : ∀ k, (((1 - t k : ℝ≥0) : ℝ≥0∞)) • (b k : Measure X)
      ≤ (x k : Measure X) := by
    intro k
    rw [← hmix k]
    exact smul_le_mix_right _ _ _ _
  -- convergence of the finite-measure decomposition, given arm limits
  have hsub : Tendsto (fun k => (1 - t k : ℝ≥0)) (U : Filter ℕ) (𝓝 (1 - τ)) :=
    Tendsto.sub tendsto_const_nhds hτle
  -- case split on the limiting coefficient
  have hxfin : ∀ k, (x k).toFiniteMeasure
      = t k • (a k).toFiniteMeasure + (1 - t k) • (b k).toFiniteMeasure := by
    intro k
    rw [← hmix k, mix_toFiniteMeasure]
  rcases eq_or_ne τ 0 with rfl | hτ0
  · -- the a-arm vanishes; the b-arm carries the limit
    rw [tsub_zero] at hsub
    have hTb : {k | (1 : ℝ≥0) / 2 ≤ 1 - t k} ∈ U :=
      (hsub.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (by norm_num : (1 : ℝ≥0) / 2 < 1)))).mono
        fun k hk => le_of_lt hk
    obtain ⟨β, hβ⟩ := exists_tendsto_of_tight U hTb
      (isTightMeasureSet_of_forall_smul_le (by norm_num : (0 : ℝ≥0) < 1 / 2)
        (fun k hk => hk) (fun k _ => hleb k) htightx)
    have hβD : β ∈ D := mem_of_tendsto_ultrafilter hD hb U hβ
    have hxβ : Tendsto x (U : Filter ℕ) (𝓝 β) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have h1 : Tendsto (fun k => t k • (a k).toFiniteMeasure)
          (U : Filter ℕ) (𝓝 0) :=
        tendsto_smul_toFiniteMeasure_zero hτle a
      have hβfin :=
        (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
          (U : Filter ℕ)).mp hβ
      have hsum : Tendsto (fun k => t k • (a k).toFiniteMeasure
          + (1 - t k) • (b k).toFiniteMeasure) (U : Filter ℕ)
          (𝓝 β.toFiniteMeasure) := by
        have h := h1.add (hsub.smul hβfin)
        simpa using h
      exact Tendsto.congr (fun k => (hxfin k).symm) hsum
    have hμβ : μ = β := tendsto_nhds_unique hxU hxβ
    exact ⟨0, zero_le_one, a 0, β, ha 0, hβD, by rw [mix_zero]; exact hμβ.symm⟩
  rcases eq_or_ne τ 1 with rfl | hτ1
  · -- the b-arm vanishes; the a-arm carries the limit
    have hTa : {k | (1 : ℝ≥0) / 2 ≤ t k} ∈ U :=
      (hτle.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (by norm_num : (1 : ℝ≥0) / 2 < 1)))).mono
        fun k hk => le_of_lt hk
    obtain ⟨α, hα⟩ := exists_tendsto_of_tight U hTa
      (isTightMeasureSet_of_forall_smul_le (by norm_num : (0 : ℝ≥0) < 1 / 2)
        (fun k hk => hk) (fun k _ => hlea k) htightx)
    have hαC : α ∈ C := mem_of_tendsto_ultrafilter hC ha U hα
    have hsub0 : Tendsto (fun k => (1 - t k : ℝ≥0)) (U : Filter ℕ) (𝓝 0) := by
      simpa using hsub
    have hxα : Tendsto x (U : Filter ℕ) (𝓝 α) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have hαfin :=
        (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
          (U : Filter ℕ)).mp hα
      have hsum : Tendsto (fun k => t k • (a k).toFiniteMeasure
          + (1 - t k) • (b k).toFiniteMeasure) (U : Filter ℕ)
          (𝓝 α.toFiniteMeasure) := by
        have h := (hτle.smul hαfin).add
          (tendsto_smul_toFiniteMeasure_zero hsub0 b)
        simpa using h
      exact Tendsto.congr (fun k => (hxfin k).symm) hsum
    have hμα : μ = α := tendsto_nhds_unique hxU hxα
    exact ⟨1, le_rfl, α, b 0, hαC, hb 0, by rw [mix_one]; exact hμα.symm⟩
  · -- both arms converge
    have hτpos : 0 < τ := pos_iff_ne_zero.mpr hτ0
    have hτlt1 : τ < 1 := lt_of_le_of_ne hτmem.2 hτ1
    have hTa : {k | τ / 2 ≤ t k} ∈ U :=
      (hτle.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (half_lt_self hτpos)))).mono fun k hk => le_of_lt hk
    have hTb : {k | (1 - τ) / 2 ≤ 1 - t k} ∈ U :=
      (hsub.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (half_lt_self (tsub_pos_of_lt hτlt1))))).mono
        fun k hk => le_of_lt hk
    obtain ⟨α, hα⟩ := exists_tendsto_of_tight U hTa
      (isTightMeasureSet_of_forall_smul_le (half_pos hτpos)
        (fun k hk => hk) (fun k _ => hlea k) htightx)
    obtain ⟨β, hβ⟩ := exists_tendsto_of_tight U hTb
      (isTightMeasureSet_of_forall_smul_le (half_pos (tsub_pos_of_lt hτlt1))
        (fun k hk => hk) (fun k _ => hleb k) htightx)
    have hαC : α ∈ C := mem_of_tendsto_ultrafilter hC ha U hα
    have hβD : β ∈ D := mem_of_tendsto_ultrafilter hD hb U hβ
    have hτle1 : τ ≤ 1 := hτmem.2
    have hxmix : Tendsto x (U : Filter ℕ) (𝓝 (mix τ hτle1 α β)) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have hαfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hα
      have hβfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hβ
      have hsum : Tendsto (fun k => t k • (a k).toFiniteMeasure
          + (1 - t k) • (b k).toFiniteMeasure) (U : Filter ℕ)
          (𝓝 ((mix τ hτle1 α β).toFiniteMeasure)) := by
        rw [mix_toFiniteMeasure]
        exact (hτle.smul hαfin).add (hsub.smul hβfin)
      exact Tendsto.congr (fun k => (hxfin k).symm) hsum
    have hμ : μ = mix τ hτle1 α β := tendsto_nhds_unique hxU hxmix
    exact ⟨τ, hτle1, α, β, hαC, hβD, hμ.symm⟩

/-- The binary hull of closed sets is closed. -/
theorem isClosed_binaryHull {C D : Set (ProbabilityMeasure X)}
    (hC : IsClosed C) (hD : IsClosed D) : IsClosed (binaryHull C D) :=
  ((isClosed_pairHull hC hD).union hC).union hD

/-! ## Levelwise exactness of the quasiconvex coproduct -/

/-- **Right-continuity of the level hulls — no `ε`-regularization.**  For
lower semicontinuous penalties, the intersection of the binary hulls of
the `(c + ε)`-sublevels over `ε > 0` is exactly the binary hull of the
`c`-sublevels: the fixed measure in the intersection manufactures its own
compactness (Ulam), and positivity passes it to the arms of its
decompositions.  Not even closedness of the generators is consumed. -/
theorem iInter_binaryHull_sublevel {σ τ' : ProbabilityMeasure X → ℝ≥0∞}
    (hσ : LowerSemicontinuous σ) (hτ' : LowerSemicontinuous τ') (c : ℝ≥0∞) :
    ⋂ ε ∈ {ε : ℝ≥0∞ | 0 < ε}, binaryHull {ν | σ ν ≤ c + ε} {ν | τ' ν ≤ c + ε}
      = binaryHull {ν | σ ν ≤ c} {ν | τ' ν ≤ c} := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · have hconst : ∀ ε : ℝ≥0∞, (⊤ : ℝ≥0∞) + ε = ⊤ := fun ε => top_add ε
    simp only [hconst]
    exact Set.biInter_const ⟨1, one_pos⟩ _
  refine subset_antisymm ?_ ?_
  swap
  · intro μ hμ
    refine Set.mem_iInter₂.mpr fun ε _ => ?_
    exact binaryHull_mono
      (fun ν hν => le_trans (show σ ν ≤ c from hν) le_self_add)
      (fun ν hν => le_trans (show τ' ν ≤ c from hν) le_self_add) hμ
  intro μ hμ
  -- the decompositions at level c + 1/(k+1)
  have hmem : ∀ k : ℕ, μ ∈ binaryHull {ν | σ ν ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹}
      {ν | τ' ν ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹} := by
    intro k
    exact Set.mem_iInter₂.mp hμ _
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _))
  set U : Ultrafilter ℕ := Ultrafilter.of atTop with hU
  have hUle : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  -- the vanishing modulus
  have h0 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have htop : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)) atTop (𝓝 ⊤) := by
      have h := ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using h
    simpa using tendsto_inv_iff.2 htop
  have hεlim : Tendsto (fun k : ℕ => c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹)
      (U : Filter ℕ) (𝓝 c) := by
    have := Tendsto.add (tendsto_const_nhds (x := c)) h0
    simpa using this.mono_left hUle
  -- a fixed value dominated by every level of the modulus is ≤ c
  have hval : ∀ {v : ℝ≥0∞},
      {k : ℕ | v ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹} ∈ U → v ≤ c := by
    intro v hv
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hE : {k : ℕ | ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ (ε : ℝ≥0∞)} ∈ (U : Filter ℕ) := by
      apply hUle
      have hεpos : (0 : ℝ≥0∞) ∈ Iio (ε : ℝ≥0∞) := by
        simpa using (ENNReal.coe_pos.mpr hε)
      exact (h0.eventually (isOpen_Iio.mem_nhds hεpos)).mono
        fun k hk => le_of_lt hk
    obtain ⟨k, hk1, hk2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hv hE)
    exact hk1.trans (add_le_add le_rfl hk2)
  -- the three membership cases split along the ultrafilter
  set A : Set ℕ := {k | μ ∈ pairHull {ν | σ ν ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹}
    {ν | τ' ν ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹}} with hA_def
  set B₁ : Set ℕ := {k | σ μ ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹} with hB₁_def
  set B₂ : Set ℕ := {k | τ' μ ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹} with hB₂_def
  have hcover : A ∪ (B₁ ∪ B₂) ∈ U := by
    refine U.sets_of_superset univ_mem fun k _ => ?_
    rcases hmem k with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases Ultrafilter.union_mem_iff.mp hcover with hA | hB
  swap
  · rcases Ultrafilter.union_mem_iff.mp hB with hB₁ | hB₂
    · exact subset_binaryHull_left _ _ (hval hB₁)
    · exact subset_binaryHull_right _ _ (hval hB₂)
  -- decompositions on the ultrafilter-large set
  have hdec : ∀ k : ℕ, ∃ (tt : ℝ≥0) (htt : tt ≤ 1) (aa bb : ProbabilityMeasure X),
      k ∈ A → σ aa ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
        ∧ τ' bb ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ∧ mix tt htt aa bb = μ := by
    intro k
    by_cases hk : k ∈ A
    · obtain ⟨tt, htt, aa, bb, h1, h2, h3⟩ := hk
      exact ⟨tt, htt, aa, bb, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, le_rfl, μ, μ, fun h => absurd h hk⟩
  choose t ht a b hprop using hdec
  -- the constant sequence at the fixed limit measure is tight (Ulam)
  have htightμ : IsTightMeasureSet
      {m | ∃ k : ℕ, (((fun _ : ℕ => μ) k : ProbabilityMeasure X) : Measure X) = m} :=
    isTightMeasureSet_range_of_tendsto (tendsto_const_nhds (x := μ))
  have hlea : ∀ k ∈ A, ((t k : ℝ≥0∞)) • (a k : Measure X)
      ≤ (((fun _ : ℕ => μ) k : ProbabilityMeasure X) : Measure X) := by
    intro k hk
    show ((t k : ℝ≥0∞)) • (a k : Measure X) ≤ (μ : Measure X)
    rw [← (hprop k hk).2.2]
    exact smul_le_mix_left _ _ _ _
  have hleb : ∀ k ∈ A, (((1 - t k : ℝ≥0) : ℝ≥0∞)) • (b k : Measure X)
      ≤ (((fun _ : ℕ => μ) k : ProbabilityMeasure X) : Measure X) := by
    intro k hk
    show (((1 - t k : ℝ≥0) : ℝ≥0∞)) • (b k : Measure X) ≤ (μ : Measure X)
    rw [← (hprop k hk).2.2]
    exact smul_le_mix_right _ _ _ _
  -- coefficient limit along the ultrafilter
  have hIcc : Icc (0 : ℝ≥0) 1 ∈ U.map t :=
    Filter.mem_map.mpr (U.sets_of_superset univ_mem fun k _ => ⟨zero_le, ht k⟩)
  obtain ⟨τ, hτmem, hτ⟩ :=
    (isCompact_Icc (a := (0 : ℝ≥0)) (b := 1)).ultrafilter_le_nhds' (U.map t) hIcc
  have hτle : Tendsto t (U : Filter ℕ) (𝓝 τ) := hτ
  have hsub : Tendsto (fun k => (1 - t k : ℝ≥0)) (U : Filter ℕ) (𝓝 (1 - τ)) :=
    Tendsto.sub tendsto_const_nhds hτle
  -- lsc bound for an ultrafilter limit of the a-arm
  have hlscbound : ∀ {f : ProbabilityMeasure X → ℝ≥0∞},
      LowerSemicontinuous f →
      ∀ {y : ℕ → ProbabilityMeasure X} {γ : ProbabilityMeasure X},
      Tendsto y (U : Filter ℕ) (𝓝 γ) →
      (∀ᶠ k in (U : Filter ℕ), f (y k) ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) →
      f γ ≤ c := by
    intro f hf y γ hy hbound
    have hy' : (U : Filter ℕ).map y ≤ 𝓝 γ := hy
    calc f γ ≤ (𝓝 γ).liminf f := hf.le_liminf γ
      _ ≤ ((U : Filter ℕ).map y).liminf f :=
          Filter.liminf_le_liminf_of_le hy'
      _ = (U : Filter ℕ).liminf (f ∘ y) :=
          (Filter.liminf_comp f y _).symm
      _ ≤ (U : Filter ℕ).liminf (fun k => c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) :=
          Filter.liminf_le_liminf hbound
      _ = c := hεlim.liminf_eq
  -- the finite-measure decomposition of the constant sequence, eventually
  have hxfin : ∀ᶠ k in (U : Filter ℕ), μ.toFiniteMeasure
      = t k • (a k).toFiniteMeasure + (1 - t k) • (b k).toFiniteMeasure := by
    filter_upwards [hA] with k hk
    rw [show μ = mix (t k) (ht k) (a k) (b k) from ((hprop k hk).2.2).symm,
      mix_toFiniteMeasure]
  have hbounda : ∀ᶠ k in (U : Filter ℕ),
      σ (a k) ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    filter_upwards [hA] with k hk
    exact (hprop k hk).1
  have hboundb : ∀ᶠ k in (U : Filter ℕ),
      τ' (b k) ≤ c + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    filter_upwards [hA] with k hk
    exact (hprop k hk).2.1
  -- case split on the limiting coefficient
  rcases eq_or_ne τ 0 with rfl | hτ0
  · -- the b-arm carries the fixed measure
    rw [tsub_zero] at hsub
    have hTb : {k | (1 : ℝ≥0) / 2 ≤ 1 - t k} ∈ U :=
      (hsub.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (by norm_num : (1 : ℝ≥0) / 2 < 1)))).mono
        fun k hk => le_of_lt hk
    obtain ⟨β, hβ⟩ := exists_tendsto_of_tight U (Filter.inter_mem hA hTb)
      (isTightMeasureSet_of_forall_smul_le (by norm_num : (0 : ℝ≥0) < 1 / 2)
        (fun k hk => hk.2) (fun k hk => hleb k hk.1) htightμ)
    have hτ'β : τ' β ≤ c := hlscbound hτ' hβ hboundb
    have hxβ : Tendsto (fun _ : ℕ => μ) (U : Filter ℕ) (𝓝 β) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have h1 : Tendsto (fun k => t k • (a k).toFiniteMeasure)
          (U : Filter ℕ) (𝓝 0) :=
        tendsto_smul_toFiniteMeasure_zero hτle a
      have hβfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hβ
      have h2 : Tendsto (fun k => (1 - t k) • (b k).toFiniteMeasure)
          (U : Filter ℕ) (𝓝 ((1 : ℝ≥0) • β.toFiniteMeasure)) := by
        have := hsub.smul hβfin
        simpa using this
      have hsum := h1.add h2
      refine Tendsto.congr' ?_ (by simpa using hsum)
      filter_upwards [hxfin] with k hk
      exact hk.symm
    have hμβ : μ = β :=
      tendsto_nhds_unique (tendsto_const_nhds (x := μ)) hxβ
    exact subset_binaryHull_right _ _ (by rw [hμβ]; exact hτ'β)
  rcases eq_or_ne τ 1 with rfl | hτ1
  · -- the a-arm carries the fixed measure
    have hTa : {k | (1 : ℝ≥0) / 2 ≤ t k} ∈ U :=
      (hτle.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (by norm_num : (1 : ℝ≥0) / 2 < 1)))).mono
        fun k hk => le_of_lt hk
    obtain ⟨α, hα⟩ := exists_tendsto_of_tight U (Filter.inter_mem hA hTa)
      (isTightMeasureSet_of_forall_smul_le (by norm_num : (0 : ℝ≥0) < 1 / 2)
        (fun k hk => hk.2) (fun k hk => hlea k hk.1) htightμ)
    have hσα : σ α ≤ c := hlscbound hσ hα hbounda
    have hsub0 : Tendsto (fun k => (1 - t k : ℝ≥0)) (U : Filter ℕ) (𝓝 0) := by
      simpa using hsub
    have hxα : Tendsto (fun _ : ℕ => μ) (U : Filter ℕ) (𝓝 α) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have hαfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hα
      have h1 : Tendsto (fun k => t k • (a k).toFiniteMeasure)
          (U : Filter ℕ) (𝓝 ((1 : ℝ≥0) • α.toFiniteMeasure)) :=
        hτle.smul hαfin
      have h2 : Tendsto (fun k => (1 - t k) • (b k).toFiniteMeasure)
          (U : Filter ℕ) (𝓝 0) :=
        tendsto_smul_toFiniteMeasure_zero hsub0 b
      have hsum := h1.add h2
      refine Tendsto.congr' ?_ (by simpa using hsum)
      filter_upwards [hxfin] with k hk
      exact hk.symm
    have hμα : μ = α :=
      tendsto_nhds_unique (tendsto_const_nhds (x := μ)) hxα
    exact subset_binaryHull_left _ _ (by rw [hμα]; exact hσα)
  · -- both arms converge; the fixed measure is their mix
    have hτpos : 0 < τ := pos_iff_ne_zero.mpr hτ0
    have hτlt1 : τ < 1 := lt_of_le_of_ne hτmem.2 hτ1
    have hTa : {k | τ / 2 ≤ t k} ∈ U :=
      (hτle.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (half_lt_self hτpos)))).mono fun k hk => le_of_lt hk
    have hTb : {k | (1 - τ) / 2 ≤ 1 - t k} ∈ U :=
      (hsub.eventually (isOpen_Ioi.mem_nhds
        (Set.mem_Ioi.mpr (half_lt_self (tsub_pos_of_lt hτlt1))))).mono
        fun k hk => le_of_lt hk
    obtain ⟨α, hα⟩ := exists_tendsto_of_tight U (Filter.inter_mem hA hTa)
      (isTightMeasureSet_of_forall_smul_le (half_pos hτpos)
        (fun k hk => hk.2) (fun k hk => hlea k hk.1) htightμ)
    obtain ⟨β, hβ⟩ := exists_tendsto_of_tight U (Filter.inter_mem hA hTb)
      (isTightMeasureSet_of_forall_smul_le
        (half_pos (tsub_pos_of_lt hτlt1))
        (fun k hk => hk.2) (fun k hk => hleb k hk.1) htightμ)
    have hσα : σ α ≤ c := hlscbound hσ hα hbounda
    have hτ'β : τ' β ≤ c := hlscbound hτ' hβ hboundb
    have hτle1 : τ ≤ 1 := hτmem.2
    have hxmix : Tendsto (fun _ : ℕ => μ) (U : Filter ℕ)
        (𝓝 (mix τ hτle1 α β)) := by
      rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
      have hαfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hα
      have hβfin := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (U : Filter ℕ)).mp hβ
      have hsum := (hτle.smul hαfin).add (hsub.smul hβfin)
      rw [show (mix τ hτle1 α β).toFiniteMeasure
        = τ • α.toFiniteMeasure + (1 - τ) • β.toFiniteMeasure
        from mix_toFiniteMeasure τ hτle1 α β]
      refine Tendsto.congr' ?_ hsum
      filter_upwards [hxfin] with k hk
      exact hk.symm
    have hμ : μ = mix τ hτle1 α β :=
      tendsto_nhds_unique (tendsto_const_nhds (x := μ)) hxmix
    exact Or.inl (Or.inl ⟨τ, hτle1, α, β, hσα, hτ'β, hμ.symm⟩)

/-! ## The quasiconvex coproduct -/

/-- The `∨`-coproduct of two penalties in the quasiconvex universe: the
level of the cheapest binary hull containing the argument. -/
noncomputable def qCoproduct (σ τ' : ProbabilityMeasure X → ℝ≥0∞)
    (μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨅ (c : ℝ≥0∞) (_ : μ ∈ binaryHull {ν | σ ν ≤ c} {ν | τ' ν ≤ c}), c

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
/-- The coproduct is bounded by the level of any binary hull containing
its argument. -/
theorem qCoproduct_le_of_mem {σ τ' : ProbabilityMeasure X → ℝ≥0∞}
    {μ : ProbabilityMeasure X} {c : ℝ≥0∞}
    (h : μ ∈ binaryHull {ν | σ ν ≤ c} {ν | τ' ν ≤ c}) :
    qCoproduct σ τ' μ ≤ c := by
  rw [qCoproduct]
  exact iInf₂_le c h

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
theorem qCoproduct_le_left (σ τ' : ProbabilityMeasure X → ℝ≥0∞)
    (μ : ProbabilityMeasure X) : qCoproduct σ τ' μ ≤ σ μ :=
  qCoproduct_le_of_mem
    (subset_binaryHull_left _ _ (show σ μ ≤ σ μ from le_rfl))

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
theorem qCoproduct_le_right (σ τ' : ProbabilityMeasure X → ℝ≥0∞)
    (μ : ProbabilityMeasure X) : qCoproduct σ τ' μ ≤ τ' μ :=
  qCoproduct_le_of_mem
    (subset_binaryHull_right _ _ (show τ' μ ≤ τ' μ from le_rfl))

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
theorem qCoproduct_le_min (σ τ' : ProbabilityMeasure X → ℝ≥0∞)
    (μ : ProbabilityMeasure X) : qCoproduct σ τ' μ ≤ min (σ μ) (τ' μ) :=
  le_min (qCoproduct_le_left σ τ' μ) (qCoproduct_le_right σ τ' μ)

omit [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X] [BorelSpace X] in
/-- Greatestness: any minorant of both penalties with mix-convex
sublevels is below the coproduct. -/
theorem le_qCoproduct_of_forall_mixConvex {σ τ' h : ProbabilityMeasure X → ℝ≥0∞}
    (hqc : ∀ c, MixConvex {ν | h ν ≤ c}) (h1 : ∀ ν, h ν ≤ σ ν)
    (h2 : ∀ ν, h ν ≤ τ' ν) (μ : ProbabilityMeasure X) :
    h μ ≤ qCoproduct σ τ' μ := by
  rw [qCoproduct]
  refine le_iInf₂ fun c hc => ?_
  have hsub : binaryHull {ν | σ ν ≤ c} {ν | τ' ν ≤ c} ⊆ {ν | h ν ≤ c} :=
    binaryHull_subset_of_mixConvex (hqc c)
      (fun ν hν => (h1 ν).trans hν) (fun ν hν => (h2 ν).trans hν)
  exact hsub hc

/-- **Levelwise exactness of the quasiconvex coproduct** on the
probability carrier over a complete second-countable metric space: the
sublevel sets of the coproduct of two lower semicontinuous penalties are
exactly the binary hulls of the sublevels — plain hulls, no closure
operation, no `ε`-regularization. -/
theorem sublevel_qCoproduct_eq {σ τ' : ProbabilityMeasure X → ℝ≥0∞}
    (hσ : LowerSemicontinuous σ) (hτ' : LowerSemicontinuous τ') (c : ℝ≥0∞) :
    {μ | qCoproduct σ τ' μ ≤ c}
      = binaryHull {ν | σ ν ≤ c} {ν | τ' ν ≤ c} := by
  ext μ
  constructor
  · intro hμ
    rw [← iInter_binaryHull_sublevel hσ hτ' c]
    refine Set.mem_iInter₂.mpr fun ε (hε : (0 : ℝ≥0∞) < ε) => ?_
    rcases eq_or_ne c ⊤ with rfl | hc
    · rw [top_add]
      exact subset_binaryHull_left _ _ (by simp)
    · have hlt : qCoproduct σ τ' μ < c + ε :=
        lt_of_le_of_lt hμ (ENNReal.lt_add_right hc hε.ne')
      rw [qCoproduct] at hlt
      obtain ⟨c', hc'⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hmem', hlt'⟩ := iInf_lt_iff.mp hc'
      exact binaryHull_mono (fun ν hν => hν.trans hlt'.le)
        (fun ν hν => hν.trans hlt'.le) hmem'
  · intro hμ
    exact qCoproduct_le_of_mem hμ

end Polish

end SuFunctor.Universe
