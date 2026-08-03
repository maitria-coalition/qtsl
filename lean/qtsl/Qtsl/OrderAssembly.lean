import Qtsl.Discharge

/-!
# The cell-order assembly

The cell order enters the discharge theorem's hypothesis interface —
never the judgement semantics and never stored certificate data: a
partial order on the cell index joins the typeclass row, and the
recomputed combinatorial facts enter as two hypotheses, fibre convexity
and monotonicity, assembled here into the ordered discharge form.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology Filter

variable {X : Type*}

section OrbitClosed

variable [TopologicalSpace X] [T2Space X]

theorem isClosed_setOf_completeOrbit {φ : Semiflow X}
    (hflow : ∀ t, Continuous (φ.flow t)) :
    IsClosed {γ : ℝ → X | φ.CompleteOrbit γ} := by
  have hrw : {γ : ℝ → X | φ.CompleteOrbit γ} =
      ⋂ (s : ℝ) (t : ℝ≥0), {γ : ℝ → X | γ (s + t) = φ.flow t (γ s)} := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, CompleteOrbit]
  rw [hrw]
  exact isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_eq (continuous_apply _) ((hflow t).comp (continuous_apply s))

end OrbitClosed

section LimitSets

variable [TopologicalSpace X] [T2Space X]

theorem limitSet_nonempty_of_directed {γ : ℝ → X} {D : Set X}
    (hD : IsCompact D) (hr : Set.range γ ⊆ D) (S : ℝ → Set ℝ)
    (hne : ∀ T, (S T).Nonempty)
    (hdir : ∀ a b : ℝ, ∃ c, S c ⊆ S a ∧ S c ⊆ S b) :
    (⋂ T : ℝ, closure (γ '' S T)).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro a b
    obtain ⟨c, hca, hcb⟩ := hdir a b
    exact ⟨c, closure_mono (Set.image_mono hca),
      closure_mono (Set.image_mono hcb)⟩
  · exact fun T => ((hne T).image γ).closure
  · intro T
    refine hD.of_isClosed_subset isClosed_closure ?_
    calc closure (γ '' S T)
        ⊆ closure D := closure_mono ((Set.image_subset_range γ _).trans hr)
      _ = D := hD.isClosed.closure_eq
  · exact fun T => isClosed_closure

theorem omegaSet_nonempty {γ : ℝ → X} {D : Set X}
    (hD : IsCompact D) (hr : Set.range γ ⊆ D) :
    (omegaSet γ).Nonempty :=
  limitSet_nonempty_of_directed hD hr _ (fun T => ⟨T, Set.self_mem_Ici⟩)
    (fun a b => ⟨max a b, Set.Ici_subset_Ici.mpr (le_max_left a b),
      Set.Ici_subset_Ici.mpr (le_max_right a b)⟩)

theorem alphaSet_nonempty {γ : ℝ → X} {D : Set X}
    (hD : IsCompact D) (hr : Set.range γ ⊆ D) :
    (alphaSet γ).Nonempty :=
  limitSet_nonempty_of_directed hD hr _ (fun T => ⟨T, Set.self_mem_Iic⟩)
    (fun a b => ⟨min a b, Set.Iic_subset_Iic.mpr (min_le_left a b),
      Set.Iic_subset_Iic.mpr (min_le_right a b)⟩)

theorem limitSet_completeOrbit_through_of_basis {φ : Semiflow X}
    {γ : ℝ → X} {D : Set X}
    (hflow : ∀ t, Continuous (φ.flow t)) (hD : IsCompact D)
    (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ D) {y : X}
    (l : Filter ℝ) (S : ℝ → Set ℝ)
    (hSl : ∀ T, S T ∈ l)
    (hbasis : ∀ s ∈ l, ∃ T, S T ⊆ s)
    (hshift : ∀ u T : ℝ, ∃ T', ∀ s ∈ S T', u + s ∈ S T)
    (hy : ∀ T : ℝ, y ∈ closure (γ '' S T)) :
    ∃ δ : ℝ → X, φ.CompleteOrbit δ ∧ δ 0 = y ∧
      Set.range δ ⊆ ⋂ T : ℝ, closure (γ '' S T) := by
  classical

  set F : Filter ℝ := l ⊓ Filter.comap γ (𝓝 y) with hF
  have hy' : ∀ (T : ℝ) (U : Set X), U ∈ 𝓝 y → ∃ s ∈ S T, γ s ∈ U := by
    intro T U hU
    obtain ⟨x, hxU, s, hsS, rfl⟩ := mem_closure_iff_nhds.mp (hy T) U hU
    exact ⟨s, hsS, hxU⟩
  have hFne : F.NeBot := by
    rw [hF, Filter.inf_neBot_iff]
    intro s hs s' hs'
    obtain ⟨T, hT⟩ := hbasis s hs
    obtain ⟨U, hU, hUs'⟩ := Filter.mem_comap.mp hs'
    obtain ⟨t, htS, htU⟩ := hy' T U hU
    exact ⟨t, hT htS, hUs' htU⟩

  set σ : ℝ → (ℝ → X) := fun s u => γ (u + s) with hσ
  set K : Set (ℝ → X) :=
    {δ : ℝ → X | φ.CompleteOrbit δ} ∩ Set.univ.pi (fun _ : ℝ => D) with hK
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => hD).inter_left
      (isClosed_setOf_completeOrbit hflow)
  have hσK : ∀ s, σ s ∈ K := fun s =>
    ⟨horb.shift s, fun u _ => hr ⟨u + s, rfl⟩⟩
  have hle : Filter.map σ F ≤ 𝓟 K :=
    Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Filter.univ_mem' hσK))
  haveI := hFne.map σ
  obtain ⟨δ, hδK, hclust⟩ := hKc hle
  refine ⟨δ, hδK.1, ?_, ?_⟩
  ·

    have hmapcl : ClusterPt (δ 0)
        (Filter.map (fun δ' : ℝ → X => δ' 0) (Filter.map σ F)) :=
      hclust.map (continuous_apply (0 : ℝ)).continuousAt Filter.tendsto_map
    have hcomp : ((fun δ' : ℝ → X => δ' 0) ∘ σ) = γ := by
      funext s
      simp [hσ]
    rw [Filter.map_map, hcomp] at hmapcl
    have hle' : Filter.map γ F ≤ 𝓝 y :=
      le_trans (Filter.map_mono inf_le_right) Filter.map_comap_le
    exact eq_of_nhds_neBot (hmapcl.mono hle')
  ·
    rintro _ ⟨u, rfl⟩
    refine Set.mem_iInter.mpr fun T => ?_
    have hclustu : ClusterPt (δ u)
        (Filter.map (fun s => γ (u + s)) F) := by
      have h := hclust.map (continuous_apply u).continuousAt Filter.tendsto_map
      rwa [Filter.map_map] at h
    obtain ⟨T', hT'⟩ := hshift u T
    have hmem : γ '' S T ∈ Filter.map (fun s => γ (u + s)) F := by
      refine Filter.mem_map.mpr
        (Filter.mem_of_superset (Filter.mem_inf_of_left (hSl T')) ?_)
      intro s hs
      exact ⟨u + s, hT' s hs, rfl⟩
    exact mem_closure_iff_clusterPt.mpr
      (hclustu.mono (Filter.le_principal_iff.mpr hmem))

theorem omegaSet_completeOrbit_through {φ : Semiflow X} {γ : ℝ → X}
    {D : Set X} (hflow : ∀ t, Continuous (φ.flow t)) (hD : IsCompact D)
    (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ D) {y : X}
    (hy : y ∈ omegaSet γ) :
    ∃ δ : ℝ → X, φ.CompleteOrbit δ ∧ δ 0 = y ∧
      Set.range δ ⊆ omegaSet γ :=
  limitSet_completeOrbit_through_of_basis hflow hD horb hr Filter.atTop _
    (fun T => Filter.Ici_mem_atTop T)
    (fun s hs => (Filter.mem_atTop_sets.mp hs).imp
      fun T hT u hu => hT u hu)
    (fun u T => ⟨T - u, fun s hs => Set.mem_Ici.mpr
      (by linarith [Set.mem_Ici.mp hs])⟩)
    (fun T => Set.mem_iInter.mp hy T)

theorem alphaSet_completeOrbit_through {φ : Semiflow X} {γ : ℝ → X}
    {D : Set X} (hflow : ∀ t, Continuous (φ.flow t)) (hD : IsCompact D)
    (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ D) {y : X}
    (hy : y ∈ alphaSet γ) :
    ∃ δ : ℝ → X, φ.CompleteOrbit δ ∧ δ 0 = y ∧
      Set.range δ ⊆ alphaSet γ :=
  limitSet_completeOrbit_through_of_basis hflow hD horb hr Filter.atBot _
    (fun T => Filter.Iic_mem_atBot T)
    (fun s hs => (Filter.mem_atBot_sets.mp hs).imp
      fun T hT u hu => hT u hu)
    (fun u T => ⟨T - u, fun s hs => Set.mem_Iic.mpr
      (by linarith [Set.mem_Iic.mp hs])⟩)
    (fun T => Set.mem_iInter.mp hy T)

end LimitSets

theorem HasTransitCert.empty_of_orbitThrough {φ : Semiflow X}
    {C L : Set X} (h : φ.HasTransitCert C) (hLC : L ⊆ C)
    (hL : L ⊆ φ.MaxInv L) : L = ∅ := by
  rw [← Set.subset_empty_iff, ← h.maxInv_empty]
  exact hL.trans (maxInv_mono hLC)

section Assembly

variable {Vtx ι : Type*} [TopologicalSpace X] [T2Space X]
  [PartialOrder ι] [PartialOrder Vtx]

theorem orderClause_assemble (φ : Semiflow X) (D : Set X)
    (hD : IsCompact D) (hflow : ∀ t, Continuous (φ.flow t))
    (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hTransit : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hInterval : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∃ bα bω : ι, bω ≤ bα ∧
        alphaSet γ ⊆ cells bα ∧ omegaSet γ ⊆ cells bω ∧
        ∀ t : ℝ, ∃ i, bω ≤ i ∧ i ≤ bα ∧ γ t ∈ cells i) :
    ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ φ.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧
        alphaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap w) := by
  intro γ horb hr hnc
  obtain ⟨bα, bω, hbb, hα, hω, hvisit⟩ := hInterval γ horb hr

  have hαself : alphaSet γ ⊆ φ.MaxInv (alphaSet γ) := fun y hy =>
    alphaSet_completeOrbit_through hflow hD horb hr hy
  have hωself : omegaSet γ ⊆ φ.MaxInv (omegaSet γ) := fun y hy =>
    omegaSet_completeOrbit_through hflow hD horb hr hy

  have hαne : (alphaSet γ).Nonempty := alphaSet_nonempty hD hr
  have hωne : (omegaSet γ).Nonempty := omegaSet_nonempty hD hr

  have hvα : ∃ v, hmap bα = some v := by
    cases hv : hmap bα with
    | none =>
        rw [(hTransit bα hv).empty_of_orbitThrough hα hαself] at hαne
        exact absurd hαne Set.not_nonempty_empty
    | some v => exact ⟨v, rfl⟩
  have hvω : ∃ w, hmap bω = some w := by
    cases hw : hmap bω with
    | none =>
        rw [(hTransit bω hw).empty_of_orbitThrough hω hωself] at hωne
        exact absurd hωne Set.not_nonempty_empty
    | some w => exact ⟨w, rfl⟩
  obtain ⟨v, hv⟩ := hvα
  obtain ⟨w, hw⟩ := hvω
  by_cases hvw : v = w
  ·
    exfalso
    apply hnc v
    have hrfib : Set.range γ ⊆ fiberUnion cells hmap v := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨i, h1, h2, hmem⟩ := hvisit t
      have hwv : hmap bω = some v := by rw [hvw]; exact hw
      exact subset_fiberUnion (hConv bω i bα v h1 h2 hwv hv) hmem
    rintro _ ⟨t, rfl⟩
    exact mem_maxInv_of_orbit horb hrfib t
  ·
    refine ⟨v, w,
      lt_of_le_of_ne (hMono bω bα w v hbb hw hv) fun h => hvw h.symm,
      ?_, ?_⟩
    · exact hαself.trans (maxInv_mono (hα.trans (subset_fiberUnion hv)))
    · exact hωself.trans (maxInv_mono (hω.trans (subset_fiberUnion hw)))

end Assembly

section Combined

variable {Vtx ι : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [PartialOrder ι] [Finite ι]

theorem qMorseDischarge_sound_orderAssembled (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hInterval : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∃ bα bω : ι, bω ≤ bα ∧
        alphaSet γ ⊆ cells bα ∧ omegaSet γ ⊆ cells bω ∧
        ∀ t : ℝ, ∃ i, bω ≤ i ∧ i ≤ bα ∧ γ t ∈ cells i) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_modelClass φ D ρ cells hmap hflow hcells hContain
    hOverlap hCell hTransitCert
    (orderClause_assemble φ D hD hflow cells hmap hConv hMono
      hTransitCert hInterval)

end Combined

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.isClosed_setOf_completeOrbit
#print axioms Qtsl.Semiflow.limitSet_nonempty_of_directed
#print axioms Qtsl.Semiflow.omegaSet_nonempty
#print axioms Qtsl.Semiflow.alphaSet_nonempty
#print axioms Qtsl.Semiflow.limitSet_completeOrbit_through_of_basis
#print axioms Qtsl.Semiflow.omegaSet_completeOrbit_through
#print axioms Qtsl.Semiflow.alphaSet_completeOrbit_through
#print axioms Qtsl.Semiflow.HasTransitCert.empty_of_orbitThrough
#print axioms Qtsl.Semiflow.orderClause_assemble
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_orderAssembled

end PPLC
