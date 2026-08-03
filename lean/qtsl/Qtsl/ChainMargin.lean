import Qtsl.ChainRecurrence
import Qtsl.GridGeometry

/-!
# Certified facet rows imply a chain margin

The bridge from per-facet integrated growth rows to the `ChainMargin`
interface consumed by the chain-recurrence development: the same row
data that serves the facet-row certificates, plus one geometric graze
clause, yields the margin — so the chain-recurrence cover rests on
checker-shaped data throughout.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology Filter

variable {X : Type*}

section MarginRows

variable [TopologicalSpace X]

def HasMarginRows (φ : Semiflow X) (D N : Set X) : Prop :=
  ∃ (n : ℕ) (ℓ : Fin n → X → ℝ) (ε : Fin n → ℝ) (F : Fin n → Set X),
    (∀ i, 0 < ε i) ∧
    (∀ i, ∀ x ∈ F i, ∀ t : ℝ≥0, (∀ s ≤ t, φ.flow s x ∈ F i) →
      ℓ i x + ε i * (t : ℝ) ≤ ℓ i (φ.flow t x)) ∧
    ∀ p ∈ N, p ∈ closure (D \ N) →
      ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 p ∧
        (∀ i ∈ A, ℓ i p = 0 ∧ F i ∈ 𝓝 p) ∧
        ∀ q ∈ U, q ∈ N → ∃ i ∈ A, 0 ≤ ℓ i q

end MarginRows

section Bridge

variable [PseudoMetricSpace X]

theorem HasMarginRows.flow_notMem_closure {φ : Semiflow X} {D N : Set X}
    (h : φ.HasMarginRows D N) (hInv : φ.Invariant N)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    {T : ℝ≥0} (hT : 0 < T) {y : X} (hy : y ∈ N) :
    φ.flow T y ∉ closure (D \ N) := by
  obtain ⟨n, ℓ, ε, F, hε, hrow, hgraze⟩ := h
  intro hcl
  have hpN : φ.flow T y ∈ N := hInv y hy T
  obtain ⟨A, U, hU, hA, hco⟩ := hgraze (φ.flow T y) hpN hcl

  have hW : U ∩ ⋂ i ∈ A, F i ∈ 𝓝 (φ.flow T y) :=
    Filter.inter_mem hU
      ((Filter.biInter_mem A.toFinite).mpr fun i hi => (hA i hi).2)

  have hgc : Continuous fun u : ℝ => φ.flow u.toNNReal y :=
    (htraj y).comp continuous_real_toNNReal
  have hgT : φ.flow ((T : ℝ)).toNNReal y = φ.flow T y := by
    rw [Real.toNNReal_coe]
  have hpre : (fun u : ℝ => φ.flow u.toNNReal y) ⁻¹' (U ∩ ⋂ i ∈ A, F i) ∈
      𝓝 ((T : ℝ)) := by
    refine hgc.continuousAt.preimage_mem_nhds ?_
    simpa [hgT] using hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre

  set r : ℝ := min (δ / 2) (T : ℝ) with hr
  have hTpos : (0 : ℝ) < (T : ℝ) := NNReal.coe_pos.mpr hT
  have hr0 : 0 < r := lt_min (by linarith) hTpos
  have hrT : r ≤ (T : ℝ) := min_le_right _ _
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwin : ∀ u : ℝ, (T : ℝ) - r ≤ u → u ≤ (T : ℝ) →
      φ.flow u.toNNReal y ∈ U ∩ ⋂ i ∈ A, F i := by
    intro u h1 h2
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |u - (T : ℝ)| = (T : ℝ) - u := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs]; linarith

  have hx₀W : φ.flow ((T : ℝ) - r).toNNReal y ∈ U ∩ ⋂ i ∈ A, F i :=
    hwin _ le_rfl (by linarith)
  have hx₀N : φ.flow ((T : ℝ) - r).toNNReal y ∈ N := hInv y hy _

  have hkey : ∀ s : ℝ≥0, (s : ℝ) ≤ r →
      φ.flow s (φ.flow ((T : ℝ) - r).toNNReal y) =
        φ.flow ((T : ℝ) - r + (s : ℝ)).toNNReal y := by
    intro s hs
    rw [← φ.flow_add]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith),
      Real.coe_toNNReal _ (by linarith [s.coe_nonneg])]
  have hsle : ∀ s : ℝ≥0, s ≤ r.toNNReal → (s : ℝ) ≤ r := by
    intro s hs
    have := NNReal.coe_le_coe.mpr hs
    rwa [Real.coe_toNNReal _ hr0.le] at this

  have hneg : ∀ i ∈ A, ℓ i (φ.flow ((T : ℝ) - r).toNNReal y) < 0 := by
    intro i hi
    have hx₀F : φ.flow ((T : ℝ) - r).toNNReal y ∈ F i :=
      Set.mem_iInter₂.mp hx₀W.2 i hi
    have hconf : ∀ s : ℝ≥0, s ≤ r.toNNReal →
        φ.flow s (φ.flow ((T : ℝ) - r).toNNReal y) ∈ F i := by
      intro s hs
      rw [hkey s (hsle s hs)]
      have hs' : (s : ℝ) ≤ r := hsle s hs
      exact Set.mem_iInter₂.mp
        (hwin ((T : ℝ) - r + (s : ℝ)) (by linarith [s.coe_nonneg])
          (by linarith)).2 i hi
    have hgrow := hrow i _ hx₀F r.toNNReal hconf
    have hflowr : φ.flow r.toNNReal (φ.flow ((T : ℝ) - r).toNNReal y) =
        φ.flow T y := by
      rw [hkey r.toNNReal (by rw [Real.coe_toNNReal _ hr0.le])]
      have harith : (T : ℝ) - r + (r.toNNReal : ℝ) = (T : ℝ) := by
        rw [Real.coe_toNNReal _ hr0.le]; ring
      rw [harith, hgT]
    rw [hflowr, (hA i hi).1] at hgrow
    have hpos : 0 < ε i * (r.toNNReal : ℝ) := by
      refine mul_pos (hε i) ?_
      rwa [Real.coe_toNNReal _ hr0.le]
    linarith

  obtain ⟨i, hi, hnn⟩ := hco _ hx₀W.1 hx₀N
  exact absurd hnn (not_le.mpr (hneg i hi))

theorem HasMarginRows.chainMargin {φ : Semiflow X} {D N : Set X}
    (h : φ.HasMarginRows D N)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hN : IsCompact N) (hInv : φ.Invariant N)
    {T : ℝ≥0} (hT : 0 < T) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ChainMargin φ D N T ε₀ := by
  classical
  rcases Set.eq_empty_or_nonempty N with hNe | hNne
  · exact ⟨1, one_pos, fun y hy => by rw [hNe] at hy; exact absurd hy (Set.notMem_empty y)⟩
  rcases Set.eq_empty_or_nonempty (D \ N) with hDNe | hDNne
  · refine ⟨1, one_pos, fun y hy t ht z hz hzN => ?_⟩
    have : z ∈ D \ N := ⟨hz, hzN⟩
    rw [hDNe] at this
    exact absurd this (Set.notMem_empty z)

  have hKc : IsCompact (φ.flow T '' N) := hN.image (hflow T)
  have hKne : (φ.flow T '' N).Nonempty := hNne.image _
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hKc.exists_isMinOn hKne
    (Metric.continuous_infDist_pt (D \ N)).continuousOn
  refine ⟨Metric.infDist p₀ (D \ N), ?_, ?_⟩
  ·
    rcases lt_or_eq_of_le
      (Metric.infDist_nonneg : (0 : ℝ) ≤ Metric.infDist p₀ (D \ N)) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨y₀, hy₀, rfl⟩ := hp₀K
      exact h.flow_notMem_closure hInv htraj hT hy₀
        ((Metric.mem_closure_iff_infDist_zero hDNne).mpr h0.symm)
  · intro y hy t ht z hz hzN
    have hmem : φ.flow t y ∈ φ.flow T '' N := by
      refine ⟨φ.flow (t - T) y, hInv y hy _, ?_⟩
      rw [← φ.flow_add, tsub_add_cancel_of_le ht]
    exact le_trans (isMinOn_iff.mp hp₀min _ hmem)
      (Metric.infDist_le_dist_of_mem ⟨hz, hzN⟩)

theorem isChainBlock_of_marginRows {φ : Semiflow X} {D N : Set X}
    (hN : IsCompact N) (hInv : φ.Invariant N)
    (h : φ.HasMarginRows D N)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x) :
    IsChainBlock φ D N := by
  obtain ⟨ε₀, hε₀, hM⟩ := h.chainMargin hflow htraj hN hInv (T := 1) one_pos
  exact ⟨hN, hInv, 1, ε₀, hε₀, hM⟩

theorem isChainBlock_of_rows [T2Space X] {φ : Semiflow X} {D N : Set X}
    (hN : IsCompact N)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hND : N ⊆ D) (hD : φ.Invariant D)
    (hfacet : φ.HasFacetRows D N) (hmargin : φ.HasMarginRows D N) :
    IsChainBlock φ D N :=
  isChainBlock_of_marginRows hN
    (invariant_of_boundaryDwell hN.isClosed htraj
      (hfacet.boundaryDwell hND hD htraj))
    hmargin hflow htraj

end Bridge

section Absorption

variable [PseudoMetricSpace X]

theorem IsChainBlock.absorbOmega {φ : Semiflow X} {D b : Set X}
    (hb : IsChainBlock φ D b)
    (hflow : ∀ t, Continuous (φ.flow t))
    {γ : ℝ → X} (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ D)
    (hne : (omegaSet γ ∩ b).Nonempty) :
    ∃ T : ℝ, ∀ t, T ≤ t → γ t ∈ b := by
  obtain ⟨z, hzω, hzb⟩ := hne
  obtain ⟨-, hbI, Tm, ε₀, hε₀, hM⟩ := hb
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp ((hflow Tm).continuousAt (x := z)) ε₀ hε₀
  have hz0 : z ∈ closure (γ '' Set.Ici (0 : ℝ)) := Set.mem_iInter.mp hzω 0
  obtain ⟨w, hw, hdw⟩ := Metric.mem_closure_iff.mp hz0 δ hδ
  obtain ⟨s, -, rfl⟩ := hw
  have hjump : dist (φ.flow Tm (γ s)) (φ.flow Tm z) < ε₀ :=
    hcont (by rwa [dist_comm] at hdw)
  have horbs : γ (s + (Tm : ℝ)) = φ.flow Tm (γ s) := horb s Tm
  have hmem : γ (s + (Tm : ℝ)) ∈ b := by
    by_contra hnb
    have hD : γ (s + (Tm : ℝ)) ∈ D := hr ⟨_, rfl⟩
    have hmargin := hM z hzb Tm le_rfl _ hD hnb
    rw [horbs] at hmargin
    rw [dist_comm] at hjump
    linarith
  exact ⟨s + (Tm : ℝ), fun t htt => horb.forward_mem hbI htt hmem⟩

theorem IsChainBlock.absorbAlpha {φ : Semiflow X} {D b : Set X}
    (hb : IsChainBlock φ D b)
    (hflow : ∀ t, Continuous (φ.flow t))
    {γ : ℝ → X} (horb : φ.CompleteOrbit γ) (hr : Set.range γ ⊆ D)
    (hne : (alphaSet γ ∩ b).Nonempty) :
    ∃ T : ℝ, ∀ t, t ≤ T → γ t ∈ b := by
  obtain ⟨z, hzα, hzb⟩ := hne
  obtain ⟨-, hbI, Tm, ε₀, hε₀, hM⟩ := hb
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp ((hflow Tm).continuousAt (x := z)) ε₀ hε₀
  refine ⟨0, fun t _ => ?_⟩
  have hzcl : z ∈ closure (γ '' Set.Iic (t - (Tm : ℝ))) :=
    Set.mem_iInter.mp hzα _
  obtain ⟨w, hw, hdw⟩ := Metric.mem_closure_iff.mp hzcl δ hδ
  obtain ⟨s, hst, rfl⟩ := hw
  have hjump : dist (φ.flow Tm (γ s)) (φ.flow Tm z) < ε₀ :=
    hcont (by rwa [dist_comm] at hdw)
  have horbs : γ (s + (Tm : ℝ)) = φ.flow Tm (γ s) := horb s Tm
  have hmem : γ (s + (Tm : ℝ)) ∈ b := by
    by_contra hnb
    have hD : γ (s + (Tm : ℝ)) ∈ D := hr ⟨_, rfl⟩
    have hmargin := hM z hzb Tm le_rfl _ hD hnb
    rw [horbs] at hmargin
    rw [dist_comm] at hjump
    linarith
  have hst' : s + (Tm : ℝ) ≤ t := by
    have := Set.mem_Iic.mp hst
    linarith
  exact horb.forward_mem hbI hst' hmem

end Absorption

section PairDescent

variable {ι β : Type*} [Finite ι]

theorem exists_member_notMem_cover {blocks : β → Set X} {emb : ι → β}
    {cover : ι → β}
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    {x : X} (i : ι) (hmem : x ∈ blocks (emb i)) :
    ∃ j : ι, x ∈ blocks (emb j) ∧ x ∉ blocks (cover j) := by
  classical
  have hwf : WellFounded (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) := by
    haveI : IsTrans ι (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) :=
      ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
    haveI : Std.Irrefl (fun i' j : ι => blocks (emb i') ⊂ blocks (emb j)) :=
      ⟨fun _ h => ssubset_irrefl _ h⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  have key := hwf.induction
    (C := fun i₀ : ι => x ∈ blocks (emb i₀) →
      ∃ j : ι, x ∈ blocks (emb j) ∧ x ∉ blocks (cover j))
    i (by
      intro i₀ IH hmem₀
      by_cases hc : x ∈ blocks (cover i₀)
      · obtain ⟨i', hmem', hsub'⟩ := hJoin (cover i₀) x hc
        exact IH i' (hsub'.trans_ssubset (hcover i₀)) hmem'
      · exact ⟨i₀, hmem₀, hc⟩)
  exact key hmem

variable [PseudoMetricSpace X]

theorem chainPair_of_memberBlocks {φ : Semiflow X} {D : Set X}
    {blocks : β → Set X} {emb : ι → β} {cover : ι → β} {bD : β}
    {cells : ι → Set X}
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (hMemberBlock : ∀ b : β, IsChainBlock φ D (blocks b)) :
    ∀ x ∈ D, ∃ (i : ι) (b b' : Set X), x ∈ b ∧ x ∉ b' ∧
      IsChainBlock φ D b ∧ IsChainBlock φ D b' ∧ b \ b' ⊆ cells i := by
  intro x hxD
  obtain ⟨i₀, hmem₀, -⟩ := hJoin bD x (hbD hxD)
  obtain ⟨j, hjmem, hjnc⟩ := exists_member_notMem_cover hJoin hcover i₀ hmem₀
  exact ⟨j, blocks (emb j), blocks (cover j), hjmem, hjnc,
    hMemberBlock (emb j), hMemberBlock (cover j), hcellsSup j⟩

end PairDescent

section Combined

variable {Vtx ι β : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [PartialOrder ι] [Finite ι]

theorem qMorseDischarge_sound_marginAssembled (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (blocks : β → Set X) (emb : ι → β) (cover : ι → β) (bD : β)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hMeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c)
    (hMemberBlock : ∀ b : β, IsChainBlock φ D (blocks b)) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_waveAssembled φ D ρ cells hmap blocks emb cover
    bD hD hflow hcells hContain hOverlap
    (chainPair_of_memberBlocks hbD hJoin hcover hcellsSup hMemberBlock)
    hTransitCert hConv hMono hbD hJoin hcover hcellsSup horder
    (fun i => (hMemberBlock (emb i)).1.isClosed)
    (fun b => (hMemberBlock b).2.1)
    hMeet
    (fun _ horb hr b hne => (hMemberBlock b).absorbOmega hflow horb hr hne)
    (fun _ horb hr b hne => (hMemberBlock b).absorbAlpha hflow horb hr hne)

theorem qMorseDischarge_sound_rowsFloor (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (blocks : β → Set X) (emb : ι → β) (cover : ι → β) (bD : β)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hDInv : φ.Invariant D)
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hMeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c)
    (hBcomp : ∀ b : β, IsCompact (blocks b))
    (hBsubD : ∀ b : β, blocks b ⊆ D)
    (hBfacet : ∀ b : β, φ.HasFacetRows D (blocks b))
    (hBmargin : ∀ b : β, φ.HasMarginRows D (blocks b)) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_marginAssembled φ D ρ cells hmap blocks emb cover
    bD hD hflow hcells hContain hOverlap hTransitCert hConv hMono hbD
    hJoin hcover hcellsSup horder hMeet
    (fun b => isChainBlock_of_rows (hBcomp b) hflow htraj (hBsubD b)
      hDInv (hBfacet b) (hBmargin b))

end Combined

end Semiflow

namespace Grid

open scoped NNReal
open Set Topology Filter

variable {d : ℕ} (G : Grid d)

theorem isCompact_cell (c : G.CellIdx) : IsCompact (G.Cell c) := by
  have h : G.Cell c = Set.Icc (fun k => G.line k (c k).castSucc)
      (fun k => G.line k (c k).succ) := by
    ext x
    simp [mem_cell_iff, Set.mem_Icc, Pi.le_def, forall_and]
  rw [h]
  exact isCompact_Icc

theorem isCompact_blockRegion (B : Finset G.CellIdx) :
    IsCompact (G.blockRegion B) :=
  B.finite_toSet.isCompact_biUnion fun c _ => G.isCompact_cell c

theorem exists_cell_of_mem_arena [Nonempty G.CellIdx] {y : Fin d → ℝ}
    (hy : y ∈ G.arena) : ∃ c : G.CellIdx, y ∈ G.Cell c := by
  classical
  have hpos : ∀ k, 0 < G.n k := fun k => ((Classical.arbitrary G.CellIdx) k).pos
  have key : ∀ k : Fin d, ∃ j : Fin (G.n k),
      G.line k j.castSucc ≤ y k ∧ y k ≤ G.line k j.succ := by
    intro k
    set J : Finset (Fin (G.n k + 1)) :=
      Finset.univ.filter fun j => G.line k j ≤ y k with hJ
    have hJne : J.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hy k).1⟩⟩
    set jm := J.max' hJne with hjm
    have hjmle : G.line k jm ≤ y k := (Finset.mem_filter.mp (J.max'_mem hJne)).2
    by_cases hlast : (jm : ℕ) = G.n k
    ·
      have hk := hpos k
      have htop : y k = G.line k (Fin.last (G.n k)) := by
        have h1 : G.line k (Fin.last (G.n k)) ≤ y k := by
          have hjml : jm = Fin.last (G.n k) := Fin.ext (by simpa using hlast)
          rwa [hjml] at hjmle
        exact le_antisymm (hy k).2 h1
      refine ⟨⟨G.n k - 1, by omega⟩, ?_, ?_⟩
      · have h1 : G.line k (Fin.castSucc (⟨G.n k - 1, by omega⟩ : Fin (G.n k))) ≤
            G.line k (Fin.last (G.n k)) :=
          (G.mono k).monotone
            (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega)
        rw [← htop] at h1
        exact h1
      · have hsucc : (Fin.succ (⟨G.n k - 1, by omega⟩ : Fin (G.n k))) =
            Fin.last (G.n k) :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [hsucc]
        exact htop.le
    ·
      have hjlt : (jm : ℕ) < G.n k := by
        have := jm.isLt; omega
      refine ⟨⟨jm, hjlt⟩, ?_, ?_⟩
      · have hcast : Fin.castSucc (⟨(jm : ℕ), hjlt⟩ : Fin (G.n k)) = jm :=
          Fin.ext (by simp)
        rwa [hcast]
      · by_contra hgt
        push Not at hgt
        have hmem : Fin.succ (⟨(jm : ℕ), hjlt⟩ : Fin (G.n k)) ∈ J :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt.le⟩
        have hle := J.le_max' _ hmem
        rw [← hjm] at hle
        simp only [Fin.le_def, Fin.val_succ] at hle
        omega
  choose c hc using key
  exact ⟨c, fun k => hc k⟩

theorem exists_nonblock_cell {B : Finset G.CellIdx} {p : Fin d → ℝ}
    (hpN : p ∈ G.blockRegion B)
    (hcl : p ∈ closure (G.arena \ G.blockRegion B)) :
    ∃ c' : G.CellIdx, c' ∉ B ∧ p ∈ G.Cell c' := by
  classical
  obtain ⟨c₀, -, -⟩ := G.mem_blockRegion_iff.mp hpN
  haveI : Nonempty G.CellIdx := ⟨c₀⟩
  have hsub : G.arena \ G.blockRegion B ⊆
      ⋃ c ∈ (Finset.univ \ B : Finset G.CellIdx), G.Cell c := by
    rintro y ⟨hyD, hyN⟩
    obtain ⟨c, hc⟩ := G.exists_cell_of_mem_arena hyD
    have hcB : c ∉ B := fun hmem => hyN (G.mem_blockRegion_iff.mpr ⟨c, hmem, hc⟩)
    exact Set.mem_biUnion (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcB⟩) hc
  have hclosed : IsClosed (⋃ c ∈ (Finset.univ \ B : Finset G.CellIdx), G.Cell c) :=
    Set.Finite.isClosed_biUnion (Finset.univ \ B).finite_toSet
      fun c _ => G.isClosed_cell c
  have hmem := hclosed.closure_subset ((closure_mono hsub) hcl)
  obtain ⟨c', hc'mem, hc'⟩ := Set.mem_iUnion₂.mp hmem
  exact ⟨c', (Finset.mem_sdiff.mp hc'mem).2, hc'⟩

theorem adjacent_of_shared {k : Fin d} {i j : Fin (G.n k)} (hij : i ≠ j)
    {v : ℝ}
    (hi : G.line k i.castSucc ≤ v ∧ v ≤ G.line k i.succ)
    (hj : G.line k j.castSucc ≤ v ∧ v ≤ G.line k j.succ) :
    ((j : ℕ) = (i : ℕ) + 1 ∧ v = G.line k i.succ) ∨
    ((i : ℕ) = (j : ℕ) + 1 ∧ v = G.line k i.castSucc) := by
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with hlt | hgt
  ·
    left
    have hle : i.succ ≤ j.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    have hchain : G.line k i.succ ≤ G.line k j.castSucc :=
      (G.mono k).monotone hle
    have hv : v = G.line k i.succ := le_antisymm hi.2 (le_trans hchain hj.1)

    refine ⟨?_, hv⟩
    by_contra hne
    have hstrict : i.succ < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
      omega
    have hlines := G.mono k hstrict
    have hv2 : G.line k j.castSucc ≤ v := hj.1
    rw [hv] at hv2
    linarith
  ·
    right
    have hle : j.succ ≤ i.castSucc := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    have hchain : G.line k j.succ ≤ G.line k i.castSucc :=
      (G.mono k).monotone hle
    have hv : v = G.line k i.castSucc :=
      le_antisymm (le_trans hj.2 hchain) hi.1
    refine ⟨?_, hv⟩
    by_contra hne
    have hstrict : j.succ < i.castSucc := by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
      omega
    have hlines := G.mono k hstrict
    have hv2 : v ≤ G.line k j.succ := hj.2
    rw [hv] at hv2
    linarith

theorem exists_active_facet {B : Finset G.CellIdx} {p : Fin d → ℝ}
    {c c' : G.CellIdx} (hcB : c ∈ B) (hc'nB : c' ∉ B)
    (hpc : p ∈ G.Cell c) (hpc' : p ∈ G.Cell c') :
    ∃ (a : G.CellIdx) (k : Fin d) (s : Bool),
      G.IsFacet B (a, k, s) ∧ p ∈ G.facetBox (a, k, s) ∧ a k = c k := by
  classical
  suffices H : ∀ (m : ℕ) (a : G.CellIdx), a ∈ B → p ∈ G.Cell a →
      (∀ j, a j = c j ∨ a j = c' j) →
      (Finset.univ.filter fun j => a j ≠ c' j).card ≤ m →
      ∃ (a' : G.CellIdx) (k : Fin d) (s : Bool),
        G.IsFacet B (a', k, s) ∧ p ∈ G.facetBox (a', k, s) ∧ a' k = c k by
    exact H _ c hcB hpc (fun j => Or.inl rfl) le_rfl
  intro m
  induction m with
  | zero =>
    intro a haB hpa hmix hcard
    exfalso
    have hempty : (Finset.univ.filter fun j => a j ≠ c' j) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have haeq : a = c' := by
      funext j
      by_contra hne
      have : j ∈ Finset.univ.filter fun j => a j ≠ c' j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      simp [hempty] at this
    exact hc'nB (haeq ▸ haB)
  | succ m ih =>
    intro a haB hpa hmix hcard

    have hne : (Finset.univ.filter fun j => a j ≠ c' j).Nonempty := by
      rcases Finset.eq_empty_or_nonempty
        (Finset.univ.filter fun j => a j ≠ c' j) with hempty | h
      · exfalso
        have haeq : a = c' := by
          funext j
          by_contra hnej
          have : j ∈ Finset.univ.filter fun j => a j ≠ c' j :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnej⟩
          simp [hempty] at this
        exact hc'nB (haeq ▸ haB)
      · exact h
    obtain ⟨k, hk⟩ := hne
    have hak : a k ≠ c' k := (Finset.mem_filter.mp hk).2
    have hakc : a k = c k := (hmix k).resolve_right hak

    rcases G.adjacent_of_shared hak (hpa k) (hpc' k) with
      ⟨hval, hv⟩ | ⟨hval, hv⟩
    ·
      have hupd : Function.update a k (c' k) k = c' k := Function.update_self ..
      have hupdj : ∀ j, j ≠ k → Function.update a k (c' k) j = a j :=
        fun j hj => Function.update_of_ne hj ..
      have hpa1 : p ∈ G.Cell (Function.update a k (c' k)) := by
        intro j
        rcases eq_or_ne j k with rfl | hjk
        · rw [hupd]; exact hpc' j
        · rw [hupdj j hjk]; exact hpa j
      by_cases ha1B : Function.update a k (c' k) ∈ B
      ·
        have hmix1 : ∀ j, Function.update a k (c' k) j = c j ∨
            Function.update a k (c' k) j = c' j := by
          intro j
          rcases eq_or_ne j k with rfl | hjk
          · exact Or.inr (hupd)
          · rw [hupdj j hjk]; exact hmix j
        have hsub : (Finset.univ.filter fun j =>
            Function.update a k (c' k) j ≠ c' j) ⊆
            (Finset.univ.filter fun j => a j ≠ c' j).erase k := by
          intro j hj
          have hjne := (Finset.mem_filter.mp hj).2
          rcases eq_or_ne j k with rfl | hjk
          · rw [hupd] at hjne; exact absurd rfl hjne
          · refine Finset.mem_erase.mpr ⟨hjk, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, ?_⟩⟩
            rwa [hupdj j hjk] at hjne
        have hcard1 : (Finset.univ.filter fun j =>
            Function.update a k (c' k) j ≠ c' j).card ≤ m := by
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem hk
          have h3 : 1 ≤ (Finset.univ.filter fun j => a j ≠ c' j).card :=
            Finset.card_pos.mpr ⟨k, hk⟩
          omega
        exact ih _ ha1B hpa1 hmix1 hcard1
      ·
        have hlt : (a k : ℕ) + 1 < G.n k := by
          have := (c' k).isLt; omega
        have hupdeq : Function.update a k (⟨(a k : ℕ) + 1, hlt⟩ : Fin (G.n k)) =
            Function.update a k (c' k) := by
          congr 1
          exact Fin.ext (by simp [hval])
        refine ⟨a, k, true, ⟨haB, hlt, ?_⟩, ⟨hpa, ?_⟩, hakc⟩
        · rw [hupdeq]; exact ha1B
        · show p k = G.facetLine (a, k, true)
          simpa [facetLine] using hv
    ·
      have hpos : 0 < (a k : ℕ) := by omega
      have hupd : Function.update a k (c' k) k = c' k := Function.update_self ..
      have hupdj : ∀ j, j ≠ k → Function.update a k (c' k) j = a j :=
        fun j hj => Function.update_of_ne hj ..
      have hpa1 : p ∈ G.Cell (Function.update a k (c' k)) := by
        intro j
        rcases eq_or_ne j k with rfl | hjk
        · rw [hupd]; exact hpc' j
        · rw [hupdj j hjk]; exact hpa j
      by_cases ha1B : Function.update a k (c' k) ∈ B
      · have hmix1 : ∀ j, Function.update a k (c' k) j = c j ∨
            Function.update a k (c' k) j = c' j := by
          intro j
          rcases eq_or_ne j k with rfl | hjk
          · exact Or.inr (hupd)
          · rw [hupdj j hjk]; exact hmix j
        have hsub : (Finset.univ.filter fun j =>
            Function.update a k (c' k) j ≠ c' j) ⊆
            (Finset.univ.filter fun j => a j ≠ c' j).erase k := by
          intro j hj
          have hjne := (Finset.mem_filter.mp hj).2
          rcases eq_or_ne j k with rfl | hjk
          · rw [hupd] at hjne; exact absurd rfl hjne
          · refine Finset.mem_erase.mpr ⟨hjk, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, ?_⟩⟩
            rwa [hupdj j hjk] at hjne
        have hcard1 : (Finset.univ.filter fun j =>
            Function.update a k (c' k) j ≠ c' j).card ≤ m := by
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem hk
          have h3 : 1 ≤ (Finset.univ.filter fun j => a j ≠ c' j).card :=
            Finset.card_pos.mpr ⟨k, hk⟩
          omega
        exact ih _ ha1B hpa1 hmix1 hcard1
      · have hltm : (a k : ℕ) - 1 < G.n k :=
          lt_of_le_of_lt (Nat.sub_le _ _) (a k).isLt
        have hupdeq : Function.update a k (⟨(a k : ℕ) - 1, hltm⟩ : Fin (G.n k)) =
            Function.update a k (c' k) := by
          congr 1
          exact Fin.ext (by simp; omega)
        refine ⟨a, k, false, ⟨haB, hpos, ?_⟩, ⟨hpa, ?_⟩, hakc⟩
        · rw [hupdeq]; exact ha1B
        · show p k = G.facetLine (a, k, false)
          simpa [facetLine] using hv

theorem graze_clause (B : Finset G.CellIdx) {p : Fin d → ℝ}
    (hpN : p ∈ G.blockRegion B)
    (hcl : p ∈ closure (G.arena \ G.blockRegion B)) :
    ∃ U ∈ 𝓝 p, ∀ q ∈ U, q ∈ G.blockRegion B →
      ∃ f : G.FacetData, G.IsFacet B f ∧ p ∈ G.facetBox f ∧ 0 ≤ G.obs f q := by
  classical
  obtain ⟨c', hc'nB, hpc'⟩ := G.exists_nonblock_cell hpN hcl
  refine ⟨(⋃ c ∈ Finset.univ.filter (fun c : G.CellIdx => p ∉ G.Cell c),
    G.Cell c)ᶜ, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact (Set.Finite.isClosed_biUnion
        (Finset.univ.filter (fun c : G.CellIdx => p ∉ G.Cell c)).finite_toSet
        fun c _ => G.isClosed_cell c).isOpen_compl
    · intro hmem
      obtain ⟨c, hc, hpmem⟩ := Set.mem_iUnion₂.mp hmem
      exact (Finset.mem_filter.mp hc).2 hpmem
  · intro q hqU hqN
    obtain ⟨c, hcB, hqc⟩ := G.mem_blockRegion_iff.mp hqN
    have hpc : p ∈ G.Cell c := by
      by_contra hnp
      exact hqU (Set.mem_biUnion
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnp⟩) hqc)
    obtain ⟨a, k, s, hfacet, hbox, hak⟩ :=
      G.exists_active_facet hcB hc'nB hpc hpc'
    refine ⟨(a, k, s), hfacet, hbox, ?_⟩
    cases s with
    | false =>

        have h1 := (hqc k).1
        simp only [obs, facetLine, Bool.false_eq_true, if_false]
        rw [hak]
        linarith
    | true =>

        have h2 := (hqc k).2
        simp only [obs, facetLine, if_true]
        rw [hak]
        linarith

theorem hasMarginRows_of_rows (φ : Semiflow (Fin d → ℝ)) (B : Finset G.CellIdx)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (hε : ∀ f, G.IsFacet B f → 0 < ε f)
    (hF : ∀ f, G.IsFacet B f → ∀ x ∈ G.facetBox f, F f ∈ 𝓝 x)
    (hrow : ∀ f, G.IsFacet B f → ∀ x ∈ F f, ∀ t : ℝ≥0,
      (∀ s ≤ t, φ.flow s x ∈ F f) →
      G.obs f x + ε f * (t : ℝ) ≤ G.obs f (φ.flow t x)) :
    φ.HasMarginRows G.arena (G.blockRegion B) := by
  classical
  refine ⟨Fintype.card {f : G.FacetData // G.IsFacet B f},
    fun i => G.obs ((Fintype.equivFin _).symm i).1,
    fun i => ε ((Fintype.equivFin _).symm i).1,
    fun i => F ((Fintype.equivFin _).symm i).1,
    fun i => hε _ ((Fintype.equivFin _).symm i).2,
    fun i => hrow _ ((Fintype.equivFin _).symm i).2, ?_⟩
  intro p hpN hcl
  obtain ⟨U, hU, hgraze⟩ := G.graze_clause B hpN hcl
  refine ⟨{i | p ∈ G.facetBox ((Fintype.equivFin _).symm i).1}, U, hU, ?_, ?_⟩
  · intro i hi
    exact ⟨G.obs_eq_zero_of_mem_facetBox hi,
      hF _ ((Fintype.equivFin _).symm i).2 p hi⟩
  · intro q hqU hqN
    obtain ⟨f, hfac, hbox, hobs⟩ := hgraze q hqU hqN
    exact ⟨(Fintype.equivFin {f : G.FacetData // G.IsFacet B f}) ⟨f, hfac⟩,
      by simpa using hbox, by simpa using hobs⟩

theorem isChainBlock_of_grid (φ : Semiflow (Fin d → ℝ)) (B : Finset G.CellIdx)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hArena : φ.Invariant G.arena)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (hε : ∀ f, G.IsFacet B f → 0 < ε f)
    (hF : ∀ f, G.IsFacet B f → ∀ x ∈ G.facetBox f, F f ∈ 𝓝 x)
    (hrow : ∀ f, G.IsFacet B f → ∀ x ∈ F f, ∀ t : ℝ≥0,
      (∀ s ≤ t, φ.flow s x ∈ F f) →
      G.obs f x + ε f * (t : ℝ) ≤ G.obs f (φ.flow t x)) :
    Semiflow.IsChainBlock φ G.arena (G.blockRegion B) :=
  Semiflow.isChainBlock_of_rows (G.isCompact_blockRegion B) hflow htraj
    (G.blockRegion_subset_arena B) hArena
    (G.hasFacetRows_of_rows φ B ε F hε hF hrow)
    (G.hasMarginRows_of_rows φ B ε F hε hF hrow)

end Grid

end Qtsl
end PPLC

#print axioms PPLC.Qtsl.Semiflow.HasMarginRows.flow_notMem_closure
#print axioms PPLC.Qtsl.Semiflow.HasMarginRows.chainMargin
#print axioms PPLC.Qtsl.Semiflow.isChainBlock_of_marginRows
#print axioms PPLC.Qtsl.Semiflow.isChainBlock_of_rows
#print axioms PPLC.Qtsl.Semiflow.IsChainBlock.absorbOmega
#print axioms PPLC.Qtsl.Semiflow.IsChainBlock.absorbAlpha
#print axioms PPLC.Qtsl.Semiflow.exists_member_notMem_cover
#print axioms PPLC.Qtsl.Semiflow.chainPair_of_memberBlocks
#print axioms PPLC.Qtsl.Semiflow.qMorseDischarge_sound_marginAssembled
#print axioms PPLC.Qtsl.Semiflow.qMorseDischarge_sound_rowsFloor
#print axioms PPLC.Qtsl.Grid.isCompact_cell
#print axioms PPLC.Qtsl.Grid.isCompact_blockRegion
#print axioms PPLC.Qtsl.Grid.exists_cell_of_mem_arena
#print axioms PPLC.Qtsl.Grid.exists_nonblock_cell
#print axioms PPLC.Qtsl.Grid.adjacent_of_shared
#print axioms PPLC.Qtsl.Grid.exists_active_facet
#print axioms PPLC.Qtsl.Grid.graze_clause
#print axioms PPLC.Qtsl.Grid.hasMarginRows_of_rows
#print axioms PPLC.Qtsl.Grid.isChainBlock_of_grid
