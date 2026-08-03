import Qtsl.ChainMargin

/-!
# No orbit rides an internal facet

The facet-riding argument: a certified nonzero normal component moves
any facet point instantly off the facet, so the times an orbit spends
on internal facets have empty interior. This moves the meet clause's
orbit-confinement from prose to row-shaped combinatorial data.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set Topology Filter

variable {X : Type*}

section TopologyCore

variable {α : Type*} [TopologicalSpace α]

theorem interior_union_eq_empty {A B : Set α} (hA : IsClosed A)
    (hAi : interior A = ∅) (hBi : interior B = ∅) :
    interior (A ∪ B) = ∅ := by
  have hsub : interior (A ∪ B) \ A ⊆ interior B :=
    interior_maximal
      (fun x hx => (interior_subset hx.1).resolve_left hx.2)
      (isOpen_interior.sdiff hA)
  have hIA : interior (A ∪ B) ⊆ A := by
    intro x hx
    by_contra hxA
    have h := hsub ⟨hx, hxA⟩
    rw [hBi] at h
    exact Set.notMem_empty x h
  have h2 : interior (A ∪ B) ⊆ interior A :=
    interior_maximal hIA isOpen_interior
  rw [hAi] at h2
  exact Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => Set.notMem_empty x (h2 hx)

theorem interior_biUnion_eq_empty {ι : Type*} (s : Finset ι)
    {f : ι → Set α} (hcl : ∀ i, IsClosed (f i))
    (hint : ∀ i, interior (f i) = ∅) :
    interior (⋃ i ∈ s, f i) = ∅ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha IH =>
      rw [Finset.cons_eq_insert, Finset.set_biUnion_insert]
      exact interior_union_eq_empty (hcl a) (hint a) IH

theorem interior_iUnion_eq_empty {ι : Type*} [Finite ι] {f : ι → Set α}
    (hcl : ∀ i, IsClosed (f i)) (hint : ∀ i, interior (f i) = ∅) :
    interior (⋃ i, f i) = ∅ := by
  classical
  cases nonempty_fintype ι
  have h : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by
    ext x; simp
  rw [h]
  exact interior_biUnion_eq_empty Finset.univ hcl hint

theorem exists_Icc_subset_of_closed_cover {ι : Type*} [Finite ι]
    {f : ι → Set ℝ} (hcl : ∀ i, IsClosed (f i)) {a b : ℝ} (hab : a < b)
    (hcov : Set.Icc a b ⊆ ⋃ i, f i) :
    ∃ (i : ι) (z₀ z₁ : ℝ), z₀ < z₁ ∧ Set.Icc z₀ z₁ ⊆ f i := by
  classical
  have hne : ∃ i, (interior (f i)).Nonempty := by
    by_contra hcon
    push Not at hcon
    have hu : interior (⋃ i, f i) = ∅ := interior_iUnion_eq_empty hcl hcon
    have hsub : Set.Ioo a b ⊆ interior (⋃ i, f i) :=
      interior_maximal (Set.Ioo_subset_Icc_self.trans hcov) isOpen_Ioo
    rw [hu] at hsub
    exact Set.notMem_empty _
      (hsub (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩ :
        (a + b) / 2 ∈ Set.Ioo a b))
  obtain ⟨i, x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  refine ⟨i, x - r / 2, x + r / 2, by linarith, ?_⟩
  intro y hy
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hy
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  exact interior_subset (hball hyball)

end TopologyCore

namespace Semiflow

section OrbitContinuity

variable [TopologicalSpace X]

theorem CompleteOrbit.continuous {φ : Semiflow X} {γ : ℝ → X}
    (horb : φ.CompleteOrbit γ)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x) :
    Continuous γ := by
  rw [continuous_iff_continuousAt]
  intro v
  have hg : Continuous fun w : ℝ => φ.flow (w - (v - 1)).toNNReal (γ (v - 1)) :=
    (htraj (γ (v - 1))).comp
      (continuous_real_toNNReal.comp (continuous_sub_right (v - 1)))
  refine hg.continuousAt.congr ?_
  refine Filter.eventuallyEq_of_mem (Ioi_mem_nhds (by linarith : v - 1 < v)) ?_
  intro w hw
  have hw' : v - 1 ≤ w := le_of_lt hw
  have h := horb (v - 1) (w - (v - 1)).toNNReal
  rw [Real.coe_toNNReal _ (by linarith)] at h
  have harith : v - 1 + (w - (v - 1)) = w := by ring
  rw [harith] at h
  exact h.symm

end OrbitContinuity

section MeetRows

variable [TopologicalSpace X]

def HasMeetRows (φ : Semiflow X) (A B C : Set X) : Prop :=
  ∃ (n : ℕ) (ℓ : Fin n → X → ℝ) (ε : Fin n → ℝ) (F Gp : Fin n → Set X),
    (∀ i, 0 < ε i) ∧
    (∀ i, ∀ x ∈ F i, ∀ t : ℝ≥0, (∀ s ≤ t, φ.flow s x ∈ F i) →
      ℓ i x + ε i * (t : ℝ) ≤ ℓ i (φ.flow t x)) ∧
    (∀ i, IsClosed (Gp i)) ∧
    (∀ i, Gp i ⊆ F i) ∧
    (∀ i, ∀ x ∈ Gp i, ℓ i x = 0) ∧
    (A ∩ B) \ C ⊆ ⋃ i, Gp i

theorem HasMeetRows.confine {φ : Semiflow X} {A B C : Set X}
    (hcert : φ.HasMeetRows A B C) (hC : IsClosed C)
    (hInvA : φ.Invariant A) (hInvB : φ.Invariant B)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    {γ : ℝ → X} (horb : φ.CompleteOrbit γ)
    {s t : ℝ} (hconf : ∀ u, s ≤ u → u ≤ t → γ u ∈ A ∩ B) :
    ∀ u, s ≤ u → u ≤ t → γ u ∈ C := by
  classical
  obtain ⟨n, ℓ, ε, F, Gp, hε, hrow, hGcl, hGF, hGz, hcov⟩ := hcert
  intro u hsu hut
  have hcont : Continuous γ := horb.continuous htraj
  have hAB : ∀ v, u ≤ v → γ v ∈ A ∩ B := fun v hv =>
    ⟨horb.forward_mem hInvA hv (hconf u hsu hut).1,
     horb.forward_mem hInvB hv (hconf u hsu hut).2⟩

  have hhit : ∀ w, u < w → ∃ v, u < v ∧ v < w ∧ γ v ∈ C := by
    intro w huw
    by_contra hno
    push Not at hno
    set w₀ : ℝ := u + (w - u) / 3 with hw₀def
    set w₁ : ℝ := u + (w - u) / 3 * 2 with hw₁def
    have hw₀₁ : w₀ < w₁ := by rw [hw₀def, hw₁def]; linarith
    have hwin : ∀ v ∈ Set.Icc w₀ w₁, u < v ∧ v < w := by
      intro v hv
      obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hv
      rw [hw₀def] at h1
      rw [hw₁def] at h2
      exact ⟨by linarith, by linarith⟩
    have hcover : Set.Icc w₀ w₁ ⊆ ⋃ i, (Set.Icc w₀ w₁ ∩ γ ⁻¹' Gp i) := by
      intro v hv
      obtain ⟨huv, hvw⟩ := hwin v hv
      have hres : γ v ∈ (A ∩ B) \ C := ⟨hAB v huv.le, hno v huv hvw⟩
      obtain ⟨i, hmem⟩ := Set.mem_iUnion.mp (hcov hres)
      exact Set.mem_iUnion.mpr ⟨i, hv, hmem⟩
    have hclosed : ∀ i, IsClosed (Set.Icc w₀ w₁ ∩ γ ⁻¹' Gp i) :=
      fun i => isClosed_Icc.inter ((hGcl i).preimage hcont)
    obtain ⟨i, z₀, z₁, hz01, hzsub⟩ :=
      exists_Icc_subset_of_closed_cover hclosed hw₀₁ hcover
    have hzG : ∀ v ∈ Set.Icc z₀ z₁, γ v ∈ Gp i := fun v hv => (hzsub hv).2

    set t' : ℝ≥0 := (z₁ - z₀).toNNReal with ht'def
    have ht'coe : (t' : ℝ) = z₁ - z₀ := Real.coe_toNNReal _ (by linarith)
    have hstay : ∀ s' : ℝ≥0, s' ≤ t' → φ.flow s' (γ z₀) ∈ F i := by
      intro s' hs'
      have hs'le : (s' : ℝ) ≤ z₁ - z₀ := by
        rw [← ht'coe]; exact NNReal.coe_le_coe.mpr hs'
      have hflow : φ.flow s' (γ z₀) = γ (z₀ + (s' : ℝ)) := (horb z₀ s').symm
      rw [hflow]
      exact hGF i (hzG _ (Set.mem_Icc.mpr
        ⟨by linarith [s'.coe_nonneg], by linarith⟩))
    have hgrow := hrow i (γ z₀)
      (hGF i (hzG z₀ (Set.left_mem_Icc.mpr hz01.le))) t' hstay
    have hend : φ.flow t' (γ z₀) = γ z₁ := by
      have h := horb z₀ t'
      rw [ht'coe] at h
      have harith : z₀ + (z₁ - z₀) = z₁ := by ring
      rw [harith] at h
      exact h.symm
    rw [hend, hGz i (γ z₀) (hzG z₀ (Set.left_mem_Icc.mpr hz01.le)),
        hGz i (γ z₁) (hzG z₁ (Set.right_mem_Icc.mpr hz01.le))] at hgrow
    have hpos : 0 < ε i * (t' : ℝ) := by
      refine mul_pos (hε i) ?_
      rw [ht'coe]; linarith
    linarith

  have hpre : IsClosed (γ ⁻¹' C) := hC.preimage hcont
  have hucl : u ∈ closure (γ ⁻¹' C) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨v, huv, hvw, hvC⟩ := hhit (u + δ) (by linarith)
    refine ⟨v, hvC, ?_⟩
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  rw [hpre.closure_eq] at hucl
  exact hucl

theorem hMeet_of_meetRows {φ : Semiflow X} (D : Set X) {β : Type*}
    {blocks : β → Set X}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hclosed : ∀ b, IsClosed (blocks b))
    (hInv : ∀ b, φ.Invariant (blocks b))
    (hcert : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      φ.HasMeetRows (blocks a) (blocks b) (blocks c)) :
    ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c := by
  intro a b
  obtain ⟨c, hsub, hrows⟩ := hcert a b
  exact ⟨c, hsub, fun γ horb _ s t hconf =>
    hrows.confine (hclosed c) (hInv a) (hInv b) htraj horb hconf⟩

end MeetRows

section Combined

variable {Vtx ι β : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [PartialOrder ι] [Finite ι]

theorem qMorseDischarge_sound_rowComplete (φ : Semiflow X) (D : Set X)
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
    (hBcomp : ∀ b : β, IsCompact (blocks b))
    (hBsubD : ∀ b : β, blocks b ⊆ D)
    (hBfacet : ∀ b : β, φ.HasFacetRows D (blocks b))
    (hBmargin : ∀ b : β, φ.HasMarginRows D (blocks b))
    (hBmeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      φ.HasMeetRows (blocks a) (blocks b) (blocks c)) :
    MorseSat φ D ρ := by
  have hInv : ∀ b : β, φ.Invariant (blocks b) := fun b =>
    invariant_of_boundaryDwell (hBcomp b).isClosed htraj
      ((hBfacet b).boundaryDwell (hBsubD b) hDInv htraj)
  exact qMorseDischarge_sound_rowsFloor φ D ρ cells hmap blocks emb cover
    bD hD hflow htraj hDInv hcells hContain hOverlap hTransitCert hConv
    hMono hbD hJoin hcover hcellsSup horder
    (hMeet_of_meetRows D htraj (fun b => (hBcomp b).isClosed) hInv hBmeet)
    hBcomp hBsubD hBfacet hBmargin

end Combined

end Semiflow

namespace Grid

open scoped NNReal
open Set Topology

variable {d : ℕ} (G : Grid d)

theorem isClosed_facetBox (p : G.FacetData) : IsClosed (G.facetBox p) :=
  (G.isClosed_cell p.1).inter
    (isClosed_eq (continuous_apply p.2.1) continuous_const)

theorem blockRegion_inter_subset (A B : Finset G.CellIdx) :
    G.blockRegion (A ∩ B) ⊆ G.blockRegion A ∩ G.blockRegion B := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := G.mem_blockRegion_iff.mp hx
  obtain ⟨hcA, hcB⟩ := Finset.mem_inter.mp hc
  exact ⟨G.mem_blockRegion_iff.mpr ⟨c, hcA, hxc⟩,
    G.mem_blockRegion_iff.mpr ⟨c, hcB, hxc⟩⟩

theorem hasMeetRows_of_rows (φ : Semiflow (Fin d → ℝ))
    (A B : Finset G.CellIdx)
    (ε : G.FacetData → ℝ) (F : G.FacetData → Set (Fin d → ℝ))
    (hε : ∀ f, G.IsFacet A f → 0 < ε f)
    (hF : ∀ f, G.IsFacet A f → ∀ x ∈ G.facetBox f, F f ∈ 𝓝 x)
    (hrow : ∀ f, G.IsFacet A f → ∀ x ∈ F f, ∀ t : ℝ≥0,
      (∀ s ≤ t, φ.flow s x ∈ F f) →
      G.obs f x + ε f * (t : ℝ) ≤ G.obs f (φ.flow t x)) :
    φ.HasMeetRows (G.blockRegion A) (G.blockRegion B)
      (G.blockRegion (A ∩ B)) := by
  classical
  refine ⟨Fintype.card {f : G.FacetData // G.IsFacet A f},
    fun i => G.obs ((Fintype.equivFin _).symm i).1,
    fun i => ε ((Fintype.equivFin _).symm i).1,
    fun i => F ((Fintype.equivFin _).symm i).1,
    fun i => G.facetBox ((Fintype.equivFin _).symm i).1,
    fun i => hε _ ((Fintype.equivFin _).symm i).2,
    fun i => hrow _ ((Fintype.equivFin _).symm i).2,
    fun i => G.isClosed_facetBox _,
    fun i x hx => mem_of_mem_nhds
      (hF _ ((Fintype.equivFin _).symm i).2 x hx),
    fun i x hx => G.obs_eq_zero_of_mem_facetBox hx,
    ?_⟩
  rintro x ⟨⟨hxA, hxB⟩, hxC⟩
  obtain ⟨α, hαA, hxα⟩ := G.mem_blockRegion_iff.mp hxA
  obtain ⟨b, hbB, hxb⟩ := G.mem_blockRegion_iff.mp hxB
  have hbnA : b ∉ A := fun hbA => hxC
    (G.mem_blockRegion_iff.mpr ⟨b, Finset.mem_inter.mpr ⟨hbA, hbB⟩, hxb⟩)
  obtain ⟨a, k, s, hfac, hbox, -⟩ := G.exists_active_facet hαA hbnA hxα hxb
  exact Set.mem_iUnion.mpr
    ⟨Fintype.equivFin {f : G.FacetData // G.IsFacet A f} ⟨(a, k, s), hfac⟩,
     by simpa using hbox⟩

end Grid

end Qtsl
end PPLC

#print axioms PPLC.Qtsl.interior_union_eq_empty
#print axioms PPLC.Qtsl.interior_biUnion_eq_empty
#print axioms PPLC.Qtsl.interior_iUnion_eq_empty
#print axioms PPLC.Qtsl.exists_Icc_subset_of_closed_cover
#print axioms PPLC.Qtsl.Semiflow.CompleteOrbit.continuous
#print axioms PPLC.Qtsl.Semiflow.HasMeetRows.confine
#print axioms PPLC.Qtsl.Semiflow.hMeet_of_meetRows
#print axioms PPLC.Qtsl.Semiflow.qMorseDischarge_sound_rowComplete
#print axioms PPLC.Qtsl.Grid.isClosed_facetBox
#print axioms PPLC.Qtsl.Grid.blockRegion_inter_subset
#print axioms PPLC.Qtsl.Grid.hasMeetRows_of_rows
