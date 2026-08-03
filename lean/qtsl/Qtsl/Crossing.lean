import Qtsl.Discharge
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Per-facet crossing certificates

Sharpens the fibre-disjointness residue to the shape checker rows come
in: the overlap of two fibre unions is a finite union of shared facets,
each carrying its own facet-sign row block with its own observable.
This module composes the per-facet certificates into the single
overlap-transit certificate the discharge development consumes —
including the genuinely non-pointwise composition step.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology

variable {X : Type*}

def HasCrossingCert (φ : Semiflow X) (O : Set X) : Prop :=
  ∃ (V : X → ℝ) (c : ℝ), (∀ x ∈ O, V x = c) ∧
    ∀ x ∈ O, ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, 0 < s → s ≤ δ → V (φ.flow s x) < c

theorem hasCrossingCert_empty {φ : Semiflow X} : φ.HasCrossingCert ∅ :=
  ⟨fun _ => 0, 0, fun x hx => absurd hx (Set.notMem_empty x),
    fun x hx => absurd hx (Set.notMem_empty x)⟩

theorem HasCrossingCert.maxInv_empty {φ : Semiflow X} {O : Set X}
    (h : φ.HasCrossingCert O) : φ.MaxInv O = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hconf := maxInv_forward_confined hx
  obtain ⟨V, c, hlevel, hcross⟩ := h
  have hx0 : x ∈ O := by have h0 := hconf 0; rwa [φ.flow_zero] at h0
  obtain ⟨δ, hδ, hV⟩ := hcross x hx0
  exact absurd (hlevel _ (hconf δ)) (ne_of_lt (hV δ hδ le_rfl))

theorem not_forward_confined_of_crossingCerts [TopologicalSpace X]
    {φ : Semiflow X} {κ : Type*} [Finite κ] {O : κ → Set X}
    (hclosed : ∀ k, IsClosed (O k))
    (hcert : ∀ k, φ.HasCrossingCert (O k))
    {x : X} (htraj : ContinuousAt (fun t : ℝ≥0 => φ.flow t x) 0) :
    ¬ ∀ t : ℝ≥0, φ.flow t x ∈ ⋃ k, O k := by
  intro hconf
  have hx0 : x ∈ ⋃ k, O k := by have h := hconf 0; rwa [φ.flow_zero] at h
  obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hx0
  haveI : Nonempty κ := ⟨k₀⟩
  haveI : Fintype κ := Fintype.ofFinite κ

  have hout : ∀ k : κ, ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, 0 < s → s ≤ δ → φ.flow s x ∉ O k := by
    intro k
    by_cases hxk : x ∈ O k
    ·
      obtain ⟨V, c, hlevel, hcross⟩ := hcert k
      obtain ⟨δ, hδ, hV⟩ := hcross x hxk
      exact ⟨δ, hδ, fun s hs hsδ hmem =>
        absurd (hlevel _ hmem) (ne_of_lt (hV s hs hsδ))⟩
    ·
      have hmem : (fun s : ℝ≥0 => φ.flow s x) ⁻¹' (O k)ᶜ ∈ 𝓝 (0 : ℝ≥0) := by
        refine htraj.preimage_mem_nhds ?_
        rw [φ.flow_zero]
        exact (hclosed k).isOpen_compl.mem_nhds hxk
      obtain ⟨ε, hε, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hmem
      refine ⟨ε / 2, by positivity, fun s _ hsδ hmemO => ?_⟩
      have hlt : s < ε := lt_of_le_of_lt hsδ (NNReal.half_lt_self hε.ne')
      exact hsub hlt hmemO
  choose δ hδpos hδout using hout

  have hpos : 0 < Finset.univ.inf' Finset.univ_nonempty δ :=
    (Finset.lt_inf'_iff _).mpr fun k _ => hδpos k
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hconf (Finset.univ.inf' Finset.univ_nonempty δ))
  exact hδout k _ hpos (Finset.inf'_le δ (Finset.mem_univ k)) hk

section FiberDisjoint

variable {Vtx ι : Type*}

theorem disjoint_maxInv_of_crossingCerts [TopologicalSpace X] [Finite ι]
    {φ : Semiflow X} {cells : ι → Set X} {hmap : ι → Option Vtx}
    (hclosed : ∀ i, IsClosed (cells i))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    {v w : Vtx}
    (hcert : ∀ i j, hmap i = some v → hmap j = some w →
      φ.HasCrossingCert (cells i ∩ cells j)) :
    Disjoint (φ.MaxInv (fiberUnion cells hmap v))
      (φ.MaxInv (fiberUnion cells hmap w)) := by
  rw [Set.disjoint_left]
  intro x h1 h2

  have hconf : ∀ t : ℝ≥0, φ.flow t x ∈
      ⋃ p : {p : ι × ι // hmap p.1 = some v ∧ hmap p.2 = some w},
        cells p.val.1 ∩ cells p.val.2 := by
    intro t
    obtain ⟨i, hi, hmemv⟩ :=
      Set.mem_iUnion₂.mp (maxInv_forward_confined h1 t)
    obtain ⟨j, hj, hmemw⟩ :=
      Set.mem_iUnion₂.mp (maxInv_forward_confined h2 t)
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hi, hj⟩, hmemv, hmemw⟩
  exact not_forward_confined_of_crossingCerts
    (κ := {p : ι × ι // hmap p.1 = some v ∧ hmap p.2 = some w})
    (O := fun p => cells p.val.1 ∩ cells p.val.2)
    (fun p => (hclosed p.val.1).inter (hclosed p.val.2))
    (fun p => hcert p.val.1 p.val.2 p.prop.1 p.prop.2)
    ((htraj x).continuousAt) hconf

end FiberDisjoint

section Combined

variable {Vtx ι : Type*} [PseudoMetricSpace X] [T2Space X] [PartialOrder Vtx]
  [Finite ι]

theorem qMorseDischarge_sound_cellCover (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hCross : ∀ v w, v ≠ w → ∀ i j, hmap i = some v → hmap j = some w →
      φ.HasCrossingCert (cells i ∩ cells j))
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hOrder : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ φ.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧ alphaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap w)) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound φ D ρ cells hmap hContain
    (fun _ => maxInv_isCompact hflow (fiberUnion_isCompact hcells _))
    (fun v w hvw => disjoint_maxInv_of_crossingCerts
      (fun i => (hcells i).isClosed) htraj (hCross v w hvw))
    (crCover_assemble hCell hTransitCert)
    hOrder

end Combined

theorem hasCrossingCert_of_deriv {φ : Semiflow X} {O : Set X}
    (V : X → ℝ) (c : ℝ) (hlevel : ∀ x ∈ O, V x = c)
    (hderiv : ∀ x ∈ O, ∃ d : ℝ, d < 0 ∧
      HasDerivWithinAt (fun s : ℝ => V (φ.flow s.toNNReal x)) d (Set.Ici 0) 0) :
    φ.HasCrossingCert O := by
  refine ⟨V, c, hlevel, fun x hx => ?_⟩
  obtain ⟨d, hd, hD⟩ := hderiv x hx
  set g : ℝ → ℝ := fun s => V (φ.flow s.toNNReal x) with hg
  have hg0 : g 0 = c := by
    rw [hg]
    dsimp only
    rw [Real.toNNReal_zero, φ.flow_zero]
    exact hlevel x hx

  have hIci : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hle, hne⟩
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · intro hlt
      exact ⟨le_of_lt hlt, ne_of_gt hlt⟩
  have hslope : Filter.Tendsto (slope g 0) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 d) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hD
    rwa [hIci] at h
  have hev : ∀ᶠ s in 𝓝[Set.Ioi 0] (0 : ℝ), slope g 0 s < 0 :=
    hslope.eventually (eventually_lt_nhds hd)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨(u / 2).toNNReal, Real.toNNReal_pos.mpr (half_pos hu0),
    fun s hs hsδ => ?_⟩
  have hs' : (0 : ℝ) < (s : ℝ) := NNReal.coe_pos.mpr hs
  have hsu : (s : ℝ) < u := by
    have h1 : (s : ℝ) ≤ ((u / 2).toNNReal : ℝ) := NNReal.coe_le_coe.mpr hsδ
    rw [Real.coe_toNNReal _ (le_of_lt (half_pos hu0))] at h1
    linarith
  have hslope_neg : slope g 0 (s : ℝ) < 0 := hsub ⟨hs', hsu⟩
  rw [slope_def_field, sub_zero] at hslope_neg

  have hgs : g (s : ℝ) < g 0 := by
    rcases div_neg_iff.mp hslope_neg with ⟨_, hden⟩ | ⟨hnum, _⟩
    · linarith
    · linarith
  have hval : g (s : ℝ) = V (φ.flow s x) := by
    rw [hg]
    dsimp only
    rw [Real.toNNReal_coe]
  rw [hval, hg0] at hgs
  exact hgs

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.hasCrossingCert_empty
#print axioms Qtsl.Semiflow.HasCrossingCert.maxInv_empty
#print axioms Qtsl.Semiflow.not_forward_confined_of_crossingCerts
#print axioms Qtsl.Semiflow.disjoint_maxInv_of_crossingCerts
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_cellCover
#print axioms Qtsl.Semiflow.hasCrossingCert_of_deriv

end PPLC
