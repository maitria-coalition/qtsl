import Qtsl.QtslSoundness
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Real

/-!
# Hypothesis discharge for the dynamical soundness lemmas

`QtslSoundness` states the Morse-rule soundness lemmas with analytic
gaps as interface hypotheses at their use sites. This module discharges
them from certificate-shaped data — everything additive, no statement
there changes shape:

* `HasTransitCert` — a decrease observable on a cell empties its
  maximal invariant set (`HasTransitCert.maxInv_empty`) and separates
  cells (`disjoint_maxInv`);
* `invariant_of_boundaryDwell` and `HasFacetRows.boundaryDwell` — from
  per-facet sign rows to isolating-block invariance
  (`qBlockInv_sound_of_facetRows`);
* compactness carriers (`maxInv_isCompact`, `fiberUnion_isCompact`)
  and the cover assembly `crCover_assemble` feeding
  `qMorseDischarge_sound_modelClass`.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology

variable {X : Type*}

theorem maxInv_mono {φ : Semiflow X} {C D : Set X} (h : C ⊆ D) :
    φ.MaxInv C ⊆ φ.MaxInv D := by
  rintro x ⟨γ, horb, h0, hr⟩
  exact ⟨γ, horb, h0, hr.trans h⟩

theorem maxInv_forward_confined {φ : Semiflow X} {C : Set X} {x : X}
    (hx : x ∈ φ.MaxInv C) : ∀ t : ℝ≥0, φ.flow t x ∈ C := by
  obtain ⟨γ, horb, rfl, hr⟩ := hx
  intro t
  rw [← horb 0 t]
  exact hr (Set.mem_range_self _)

theorem subset_fiberUnion {Vtx ι : Type*} {cells : ι → Set X}
    {hmap : ι → Option Vtx} {i : ι} {v : Vtx} (hi : hmap i = some v) :
    cells i ⊆ fiberUnion cells hmap v :=
  Set.subset_biUnion_of_mem (u := cells) hi

theorem invariant_univ (φ : Semiflow X) : φ.Invariant Set.univ :=
  fun _ _ _ => Set.mem_univ _

def HasTransitCert (φ : Semiflow X) (C : Set X) : Prop :=
  ∃ (V : X → ℝ) (ε : ℝ), 0 < ε ∧ BddBelow (V '' C) ∧
    ∀ x ∈ C, ∀ t : ℝ≥0,
      (∀ s : ℝ≥0, s ≤ t → φ.flow s x ∈ C) → V (φ.flow t x) ≤ V x - ε * t

theorem HasTransitCert.not_forward_confined {φ : Semiflow X} {C : Set X}
    (h : φ.HasTransitCert C) (x : X) : ¬ ∀ t : ℝ≥0, φ.flow t x ∈ C := by
  intro hx
  obtain ⟨V, ε, hε, hBdd, hDec⟩ := h
  obtain ⟨m, hm⟩ := hBdd
  have hxC : x ∈ C := by have h0 := hx 0; rwa [φ.flow_zero] at h0
  obtain ⟨n, hAr⟩ := Archimedean.arch (V x - m) hε
  rw [nsmul_eq_mul] at hAr
  have hdec := hDec x hxC ((n + 1 : ℕ) : ℝ≥0) (fun s _ => hx s)
  have hlow : m ≤ V (φ.flow ((n + 1 : ℕ) : ℝ≥0) x) := hm ⟨_, hx _, rfl⟩
  have hcoe : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcoe] at hdec
  have hexp : ε * ((n : ℝ) + 1) = ε * n + ε := by ring
  linarith

/-- A transit certificate empties the maximal invariant subset of its
cell. -/
theorem HasTransitCert.maxInv_empty {φ : Semiflow X} {C : Set X}
    (h : φ.HasTransitCert C) : φ.MaxInv C = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hx => h.not_forward_confined x (maxInv_forward_confined hx)

theorem HasTransitCert.disjoint_maxInv {φ : Semiflow X} {C₁ C₂ : Set X}
    (h : φ.HasTransitCert (C₁ ∩ C₂)) :
    Disjoint (φ.MaxInv C₁) (φ.MaxInv C₂) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  exact h.not_forward_confined x fun t =>
    ⟨maxInv_forward_confined h1 t, maxInv_forward_confined h2 t⟩

section G1

variable [TopologicalSpace X]

theorem invariant_of_boundaryDwell {φ : Semiflow X} {N : Set X}
    (hN : IsClosed N)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hdwell : ∀ x ∈ N, x ∈ frontier N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, φ.flow s x ∈ N) :
    φ.Invariant N := by

  have hdwell' : ∀ y ∈ N, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, φ.flow s y ∈ N := by
    intro y hy
    by_cases hfr : y ∈ frontier N
    · exact hdwell y hy hfr
    · have hyint : y ∈ interior N := by
        rw [hN.frontier_eq] at hfr
        simpa [hy] using hfr
      have hmem : (fun s : ℝ≥0 => φ.flow s y) ⁻¹' interior N ∈ 𝓝 (0 : ℝ≥0) := by
        refine (htraj y).continuousAt.preimage_mem_nhds ?_
        rw [φ.flow_zero]
        exact isOpen_interior.mem_nhds hyint
      obtain ⟨ε, hε, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hmem
      refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
      have hlt : s < ε := lt_of_le_of_lt hs (NNReal.half_lt_self hε.ne')
      exact interior_subset (hsub hlt)
  intro x hxN t
  by_contra hexit

  set S : Set ℝ≥0 := {u | ∀ s ≤ u, φ.flow s x ∈ N} with hS
  have h0S : (0 : ℝ≥0) ∈ S := by
    intro s hs
    rw [le_zero_iff.mp hs, φ.flow_zero]
    exact hxN
  have hne : S.Nonempty := ⟨0, h0S⟩
  have hub : ∀ u ∈ S, u ≤ t := by
    intro u hu
    by_contra hlt
    exact hexit (hu t (le_of_not_ge hlt))
  have hbdd : BddAbove S := ⟨t, hub⟩
  set T := sSup S with hT

  have hpre : ∀ s : ℝ≥0, s < T → φ.flow s x ∈ N := by
    intro s hsT
    obtain ⟨u, huS, hsu⟩ := exists_lt_of_lt_csSup hne hsT
    exact huS s hsu.le

  have hTN : φ.flow T x ∈ N := by
    by_cases hT0 : T = 0
    · rw [hT0, φ.flow_zero]; exact hxN
    · have hpos : 0 < T := pos_iff_ne_zero.mpr hT0
      have hclosed : IsClosed ((fun s : ℝ≥0 => φ.flow s x) ⁻¹' N) :=
        hN.preimage (htraj x)
      have hIio : Set.Iio T ⊆ (fun s : ℝ≥0 => φ.flow s x) ⁻¹' N :=
        fun s hs => hpre s hs
      have hTcl : T ∈ closure (Set.Iio T) := by
        rw [closure_Iio' (a := T) ⟨0, hpos⟩]
        exact Set.self_mem_Iic
      exact hclosed.closure_subset ((closure_mono hIio) hTcl)
  have hTS : T ∈ S := by
    intro s hsT
    rcases lt_or_eq_of_le hsT with hlt | heq
    · exact hpre s hlt
    · rw [heq]; exact hTN

  obtain ⟨δ, hδ, hdw⟩ := hdwell' (φ.flow T x) hTN
  have hTδS : T + δ ∈ S := by
    intro s hs
    rcases le_or_gt s T with hsT | hTs
    · exact hTS s hsT
    · have hs' : s - T ≤ δ := tsub_le_iff_left.mpr hs
      have hrepr : T + (s - T) = s := add_tsub_cancel_of_le hTs.le
      have := hdw (s - T) hs'
      rwa [← φ.flow_add, hrepr] at this
  have hTδ : T + δ ≤ T := le_csSup hbdd hTδS
  have hδ0 : δ = 0 :=
    le_zero_iff.mp (le_of_add_le_add_left (show T + δ ≤ T + 0 by simpa using hTδ))
  exact absurd hδ0 hδ.ne'

theorem qBlockInv_sound_of_dwell {φ : Semiflow X} {N X0 : Set X}
    (hN : IsClosed N)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hdwell : ∀ x ∈ N, x ∈ frontier N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, φ.flow s x ∈ N)
    (hInit : X0 ⊆ N) : φ.InvScopeSat N X0 :=
  qBlockInv_sound (invariant_of_boundaryDwell hN htraj hdwell) hInit

def HasFacetRows (φ : Semiflow X) (D N : Set X) : Prop :=
  ∃ (n : ℕ) (ℓ : Fin n → X → ℝ) (ε : Fin n → ℝ) (F : Fin n → Set X),
    (∀ i, 0 < ε i) ∧
    (∀ i, ∀ x ∈ F i, ∀ t : ℝ≥0, (∀ s ≤ t, φ.flow s x ∈ F i) →
      ℓ i x + ε i * (t : ℝ) ≤ ℓ i (φ.flow t x)) ∧
    ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N

theorem HasFacetRows.boundaryDwell {φ : Semiflow X} {D N : Set X}
    (h : φ.HasFacetRows D N) (hND : N ⊆ D) (hD : φ.Invariant D)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x) :
    ∀ x ∈ N, x ∈ frontier N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, φ.flow s x ∈ N := by
  obtain ⟨n, ℓ, ε, F, hε, hrow, hlocal⟩ := h
  intro x hxN hxfr
  obtain ⟨A, U, hU, hA, hwedge⟩ := hlocal x hxfr

  have hW : U ∩ ⋂ i ∈ A, F i ∈ 𝓝 x :=
    Filter.inter_mem hU
      ((Filter.biInter_mem A.toFinite).mpr fun i hi => (hA i hi).2)
  have hpre : (fun s : ℝ≥0 => φ.flow s x) ⁻¹' (U ∩ ⋂ i ∈ A, F i) ∈
      𝓝 (0 : ℝ≥0) := by
    refine (htraj x).continuousAt.preimage_mem_nhds ?_
    rw [φ.flow_zero]
    exact hW
  obtain ⟨δ₀, hδ₀, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hpre
  refine ⟨δ₀ / 2, by positivity, fun s hs => ?_⟩
  have hprefix : ∀ s' : ℝ≥0, s' ≤ s → φ.flow s' x ∈ U ∩ ⋂ i ∈ A, F i :=
    fun s' hs' =>
      hsub (lt_of_le_of_lt (hs'.trans hs) (NNReal.half_lt_self hδ₀.ne'))
  refine hwedge _ (hprefix s le_rfl).1 (hD x (hND hxN) s) fun i hi => ?_

  have hxF : x ∈ F i := mem_of_mem_nhds (hA i hi).2
  have hconf : ∀ s' : ℝ≥0, s' ≤ s → φ.flow s' x ∈ F i := fun s' hs' =>
    Set.mem_iInter₂.mp (hprefix s' hs').2 i hi
  have hgrow := hrow i x hxF s hconf
  have h0 : ℓ i x = 0 := (hA i hi).1
  have hεs : (0 : ℝ) ≤ ε i * (s : ℝ) := mul_nonneg (hε i).le s.coe_nonneg
  linarith

/-- Block invariance discharged from per-facet sign rows. -/
theorem qBlockInv_sound_of_facetRows {φ : Semiflow X} {D N X0 : Set X}
    (hN : IsClosed N)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hND : N ⊆ D) (hD : φ.Invariant D) (hrows : φ.HasFacetRows D N)
    (hInit : X0 ⊆ N) : φ.InvScopeSat N X0 :=
  qBlockInv_sound_of_dwell hN htraj (hrows.boundaryDwell hND hD htraj) hInit

end G1

section G3

variable [TopologicalSpace X]

theorem maxInv_isCompact [T2Space X] {φ : Semiflow X} {C : Set X}
    (hflow : ∀ t, Continuous (φ.flow t)) (hC : IsCompact C) :
    IsCompact (φ.MaxInv C) := by
  classical
  set K : Set (ℝ → X) :=
    {γ : ℝ → X | φ.CompleteOrbit γ} ∩ Set.univ.pi (fun _ : ℝ => C) with hK
  have hKc : IsCompact K := by
    have hpi : IsCompact (Set.univ.pi fun _ : ℝ => C) :=
      isCompact_univ_pi fun _ => hC
    have hcl : IsClosed {γ : ℝ → X | φ.CompleteOrbit γ} := by
      have hrw : {γ : ℝ → X | φ.CompleteOrbit γ} =
          ⋂ (s : ℝ) (t : ℝ≥0), {γ : ℝ → X | γ (s + t) = φ.flow t (γ s)} := by
        ext γ
        simp only [Set.mem_setOf_eq, Set.mem_iInter, CompleteOrbit]
      rw [hrw]
      exact isClosed_iInter fun s => isClosed_iInter fun t =>
        isClosed_eq (continuous_apply _) ((hflow t).comp (continuous_apply s))
    exact hpi.inter_left hcl
  have himg : φ.MaxInv C = (fun γ : ℝ → X => γ 0) '' K := by
    ext x
    constructor
    · rintro ⟨γ, horb, h0, hr⟩
      exact ⟨γ, ⟨horb, fun s _ => hr (Set.mem_range_self s)⟩, h0⟩
    · rintro ⟨γ, ⟨horb, hpiC⟩, h0⟩
      refine ⟨γ, horb, h0, ?_⟩
      rintro y ⟨s, rfl⟩
      exact hpiC s (Set.mem_univ s)
  rw [himg]
  exact hKc.image (continuous_apply 0)

theorem fiberUnion_isCompact {Vtx ι : Type*} [Finite ι]
    {cells : ι → Set X} {hmap : ι → Option Vtx}
    (hcells : ∀ i, IsCompact (cells i)) (v : Vtx) :
    IsCompact (fiberUnion cells hmap v) :=
  (Set.toFinite {i | hmap i = some v}).isCompact_biUnion fun i _ => hcells i

end G3

section G5

variable {Vtx ι : Type*} [PseudoMetricSpace X]

theorem crCover_assemble {φ : Semiflow X} {D : Set X}
    {cells : ι → Set X} {hmap : ι → Option Vtx}
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hTransit : ∀ i, hmap i = none → φ.HasTransitCert (cells i)) :
    ∀ x ∈ D, ChainRecurrentIn φ D x →
      ∃ v, x ∈ φ.MaxInv (fiberUnion cells hmap v) := by
  intro x hx hcr
  obtain ⟨i, hi⟩ := hCell x hx hcr
  cases hv : hmap i with
  | none =>
      rw [(hTransit i hv).maxInv_empty] at hi
      exact absurd hi (Set.notMem_empty x)
  | some v =>
      exact ⟨v, maxInv_mono (subset_fiberUnion hv) hi⟩

end G5

section Combined

variable {Vtx ι : Type*} [PseudoMetricSpace X] [T2Space X] [PartialOrder Vtx]
  [Finite ι]

/-- The Morse-discharge soundness theorem with its analytic hypotheses
discharged for the model class. -/
theorem qMorseDischarge_sound_modelClass (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hOrder : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ φ.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧ alphaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap w)) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound φ D ρ cells hmap hContain
    (fun _ => maxInv_isCompact hflow (fiberUnion_isCompact hcells _))
    (fun v w hvw => (hOverlap v w hvw).disjoint_maxInv)
    (crCover_assemble hCell hTransitCert)
    hOrder

end Combined

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.maxInv_mono
#print axioms Qtsl.Semiflow.maxInv_forward_confined
#print axioms Qtsl.Semiflow.HasTransitCert.not_forward_confined
#print axioms Qtsl.Semiflow.HasTransitCert.maxInv_empty
#print axioms Qtsl.Semiflow.HasTransitCert.disjoint_maxInv
#print axioms Qtsl.Semiflow.invariant_of_boundaryDwell
#print axioms Qtsl.Semiflow.qBlockInv_sound_of_dwell
#print axioms Qtsl.Semiflow.invariant_univ
#print axioms Qtsl.Semiflow.HasFacetRows.boundaryDwell
#print axioms Qtsl.Semiflow.qBlockInv_sound_of_facetRows
#print axioms Qtsl.Semiflow.maxInv_isCompact
#print axioms Qtsl.Semiflow.fiberUnion_isCompact
#print axioms Qtsl.Semiflow.crCover_assemble
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_modelClass

end PPLC
