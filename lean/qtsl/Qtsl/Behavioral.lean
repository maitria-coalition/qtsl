import Qtsl.DiniProfile
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The behavioural floor

The discharge stack's base restated over solution-trajectory sets: a
`Behavior` is a shift-closed set of forward trajectories, with no
existence or uniqueness demanded — properties quantify over all
trajectories that solve the dynamics, rather than assuming a
well-posed flow. Membership and monotonicity lemmas connect behaviours
to the semiflow stratum, and the module defines the interfaces the
switched/hybrid and timed layers build on.
-/

namespace PPLC
namespace Qtsl

open scoped NNReal
open Set Topology

variable {X : Type*}

structure Behavior (X : Type*) where

  fwd : Set (ℝ≥0 → X)

  cpl : Set (ℝ → X)

  shift_fwd : ∀ γ ∈ fwd, ∀ s : ℝ≥0, (fun t : ℝ≥0 => γ (s + t)) ∈ fwd

  shift_cpl : ∀ γ ∈ cpl, ∀ s : ℝ, (fun t : ℝ => γ (t + s)) ∈ cpl

  restrict_cpl : ∀ γ ∈ cpl, (fun t : ℝ≥0 => γ (t : ℝ)) ∈ fwd

namespace Behavior

def Invariant (B : Behavior X) (S : Set X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ S → ∀ t : ℝ≥0, γ t ∈ S

def SafetySat (B : Behavior X) (X0 Bad : Set X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ X0 → ∀ t : ℝ≥0, γ t ∉ Bad

def InvScopeSat (B : Behavior X) (S X0 : Set X) : Prop :=
  B.Invariant S ∧ X0 ⊆ S

def MaxInv (B : Behavior X) (C : Set X) : Set X :=
  {x | ∃ γ ∈ B.cpl, γ 0 = x ∧ Set.range γ ⊆ C}

theorem maxInv_subset (B : Behavior X) (C : Set X) : B.MaxInv C ⊆ C := by
  rintro x ⟨γ, -, rfl, hr⟩
  exact hr (Set.mem_range_self 0)

theorem maxInv_mono {B : Behavior X} {C D : Set X} (h : C ⊆ D) :
    B.MaxInv C ⊆ B.MaxInv D := by
  rintro x ⟨γ, hγ, h0, hr⟩
  exact ⟨γ, hγ, h0, hr.trans h⟩

theorem mem_maxInv_of_sol {B : Behavior X} {γ : ℝ → X} {C : Set X}
    (hγ : γ ∈ B.cpl) (hr : Set.range γ ⊆ C) (s : ℝ) : γ s ∈ B.MaxInv C := by
  refine ⟨fun u => γ (u + s), B.shift_cpl γ hγ s, by simp, ?_⟩
  rintro y ⟨u, rfl⟩
  exact hr ⟨u + s, rfl⟩

def IsInvariantIn (B : Behavior X) (S : Set X) : Prop :=
  S ⊆ B.MaxInv S

theorem maxInv_isInvariant (B : Behavior X) (C : Set X) :
    B.IsInvariantIn (B.MaxInv C) := by
  rintro x ⟨γ, hγ, rfl, hr⟩
  refine ⟨γ, hγ, rfl, ?_⟩
  rintro y ⟨s, rfl⟩
  exact mem_maxInv_of_sol hγ hr s

section Chains

variable [PseudoMetricSpace X]

inductive EpsChainIn (B : Behavior X) (D : Set X) (ε : ℝ) (T : ℝ≥0) :
    X → X → Prop
  | step {x y : X} {γ : ℝ≥0 → X} {t : ℝ≥0} (hγ : γ ∈ B.fwd) (hγ0 : γ 0 = x)
      (hx : x ∈ D) (hy : y ∈ D) (ht : T ≤ t) (hjump : dist (γ t) y < ε) :
      EpsChainIn B D ε T x y
  | trans {x y z : X} (h1 : EpsChainIn B D ε T x y)
      (h2 : EpsChainIn B D ε T y z) : EpsChainIn B D ε T x z

def ChainRecurrentIn (B : Behavior X) (D : Set X) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ T : ℝ≥0, EpsChainIn B D ε T x x

end Chains

section Judgment

variable [PseudoMetricSpace X] {Vtx : Type*}

open Semiflow (alphaSet omegaSet)

structure MorseWitness (B : Behavior X) (D : Set X) [PartialOrder Vtx]
    (ρ : Vtx → Set X) where

  M : Vtx → Set X

  isCompact : ∀ v, IsCompact (M v)

  invariant : ∀ v, B.IsInvariantIn (M v)

  located : ∀ v, M v ⊆ ρ v

  disjoint : ∀ v w, v ≠ w → Disjoint (M v) (M w)

  crCover : ∀ x ∈ D, B.ChainRecurrentIn D x → ∃ v, x ∈ M v

  order : ∀ γ ∈ B.cpl, Set.range γ ⊆ D →
    (∀ v, ¬ Set.range γ ⊆ M v) →
    ∃ v w, w < v ∧ alphaSet γ ⊆ M v ∧ omegaSet γ ⊆ M w

def MorseSat (B : Behavior X) (D : Set X) [PartialOrder Vtx]
    (ρ : Vtx → Set X) : Prop :=
  Nonempty (MorseWitness B D ρ)

end Judgment

def HasTransitCert (B : Behavior X) (C : Set X) : Prop :=
  ∃ (V : X → ℝ) (ε : ℝ), 0 < ε ∧ BddBelow (V '' C) ∧
    ∀ γ ∈ B.fwd, ∀ t : ℝ≥0, (∀ s ≤ t, γ s ∈ C) →
      V (γ t) ≤ V (γ 0) - ε * t

theorem HasTransitCert.not_forward_confined {B : Behavior X} {C : Set X}
    (h : B.HasTransitCert C) {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) :
    ¬ ∀ t : ℝ≥0, γ t ∈ C := by
  intro hconf
  obtain ⟨V, ε, hε, hBdd, hDec⟩ := h
  obtain ⟨m, hm⟩ := hBdd
  obtain ⟨n, hAr⟩ := Archimedean.arch (V (γ 0) - m) hε
  rw [nsmul_eq_mul] at hAr
  have hdec := hDec γ hγ ((n + 1 : ℕ) : ℝ≥0) (fun s _ => hconf s)
  have hlow : m ≤ V (γ ((n + 1 : ℕ) : ℝ≥0)) := hm ⟨_, hconf _, rfl⟩
  have hcoe : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcoe] at hdec
  have hexp : ε * ((n : ℝ) + 1) = ε * n + ε := by ring
  linarith

theorem HasTransitCert.maxInv_empty {B : Behavior X} {C : Set X}
    (h : B.HasTransitCert C) : B.MaxInv C = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨γ, hγ, rfl, hr⟩
  exact h.not_forward_confined (B.restrict_cpl γ hγ) fun t => hr ⟨(t : ℝ), rfl⟩

def HasCrossingCert (B : Behavior X) (O : Set X) : Prop :=
  ∃ (V : X → ℝ) (c : ℝ), (∀ x ∈ O, V x = c) ∧
    ∀ γ ∈ B.fwd, γ 0 ∈ O → ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, 0 < s → s ≤ δ → V (γ s) < c

theorem HasCrossingCert.maxInv_empty {B : Behavior X} {O : Set X}
    (h : B.HasCrossingCert O) : B.MaxInv O = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨γ, hγ, rfl, hr⟩
  obtain ⟨V, c, hlevel, hcross⟩ := h
  have hfwd := B.restrict_cpl γ hγ
  have h0 : (fun t : ℝ≥0 => γ (t : ℝ)) 0 ∈ O := by
    simpa using hr ⟨(0 : ℝ), rfl⟩
  obtain ⟨δ, hδ, hV⟩ := hcross _ hfwd h0
  exact absurd (hlevel _ (hr ⟨((δ : ℝ≥0) : ℝ), rfl⟩))
    (ne_of_lt (hV δ hδ le_rfl))

theorem not_forward_confined_of_crossingCerts [TopologicalSpace X]
    {B : Behavior X} {κ : Type*} [Finite κ] {O : κ → Set X}
    (hclosed : ∀ k, IsClosed (O k))
    (hcert : ∀ k, B.HasCrossingCert (O k))
    {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) (hγc : ContinuousAt γ 0) :
    ¬ ∀ t : ℝ≥0, γ t ∈ ⋃ k, O k := by
  intro hconf
  obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp (hconf 0)
  haveI : Nonempty κ := ⟨k₀⟩
  haveI : Fintype κ := Fintype.ofFinite κ
  have hout : ∀ k : κ, ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, 0 < s → s ≤ δ → γ s ∉ O k := by
    intro k
    by_cases hxk : γ 0 ∈ O k
    · obtain ⟨V, c, hlevel, hcross⟩ := hcert k
      obtain ⟨δ, hδ, hV⟩ := hcross γ hγ hxk
      exact ⟨δ, hδ, fun s hs hsδ hmem =>
        absurd (hlevel _ hmem) (ne_of_lt (hV s hs hsδ))⟩
    · have hmem : γ ⁻¹' (O k)ᶜ ∈ 𝓝 (0 : ℝ≥0) :=
        hγc.preimage_mem_nhds ((hclosed k).isOpen_compl.mem_nhds hxk)
      obtain ⟨ε, hε, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hmem
      refine ⟨ε / 2, by positivity, fun s _ hsδ hmemO => ?_⟩
      have hlt : s < ε := lt_of_le_of_lt hsδ (NNReal.half_lt_self hε.ne')
      exact hsub hlt hmemO
  choose δ hδpos hδout using hout
  have hpos : 0 < Finset.univ.inf' Finset.univ_nonempty δ :=
    (Finset.lt_inf'_iff _).mpr fun k _ => hδpos k
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
    (hconf (Finset.univ.inf' Finset.univ_nonempty δ))
  exact hδout k _ hpos (Finset.inf'_le δ (Finset.mem_univ k)) hk

def HasFacetRows (B : Behavior X) [TopologicalSpace X] (D N : Set X) : Prop :=
  ∃ (n : ℕ) (ℓ : Fin n → X → ℝ) (ε : Fin n → ℝ) (F : Fin n → Set X),
    (∀ i, 0 < ε i) ∧
    (∀ i, ∀ γ ∈ B.fwd, γ 0 ∈ F i → ∀ t : ℝ≥0, (∀ s ≤ t, γ s ∈ F i) →
      ℓ i (γ 0) + ε i * (t : ℝ) ≤ ℓ i (γ t)) ∧
    ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N

section Safety

variable [TopologicalSpace X]

theorem invariant_of_boundaryDwell {B : Behavior X} {N : Set X}
    (hN : IsClosed N)
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hdwell : ∀ γ ∈ B.fwd, γ 0 ∈ N → γ 0 ∈ frontier N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, γ s ∈ N) :
    B.Invariant N := by

  have hdwell' : ∀ γ ∈ B.fwd, γ 0 ∈ N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, γ s ∈ N := by
    intro γ hγ h0
    by_cases hfr : γ 0 ∈ frontier N
    · exact hdwell γ hγ h0 hfr
    · have hint : γ 0 ∈ interior N := by
        rw [hN.frontier_eq] at hfr
        simpa [h0] using hfr
      have hmem : γ ⁻¹' interior N ∈ 𝓝 (0 : ℝ≥0) :=
        ((hcont γ hγ).continuousAt).preimage_mem_nhds
          (isOpen_interior.mem_nhds hint)
      obtain ⟨ε, hε, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hmem
      refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
      have hlt : s < ε := lt_of_le_of_lt hs (NNReal.half_lt_self hε.ne')
      exact interior_subset (hsub hlt)
  intro γ hγ h0 t
  by_contra hexit
  set S : Set ℝ≥0 := {u | ∀ s ≤ u, γ s ∈ N} with hS
  have h0S : (0 : ℝ≥0) ∈ S := by
    intro s hs
    rw [le_zero_iff.mp hs]
    exact h0
  have hne : S.Nonempty := ⟨0, h0S⟩
  have hub : ∀ u ∈ S, u ≤ t := by
    intro u hu
    by_contra hlt
    exact hexit (hu t (le_of_not_ge hlt))
  have hbdd : BddAbove S := ⟨t, hub⟩
  set T := sSup S with hT
  have hpre : ∀ s : ℝ≥0, s < T → γ s ∈ N := by
    intro s hsT
    obtain ⟨u, huS, hsu⟩ := exists_lt_of_lt_csSup hne hsT
    exact huS s hsu.le
  have hTN : γ T ∈ N := by
    by_cases hT0 : T = 0
    · rw [hT0]; exact h0
    · have hpos : 0 < T := pos_iff_ne_zero.mpr hT0
      have hclosed : IsClosed (γ ⁻¹' N) := hN.preimage (hcont γ hγ)
      have hIio : Set.Iio T ⊆ γ ⁻¹' N := fun s hs => hpre s hs
      have hTcl : T ∈ closure (Set.Iio T) := by
        rw [closure_Iio' (a := T) ⟨0, hpos⟩]
        exact Set.self_mem_Iic
      exact hclosed.closure_subset ((closure_mono hIio) hTcl)
  have hTS : T ∈ S := by
    intro s hsT
    rcases lt_or_eq_of_le hsT with hlt | heq
    · exact hpre s hlt
    · rw [heq]; exact hTN

  obtain ⟨δ, hδ, hdw⟩ := hdwell' _ (B.shift_fwd γ hγ T) (by simpa using hTN)
  have hTδS : T + δ ∈ S := by
    intro s hs
    rcases le_or_gt s T with hsT | hTs
    · exact hTS s hsT
    · have hs' : s - T ≤ δ := tsub_le_iff_left.mpr hs
      have hrepr : T + (s - T) = s := add_tsub_cancel_of_le hTs.le
      have hmem := hdw (s - T) hs'
      simpa [hrepr] using hmem
  have hTδ : T + δ ≤ T := le_csSup hbdd hTδS
  have hδ0 : δ = 0 :=
    le_zero_iff.mp (le_of_add_le_add_left (show T + δ ≤ T + 0 by simpa using hTδ))
  exact absurd hδ0 hδ.ne'

theorem HasFacetRows.boundaryDwell {B : Behavior X} {D N : Set X}
    (h : B.HasFacetRows D N) (hND : N ⊆ D) (hD : B.Invariant D)
    (hcont : ∀ γ ∈ B.fwd, Continuous γ) :
    ∀ γ ∈ B.fwd, γ 0 ∈ N → γ 0 ∈ frontier N →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ≤ δ, γ s ∈ N := by
  obtain ⟨n, ℓ, ε, F, hε, hrow, hlocal⟩ := h
  intro γ hγ hxN hxfr
  obtain ⟨A, U, hU, hA, hwedge⟩ := hlocal (γ 0) hxfr
  have hW : U ∩ ⋂ i ∈ A, F i ∈ 𝓝 (γ 0) :=
    Filter.inter_mem hU
      ((Filter.biInter_mem A.toFinite).mpr fun i hi => (hA i hi).2)
  have hpre : γ ⁻¹' (U ∩ ⋂ i ∈ A, F i) ∈ 𝓝 (0 : ℝ≥0) :=
    ((hcont γ hγ).continuousAt).preimage_mem_nhds hW
  obtain ⟨δ₀, hδ₀, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.mp hpre
  refine ⟨δ₀ / 2, by positivity, fun s hs => ?_⟩
  have hprefix : ∀ s' : ℝ≥0, s' ≤ s → γ s' ∈ U ∩ ⋂ i ∈ A, F i :=
    fun s' hs' =>
      hsub (lt_of_le_of_lt (hs'.trans hs) (NNReal.half_lt_self hδ₀.ne'))
  refine hwedge _ (hprefix s le_rfl).1 (hD γ hγ (hND hxN) s) fun i hi => ?_
  have hxF : γ 0 ∈ F i := mem_of_mem_nhds (hA i hi).2
  have hconf : ∀ s' : ℝ≥0, s' ≤ s → γ s' ∈ F i := fun s' hs' =>
    Set.mem_iInter₂.mp (hprefix s' hs').2 i hi
  have hgrow := hrow i γ hγ hxF s hconf
  have h0 : ℓ i (γ 0) = 0 := (hA i hi).1
  have hεs : (0 : ℝ) ≤ ε i * (s : ℝ) := mul_nonneg (hε i).le s.coe_nonneg
  linarith

theorem qBlockInv_sound_of_facetRows {B : Behavior X} {D N X0 : Set X}
    (hN : IsClosed N)
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hND : N ⊆ D) (hD : B.Invariant D) (hrows : B.HasFacetRows D N)
    (hInit : X0 ⊆ N) : B.InvScopeSat N X0 :=
  ⟨invariant_of_boundaryDwell hN hcont (hrows.boundaryDwell hND hD hcont),
    hInit⟩

end Safety

theorem invariant_univ (B : Behavior X) : B.Invariant Set.univ :=
  fun _ _ _ _ => Set.mem_univ _

theorem qBlockInv_sound {B : Behavior X} {N X0 : Set X}
    (hInv : B.Invariant N) (hInit : X0 ⊆ N) : B.InvScopeSat N X0 :=
  ⟨hInv, hInit⟩

theorem qBasin_sound {B : Behavior X} {S X0 Bad : Set X}
    (hscope : B.InvScopeSat S X0) (hAvoid : S ∩ Bad = ∅) :
    B.SafetySat X0 Bad := by
  intro γ hγ h0 t hB
  have hS : γ t ∈ S := hscope.1 γ hγ (hscope.2 h0) t
  have hmem : γ t ∈ S ∩ Bad := ⟨hS, hB⟩
  rw [hAvoid] at hmem
  exact hmem

theorem qBasin_batch {B : Behavior X} {S X0 : Set X} {J : Type*}
    {Bad : J → Set X} (hscope : B.InvScopeSat S X0)
    (hAvoid : ∀ j, S ∩ Bad j = ∅) :
    B.SafetySat X0 (⋃ j, Bad j) := by
  intro γ hγ h0 t hB
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hB
  exact qBasin_sound hscope (hAvoid j) γ hγ h0 t hj

section Apex

open Semiflow (fiberUnion fiberUnion_subset subset_fiberUnion)

variable {Vtx ι : Type*} [PseudoMetricSpace X] [PartialOrder Vtx]

omit [PartialOrder Vtx] in

theorem crCover_assemble {B : Behavior X} {D : Set X}
    {cells : ι → Set X} {hmap : ι → Option Vtx}
    (hCell : ∀ x ∈ D, B.ChainRecurrentIn D x → ∃ i, x ∈ B.MaxInv (cells i))
    (hTransit : ∀ i, hmap i = none → B.HasTransitCert (cells i)) :
    ∀ x ∈ D, B.ChainRecurrentIn D x →
      ∃ v, x ∈ B.MaxInv (fiberUnion cells hmap v) := by
  intro x hx hcr
  obtain ⟨i, hi⟩ := hCell x hx hcr
  cases hv : hmap i with
  | none =>
      rw [(hTransit i hv).maxInv_empty] at hi
      exact absurd hi (Set.notMem_empty x)
  | some v =>
      exact ⟨v, maxInv_mono (subset_fiberUnion hv) hi⟩

open Semiflow (alphaSet omegaSet) in

theorem qMorseDischarge_sound (B : Behavior X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hCompact : ∀ v, IsCompact (B.MaxInv (fiberUnion cells hmap v)))
    (hDisj : ∀ v w, v ≠ w →
      Disjoint (B.MaxInv (fiberUnion cells hmap v))
        (B.MaxInv (fiberUnion cells hmap w)))
    (hCell : ∀ x ∈ D, B.ChainRecurrentIn D x → ∃ i, x ∈ B.MaxInv (cells i))
    (hTransit : ∀ i, hmap i = none → B.HasTransitCert (cells i))
    (hOrder : ∀ γ ∈ B.cpl, Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ B.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧ alphaSet γ ⊆ B.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ B.MaxInv (fiberUnion cells hmap w)) :
    B.MorseSat D ρ :=
  ⟨{ M := fun v => B.MaxInv (fiberUnion cells hmap v)
     isCompact := hCompact
     invariant := fun _ => B.maxInv_isInvariant _
     located := fun v =>
       (B.maxInv_subset _).trans (fiberUnion_subset hContain v)
     disjoint := hDisj
     crCover := crCover_assemble hCell hTransit
     order := hOrder }⟩

end Apex

section RowFloor

def DerivOn (B : Behavior X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ C →
    HasDerivWithinAt (fun s : ℝ => V (γ s.toNNReal)) (W (γ 0)) (Set.Ici 0) 0

def DiniLeOn (B : Behavior X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ C → ∀ r, W (γ 0) < r →
    ∀ᶠ s in 𝓝[>] (0:ℝ), slope (fun u : ℝ => V (γ u.toNNReal)) 0 s < r

def DiniGeOn (B : Behavior X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ C → ∀ r, r < W (γ 0) →
    ∀ᶠ s in 𝓝[>] (0:ℝ), r < slope (fun u : ℝ => V (γ u.toNNReal)) 0 s

theorem DerivOn.diniLeOn {B : Behavior X} {V W : X → ℝ} {C : Set X}
    (h : B.DerivOn V W C) : B.DiniLeOn V W C :=
  fun γ hγ hx _ hr =>
    (h γ hγ hx).Ioi_of_Ici.limsup_slope_le' (by simp) hr

theorem DerivOn.diniGeOn {B : Behavior X} {V W : X → ℝ} {C : Set X}
    (h : B.DerivOn V W C) : B.DiniGeOn V W C := by
  intro γ hγ hx r hr
  have htend := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl 0)).mp
    (h γ hγ hx).Ioi_of_Ici
  exact htend.eventually (eventually_gt_nhds hr)

theorem DiniGeOn.neg {B : Behavior X} {V W : X → ℝ} {C : Set X}
    (h : B.DiniGeOn V W C) :
    B.DiniLeOn (fun z => -V z) (fun z => -W z) C := by
  intro γ hγ hx r hr
  have hr' : -r < W (γ 0) := by linarith
  filter_upwards [h γ hγ hx (-r) hr'] with s hs
  have hneg : slope (fun u : ℝ => -(V (γ u.toNNReal))) 0 s
      = -slope (fun u : ℝ => V (γ u.toNNReal)) 0 s := by
    simp only [slope_def_field]
    ring
  have h2 : -slope (fun u : ℝ => V (γ u.toNNReal)) 0 s < r := by
    linarith
  simpa [hneg] using h2

theorem DiniLeOn.frequently_slope_lt {B : Behavior X} {V W : X → ℝ}
    {C : Set X} (hW : B.DiniLeOn V W C) {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd)
    {s r : ℝ} (hs : 0 ≤ s) (hyC : γ s.toNNReal ∈ C)
    (hr : W (γ s.toNNReal) < r) :
    ∃ᶠ z in 𝓝[>] s, slope (fun u : ℝ => V (γ u.toNNReal)) s z < r := by
  set δγ : ℝ≥0 → X := fun t => γ (s.toNNReal + t) with hδγ
  have hδmem : δγ ∈ B.fwd := B.shift_fwd γ hγ s.toNNReal
  have hδ0 : δγ 0 = γ s.toNNReal := by simp [hδγ]
  have hbase : ∀ᶠ v in 𝓝[>] (0:ℝ),
      slope (fun u : ℝ => V (δγ u.toNNReal)) 0 v < r :=
    hW δγ hδmem (by rw [hδ0]; exact hyC) r (by rw [hδ0]; exact hr)
  have hmap : Filter.Tendsto (fun v : ℝ => s + v) (𝓝[>] (0:ℝ)) (𝓝[>] s) := by
    have h1' : Filter.Tendsto (fun v : ℝ => s + v) (𝓝[>] (0:ℝ)) (𝓝 s) := by
      have h0 : Filter.Tendsto (fun v : ℝ => s + v) (𝓝 (0:ℝ)) (𝓝 (s + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h2 : ∀ᶠ v in 𝓝[>] (0:ℝ), s + v ∈ Set.Ioi s := by
      filter_upwards [eventually_mem_nhdsWithin] with v hv
      exact lt_add_of_pos_right s hv
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1' h2
  have hfreq0 : ∃ᶠ v in 𝓝[>] (0:ℝ),
      slope (fun u : ℝ => V (γ u.toNNReal)) s (s + v) < r := by
    refine ((hbase.and eventually_mem_nhdsWithin).frequently).mono ?_
    rintro v ⟨hv, hv0⟩
    have hvpos : (0:ℝ) < v := hv0
    have hsplit : (s + v).toNNReal = s.toNNReal + v.toNNReal := by
      rw [← Real.toNNReal_add hs hvpos.le]
    have hkey : V (γ (s + v).toNNReal) = V (δγ v.toNNReal) := by
      rw [hsplit, hδγ]
    have hv' := hv
    rw [slope_def_field, sub_zero] at hv'
    have hg0 : V (δγ (0:ℝ).toNNReal) = V (γ s.toNNReal) := by
      rw [Real.toNNReal_zero, hδ0]
    rw [hg0] at hv'
    rw [slope_def_field, hkey, add_sub_cancel_left]
    exact hv'
  exact (Filter.frequently_map.mpr hfreq0).filter_mono hmap

section Bridge

variable [TopologicalSpace X]

theorem integrated_le_of_diniLe {B : Behavior X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hV : ContinuousOn V C)
    (hW : B.DiniLeOn V W C)
    (hrow : ∀ y ∈ C, W y ≤ c)
    {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) {t : ℝ≥0}
    (hconf : ∀ s ≤ t, γ s ∈ C) :
    V (γ t) ≤ V (γ 0) + c * t := by
  set g : ℝ → ℝ := fun u => V (γ u.toNNReal) with hg
  have htraj' : Continuous fun u : ℝ => γ u.toNNReal :=
    (hcont γ hγ).comp continuous_real_toNNReal
  have hmapsC : ∀ u ∈ Set.Icc (0 : ℝ) (t : ℝ), γ u.toNNReal ∈ C :=
    fun u hu => hconf _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
  have hcont' : ContinuousOn g (Set.Icc 0 (t : ℝ)) :=
    hV.comp htraj'.continuousOn hmapsC
  set Bd : ℝ → ℝ := fun u => g 0 + c * u with hBd
  have hBc : ContinuousOn Bd (Set.Icc 0 (t : ℝ)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hB' : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ),
      HasDerivWithinAt Bd ((fun _ : ℝ => c) u) (Set.Ici u) u := by
    intro u _
    show HasDerivWithinAt Bd c (Set.Ici u) u
    rw [hBd]
    have h1 := ((hasDerivWithinAt_id u (Set.Ici u)).const_mul c).const_add (g 0)
    simpa only [id_eq, mul_one] using h1
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ), ∀ r, (fun _ : ℝ => c) u < r →
      ∃ᶠ z in 𝓝[>] u, slope g u z < r := by
    intro u hu r hr
    have huC := hmapsC u ⟨hu.1, hu.2.le⟩
    exact hW.frequently_slope_lt hγ hu.1 huC
      (lt_of_le_of_lt (hrow _ huC) hr)
  have hfence := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := g) (a := 0) (b := (t : ℝ)) (B := Bd) (B' := fun _ : ℝ => c)
    hcont' (by simp [hBd]) hBc hB' hbound
  have hend := hfence ⟨t.coe_nonneg, le_refl (t : ℝ)⟩
  have hg0 : g 0 = V (γ 0) := by simp [hg]
  have hgt : g (t : ℝ) = V (γ t) := by simp [hg]
  simp only [hBd] at hend
  rw [hg0, hgt] at hend
  exact hend

theorem integrated_ge_of_diniGe {B : Behavior X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hV : ContinuousOn V C)
    (hW : B.DiniGeOn V W C)
    (hrow : ∀ y ∈ C, c ≤ W y)
    {γ : ℝ≥0 → X} (hγ : γ ∈ B.fwd) {t : ℝ≥0}
    (hconf : ∀ s ≤ t, γ s ∈ C) :
    V (γ 0) + c * t ≤ V (γ t) := by
  have h := integrated_le_of_diniLe (V := fun z => -V z)
    (W := fun z => -W z) (c := -c) hcont hV.neg hW.neg
    (fun y hy => neg_le_neg (hrow y hy)) hγ hconf
  simp only [neg_mul] at h
  linarith

theorem hasTransitCert_of_dini_rows {B : Behavior X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hε : 0 < ε) (hV : ContinuousOn V C) (hbdd : BddBelow (V '' C))
    (hW : B.DiniLeOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    B.HasTransitCert C := by
  refine ⟨V, ε, hε, hbdd, fun γ hγ t hconf => ?_⟩
  have h := integrated_le_of_diniLe hcont hV hW hrow hγ hconf
  simpa [neg_mul, sub_eq_add_neg] using h

theorem hasTransitCert_of_dini_rows_isCompact {B : Behavior X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hC : IsCompact C) (hε : 0 < ε) (hV : ContinuousOn V C)
    (hW : B.DiniLeOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    B.HasTransitCert C :=
  hasTransitCert_of_dini_rows hcont hε hV (hC.bddBelow_image hV) hW hrow

theorem hasFacetRows_of_dini_rows {B : Behavior X} {D N : Set X}
    {n : ℕ} {ℓ : Fin n → X → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set X}
    (W : Fin n → X → ℝ)
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hε : ∀ i, 0 < ε i)
    (hℓ : ∀ i, ContinuousOn (ℓ i) (F i))
    (hW : ∀ i, B.DiniGeOn (ℓ i) (W i) (F i))
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ W i y)
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N) :
    B.HasFacetRows D N :=
  ⟨n, ℓ, ε, F, hε,
    fun i _γ hγ _ _t hconf =>
      integrated_ge_of_diniGe hcont (hℓ i) (hW i) (hrow i) hγ hconf,
    hlocal⟩

theorem qBlockInv_sound_of_dini_rows {B : Behavior X} {D N X0 : Set X}
    {n : ℕ} {ℓ : Fin n → X → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set X}
    (W : Fin n → X → ℝ)
    (hN : IsClosed N)
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hND : N ⊆ D) (hD : B.Invariant D)
    (hε : ∀ i, 0 < ε i)
    (hℓ : ∀ i, ContinuousOn (ℓ i) (F i))
    (hW : ∀ i, B.DiniGeOn (ℓ i) (W i) (F i))
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ W i y)
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N)
    (hInit : X0 ⊆ N) : B.InvScopeSat N X0 :=
  qBlockInv_sound_of_facetRows hN hcont hND hD
    (hasFacetRows_of_dini_rows W hcont hε hℓ hW hrow hlocal) hInit

end Bridge

theorem hasCrossingCert_of_dini {B : Behavior X} {O : Set X}
    {V W : X → ℝ} {c : ℝ}
    (hlevel : ∀ x ∈ O, V x = c) (hW : B.DiniLeOn V W O)
    (hneg : ∀ x ∈ O, W x < 0) :
    B.HasCrossingCert O := by
  refine ⟨V, c, hlevel, fun γ hγ hx => ?_⟩
  have hev := hW γ hγ hx 0 (hneg _ hx)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hupos : (0:ℝ) < u := hu
  refine ⟨(u / 2).toNNReal, Real.toNNReal_pos.mpr (by linarith), ?_⟩
  intro s hs hsle
  have hs' : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsu : (s : ℝ) ≤ u / 2 := by
    have h1 : ((s : ℝ≥0) : ℝ) ≤ (((u / 2).toNNReal : ℝ≥0) : ℝ) := by
      exact_mod_cast hsle
    rwa [Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ u / 2)] at h1
  have hmem : (s : ℝ) ∈ Set.Ioo (0:ℝ) u := ⟨hs', by linarith⟩
  have hslope := hsub hmem
  simp only [Set.mem_setOf_eq, slope_def_field, sub_zero, Real.toNNReal_coe,
    Real.toNNReal_zero] at hslope
  rw [hlevel _ hx] at hslope
  have hnum : V (γ s) - c < 0 := by
    by_contra hcon
    exact absurd hslope (not_lt.mpr (div_nonneg (not_lt.mp hcon) hs'.le))
  linarith

end RowFloor

section Switched

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

def SolvesSwitched (B : Behavior E) (f : ι → E → E) (R : ι → Set E)
    (C : Set E) : Prop :=
  ∀ γ ∈ B.fwd, γ 0 ∈ C → ∃ i, γ 0 ∈ R i ∧
    HasDerivWithinAt (fun s : ℝ => γ s.toNNReal) (f i (γ 0)) (Set.Ici 0) 0

theorem diniLeOn_of_switched {B : Behavior E} {f : ι → E → E}
    {R : ι → Set E} {C : Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {W : E → ℝ}
    (hode : B.SolvesSwitched f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, DV y (f i y) ≤ W y) :
    B.DiniLeOn V W C := by
  intro γ hγ hx r hr
  obtain ⟨i, hxR, hd⟩ := hode γ hγ hx
  have hcomp : HasDerivWithinAt (fun s : ℝ => V (γ s.toNNReal))
      (DV (γ 0) (f i (γ 0))) (Set.Ici 0) 0 :=
    (hV (γ 0) hx).comp_hasDerivWithinAt_of_eq (0 : ℝ) hd
      (by simp [Real.toNNReal_zero])
  exact hcomp.Ioi_of_Ici.limsup_slope_le' (by simp)
    (lt_of_le_of_lt (hrow i (γ 0) ⟨hx, hxR⟩) hr)

theorem diniGeOn_of_switched {B : Behavior E} {f : ι → E → E}
    {R : ι → Set E} {C : Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {W : E → ℝ}
    (hode : B.SolvesSwitched f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, W y ≤ DV y (f i y)) :
    B.DiniGeOn V W C := by
  intro γ hγ hx r hr
  obtain ⟨i, hxR, hd⟩ := hode γ hγ hx
  have hcomp : HasDerivWithinAt (fun s : ℝ => V (γ s.toNNReal))
      (DV (γ 0) (f i (γ 0))) (Set.Ici 0) 0 :=
    (hV (γ 0) hx).comp_hasDerivWithinAt_of_eq (0 : ℝ) hd
      (by simp [Real.toNNReal_zero])
  have htend := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl 0)).mp
    hcomp.Ioi_of_Ici
  exact htend.eventually (eventually_gt_nhds
    (lt_of_lt_of_le hr (hrow i (γ 0) ⟨hx, hxR⟩)))

theorem hasTransitCert_of_switched_rows
    {B : Behavior E} {C : Set E}
    {f : ι → E → E} {R : ι → Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {ε : ℝ}
    (hcont : ∀ γ ∈ B.fwd, Continuous γ)
    (hC : IsCompact C) (hε : 0 < ε)
    (hode : B.SolvesSwitched f R C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ i, ∀ y ∈ C ∩ R i, DV y (f i y) ≤ -ε) :
    B.HasTransitCert C :=
  hasTransitCert_of_dini_rows_isCompact hcont hC hε
    (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
    (diniLeOn_of_switched (W := fun _ => -ε) hode hV hrow)
    (fun _ _ => le_refl _)

end Switched

section Profiles

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

def IsClassicalSolOn (f : E → E) (A : Set E) (γ : ℝ≥0 → E) : Prop :=
  Continuous γ ∧ ∀ u : ℝ, 0 ≤ u → γ u.toNNReal ∈ A →
    HasDerivWithinAt (fun w : ℝ => γ w.toNNReal) (f (γ u.toNNReal))
      (Set.Ici u) u

def FilippovWindow (f : ι → E → E) (inc : E → Set ι) (γ : ℝ≥0 → E)
    (a b : ℝ) : Prop :=
  (∃ K : ℝ≥0, LipschitzOnWith K (fun u : ℝ => γ u.toNNReal) (Set.Icc a b)) ∧
  ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioo a b →
    ∃ v ∈ convexHull ℝ ((fun i => f i (γ u.toNNReal)) '' inc (γ u.toNNReal)),
      HasDerivAt (fun w : ℝ => γ w.toNNReal) v u

def filippovFwd (f : ι → E → E) (inc : E → Set ι) (A : Set E) :
    Set (ℝ≥0 → E) :=
  {γ | Continuous γ ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    (∀ u ∈ Set.Icc a b, γ u.toNNReal ∈ A) → FilippovWindow f inc γ a b}

def FilippovWindowCpl (f : ι → E → E) (inc : E → Set ι) (γ : ℝ → E)
    (a b : ℝ) : Prop :=
  (∃ K : ℝ≥0, LipschitzOnWith K γ (Set.Icc a b)) ∧
  ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioo a b →
    ∃ v ∈ convexHull ℝ ((fun i => f i (γ u)) '' inc (γ u)),
      HasDerivAt γ v u

def filippovCpl (f : ι → E → E) (inc : E → Set ι) (A : Set E) :
    Set (ℝ → E) :=
  {γ | Continuous γ ∧ ∀ a b : ℝ, a ≤ b →
    (∀ u ∈ Set.Icc a b, γ u ∈ A) → FilippovWindowCpl f inc γ a b}

private theorem ae_comp_add_const {p : ℝ → Prop} (s : ℝ)
    (h : ∀ᵐ u ∂(volume : Measure ℝ), p u) :
    ∀ᵐ u ∂(volume : Measure ℝ), p (u + s) := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hpre : {u : ℝ | ¬ p (u + s)} = (fun u : ℝ => u + s) ⁻¹' {u | ¬ p u} :=
    rfl
  rw [hpre]
  exact ((measurePreserving_add_right volume s).quasiMeasurePreserving).preimage_null h

theorem FilippovWindow.shift {f : ι → E → E} {inc : E → Set ι}
    {γ : ℝ≥0 → E} (s : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a)
    (h : FilippovWindow f inc γ (a + (s:ℝ)) (b + (s:ℝ))) :
    FilippovWindow f inc (fun t => γ (s + t)) a b := by
  obtain ⟨⟨K, hK⟩, hae⟩ := h
  have hagree : ∀ u : ℝ, 0 ≤ u →
      γ (s + u.toNNReal) = γ (u + (s:ℝ)).toNNReal := by
    intro u hu0
    rw [Real.toNNReal_add hu0 s.coe_nonneg, Real.toNNReal_coe, add_comm]
  constructor
  · refine ⟨K, ?_⟩
    intro x hx y hy
    have hx' : x + (s:ℝ) ∈ Set.Icc (a + (s:ℝ)) (b + (s:ℝ)) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : y + (s:ℝ) ∈ Set.Icc (a + (s:ℝ)) (b + (s:ℝ)) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hbound := hK hx' hy'
    have hgx : (fun u : ℝ => (fun t => γ (s + t)) u.toNNReal) x
        = (fun u : ℝ => γ u.toNNReal) (x + (s:ℝ)) := hagree x (le_trans ha hx.1)
    have hgy : (fun u : ℝ => (fun t => γ (s + t)) u.toNNReal) y
        = (fun u : ℝ => γ u.toNNReal) (y + (s:ℝ)) := hagree y (le_trans ha hy.1)
    rw [hgx, hgy]
    simpa [edist_add_right] using hbound
  · have htr := ae_comp_add_const (s := (s:ℝ))
      (p := fun u => u ∈ Set.Ioo (a + (s:ℝ)) (b + (s:ℝ)) →
        ∃ v ∈ convexHull ℝ
          ((fun i => f i (γ u.toNNReal)) '' inc (γ u.toNNReal)),
          HasDerivAt (fun w : ℝ => γ w.toNNReal) v u) hae
    filter_upwards [htr] with u hu hmem
    have hu0 : (0:ℝ) < u := lt_of_le_of_lt ha hmem.1
    have hmem' : u + (s:ℝ) ∈ Set.Ioo (a + (s:ℝ)) (b + (s:ℝ)) :=
      ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    obtain ⟨v, hv, hderiv⟩ := hu hmem'
    have hocc : γ (u + (s:ℝ)).toNNReal = γ (s + u.toNNReal) :=
      (hagree u hu0.le).symm
    refine ⟨v, by rwa [hocc] at hv, ?_⟩
    have htrans : HasDerivAt (fun w : ℝ => w + (s:ℝ)) 1 u := by
      simpa using (hasDerivAt_id u).add_const (s:ℝ)
    have hcomp := hderiv.scomp (h := fun w : ℝ => w + (s:ℝ)) u htrans
    have hcomp' : HasDerivAt
        (fun w : ℝ => γ (w + (s:ℝ)).toNNReal) v u := by
      simpa [Function.comp_def] using hcomp
    have heq : (fun w : ℝ => (fun t => γ (s + t)) w.toNNReal)
        =ᶠ[𝓝 u] fun w : ℝ => γ (w + (s:ℝ)).toNNReal := by
      filter_upwards [isOpen_Ioi.mem_nhds hu0] with w hw
      exact hagree w (le_of_lt hw)
    exact hcomp'.congr_of_eventuallyEq heq

def filippovBehavior (f : ι → E → E) (inc : E → Set ι) (A : Set E) :
    Behavior E where
  fwd := filippovFwd f inc A
  cpl := filippovCpl f inc A
  shift_fwd := by
    rintro γ ⟨hcont, hwin⟩ s
    refine ⟨hcont.comp (continuous_const.add continuous_id), ?_⟩
    intro a b ha hab hconf
    have hconf' : ∀ u ∈ Set.Icc (a + (s:ℝ)) (b + (s:ℝ)),
        γ u.toNNReal ∈ A := by
      intro u hu
      have h1 : (0:ℝ) ≤ u - (s:ℝ) := by
        have := hu.1
        have ha' : (0:ℝ) ≤ a := ha
        linarith
      have hus : u - (s:ℝ) ∈ Set.Icc a b :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hmem : γ (s + (u - (s:ℝ)).toNNReal) ∈ A := hconf _ hus
      have hrepr : (s:ℝ) + (u - (s:ℝ)) = u := by ring
      have hcalc : s + (u - (s:ℝ)).toNNReal = u.toNNReal := by
        conv_rhs => rw [← hrepr]
        rw [Real.toNNReal_add s.coe_nonneg h1, Real.toNNReal_coe]
      rwa [hcalc] at hmem
    exact FilippovWindow.shift s ha
      (hwin (a + (s:ℝ)) (b + (s:ℝ)) (add_nonneg ha s.coe_nonneg)
        (by linarith) hconf')
  shift_cpl := by
    rintro γ ⟨hcont, hwin⟩ s
    refine ⟨hcont.comp (continuous_id.add continuous_const), ?_⟩
    intro a b hab hconf
    have hconf' : ∀ u ∈ Set.Icc (a + s) (b + s), γ u ∈ A := by
      intro u hu
      have hus : u - s ∈ Set.Icc a b := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hmem : γ (u - s + s) ∈ A := hconf _ hus
      simpa [sub_add_cancel] using hmem
    obtain ⟨⟨K, hK⟩, hae⟩ := hwin (a + s) (b + s) (by linarith) hconf'
    constructor
    · refine ⟨K, ?_⟩
      intro x hx y hy
      have hx' : x + s ∈ Set.Icc (a + s) (b + s) :=
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hy' : y + s ∈ Set.Icc (a + s) (b + s) :=
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hbound := hK hx' hy'
      simpa [edist_add_right] using hbound
    · have htr := ae_comp_add_const (s := s)
        (p := fun u => u ∈ Set.Ioo (a + s) (b + s) →
          ∃ v ∈ convexHull ℝ ((fun i => f i (γ u)) '' inc (γ u)),
            HasDerivAt γ v u) hae
      filter_upwards [htr] with u hu hmem
      obtain ⟨v, hv, hderiv⟩ := hu
        ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      refine ⟨v, hv, ?_⟩
      have htrans : HasDerivAt (fun w : ℝ => w + s) 1 u := by
        simpa using (hasDerivAt_id u).add_const s
      have hcomp := hderiv.scomp (h := fun w : ℝ => w + s) u htrans
      simpa [Function.comp_def] using hcomp
  restrict_cpl := by
    rintro γ ⟨hcont, hwin⟩
    refine ⟨hcont.comp NNReal.continuous_coe, ?_⟩
    intro a b ha hab hconf
    have hconf' : ∀ u ∈ Set.Icc a b, γ u ∈ A := by
      intro u hu
      have hu0 : (0:ℝ) ≤ u := le_trans ha hu.1
      have hmem : γ ((u.toNNReal : ℝ)) ∈ A := hconf u hu
      rwa [Real.coe_toNNReal _ hu0] at hmem
    obtain ⟨⟨K, hK⟩, hae⟩ := hwin a b hab hconf'
    constructor
    · refine ⟨K, ?_⟩
      intro x hx y hy
      have hbound := hK hx hy
      show edist (γ ((x.toNNReal : ℝ))) (γ ((y.toNNReal : ℝ))) ≤ K * edist x y
      rw [Real.coe_toNNReal _ (le_trans ha hx.1),
        Real.coe_toNNReal _ (le_trans ha hy.1)]
      exact hbound
    · filter_upwards [hae] with u hu hmem
      have hu0 : (0:ℝ) < u := lt_of_le_of_lt ha hmem.1
      obtain ⟨v, hv, hderiv⟩ := hu hmem
      have hocc : γ ((u.toNNReal : ℝ)) = γ u := by
        rw [Real.coe_toNNReal _ hu0.le]
      refine ⟨v, ?_, ?_⟩
      · show v ∈ convexHull ℝ
          ((fun i => f i (γ ((u.toNNReal : ℝ)))) '' inc (γ ((u.toNNReal : ℝ))))
        rw [hocc]
        exact hv
      · have heq : (fun w : ℝ => (fun t : ℝ≥0 => γ (t:ℝ)) w.toNNReal)
            =ᶠ[𝓝 u] γ := by
          filter_upwards [isOpen_Ioi.mem_nhds hu0] with w hw
          show γ ((w.toNNReal : ℝ)) = γ w
          rw [Real.coe_toNNReal _ (le_of_lt hw)]
        exact hderiv.congr_of_eventuallyEq heq

theorem hasTransitCert_of_filippov {f : ι → E → E} {inc : E → Set ι}
    {A C : Set E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {KV : ℝ≥0} {ε : ℝ}
    (hCA : C ⊆ A) (hε : 0 < ε) (hbdd : BddBelow (V '' C))
    (hVLip : LipschitzOnWith KV V C)
    (hV : ∀ y ∈ C, HasFDerivAt V (DV y) y)
    (hrow : ∀ y ∈ C, ∀ i ∈ inc y, DV y (f i y) ≤ -ε) :
    (filippovBehavior f inc A).HasTransitCert C := by
  refine ⟨V, ε, hε, hbdd, ?_⟩
  rintro γ ⟨hcont, hwin⟩ t hconf
  have hmapsC : ∀ u ∈ Set.Icc (0:ℝ) (t:ℝ), γ u.toNNReal ∈ C := fun u hu =>
    hconf _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
  obtain ⟨⟨K, hLip⟩, hae⟩ := hwin 0 t le_rfl t.coe_nonneg
    (fun u hu => hCA (hmapsC u hu))
  have hACcomp : AbsolutelyContinuousOnInterval
      (fun u : ℝ => V (γ u.toNNReal)) 0 t := by
    have hcompL : LipschitzOnWith (KV * K)
        (fun u : ℝ => V (γ u.toNNReal)) (Set.uIcc (0:ℝ) (t:ℝ)) := by
      rw [Set.uIcc_of_le t.coe_nonneg]
      exact hVLip.comp hLip hmapsC
    exact hcompL.absolutelyContinuousOnInterval
  have h0mem : ({(0:ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton _)
  have htmem : ({(t:ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton _)
  have hae' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Icc (0:ℝ) (t:ℝ) →
      DifferentiableAt ℝ (fun u : ℝ => V (γ u.toNNReal)) u →
      deriv (fun u : ℝ => V (γ u.toNNReal)) u ≤ -ε := by
    filter_upwards [hae, h0mem, htmem] with u himp hu0 hut hu _
    have hu0' : u ≠ 0 := hu0
    have hut' : u ≠ (t:ℝ) := hut
    have humem : u ∈ Set.Ioo (0:ℝ) (t:ℝ) :=
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0'), lt_of_le_of_ne hu.2 hut'⟩
    obtain ⟨v, hvhull, hvderiv⟩ := himp humem
    have hyC : γ u.toNNReal ∈ C := hmapsC u hu
    have hchain : HasDerivAt (fun w : ℝ => V (γ w.toNNReal))
        (DV (γ u.toNNReal) v) u := (hV _ hyC).comp_hasDerivAt u hvderiv
    rw [hchain.deriv]
    refine Semiflow.le_on_convexHull ?_ v hvhull
    rintro w ⟨i, hi, rfl⟩
    exact hrow _ hyC i hi
  have h := Semiflow.le_add_of_absolutelyContinuous_of_ae_deriv_le
    t.coe_nonneg hACcomp hae'
  simpa [Real.toNNReal_coe, Real.toNNReal_zero, neg_mul, sub_eq_add_neg]
    using h

def Nonvacuous (B : Behavior X) (X0 : Set X) : Prop :=
  ∀ x ∈ X0, ∃ γ ∈ B.fwd, γ 0 = x

/-- Basin soundness in the properness-carrying (option-A) form: the
conclusion asserts the safety verdict *and* per-init-point trajectory
existence. The existence conjunct cannot be derived from the safety
premises — they are universals over trajectories, vacuously satisfied
by a behaviour with no trajectory from `X0` — so it enters as the
`Nonvacuous` input. Within the semiflow model class that input is
discharged once per system (`Semiflow.behavior_nonvacuous`). -/
theorem qBasin_sound_optionA {B : Behavior X} {S X0 Bad : Set X}
    (hscope : B.InvScopeSat S X0) (hAvoid : S ∩ Bad = ∅)
    (hprop : B.Nonvacuous X0) :
    B.SafetySat X0 Bad ∧ B.Nonvacuous X0 :=
  ⟨qBasin_sound hscope hAvoid, hprop⟩

/-- Batch form of `qBasin_sound_optionA`: one properness discharge
serves every avoid set — the existence conjunct is a property of the
system and its init set, not of the individual specification. -/
theorem qBasin_batch_optionA {B : Behavior X} {S X0 : Set X} {J : Type*}
    {Bad : J → Set X} (hscope : B.InvScopeSat S X0)
    (hAvoid : ∀ j, S ∩ Bad j = ∅) (hprop : B.Nonvacuous X0) :
    B.SafetySat X0 (⋃ j, Bad j) ∧ B.Nonvacuous X0 :=
  ⟨qBasin_batch hscope hAvoid, hprop⟩

end Profiles

section Witness

noncomputable def sqrtField : ℝ → ℝ := fun x => Real.sqrt |x|

def gammaZero : ℝ≥0 → ℝ := fun _ => 0

noncomputable def gammaQuad : ℝ≥0 → ℝ := fun t => (t : ℝ) ^ 2 / 4

theorem gammaZero_classical :
    IsClassicalSolOn sqrtField Set.univ gammaZero := by
  refine ⟨continuous_const, fun u hu _ => ?_⟩
  simp only [gammaZero, sqrtField, abs_zero, Real.sqrt_zero]
  exact hasDerivWithinAt_const u (Set.Ici u) 0

theorem gammaQuad_classical :
    IsClassicalSolOn sqrtField Set.univ gammaQuad := by
  constructor
  · exact (NNReal.continuous_coe.pow 2).div_const 4
  · intro u hu _
    have hval : gammaQuad u.toNNReal = u ^ 2 / 4 := by
      simp [gammaQuad, Real.coe_toNNReal _ hu]
    have hf : sqrtField (gammaQuad u.toNNReal) = u / 2 := by
      rw [hval]
      have h4 : u ^ 2 / 4 = (u / 2) ^ 2 := by ring
      have hnn : (0:ℝ) ≤ u ^ 2 / 4 := by positivity
      rw [sqrtField]
      show Real.sqrt |u ^ 2 / 4| = u / 2
      rw [abs_of_nonneg hnn, h4, Real.sqrt_sq (by linarith : (0:ℝ) ≤ u / 2)]
    rw [hf]
    have hpoly : HasDerivWithinAt (fun w : ℝ => w ^ 2 / 4) (u / 2)
        (Set.Ici u) u := by
      have h := (hasDerivAt_pow 2 u).div_const 4
      have h2 : (↑(2:ℕ) * u ^ (2 - 1) / 4 : ℝ) = u / 2 := by
        norm_num
        ring
      rw [h2] at h
      exact h.hasDerivWithinAt
    refine hpoly.congr ?_ ?_
    · intro w hw
      have hw0 : (0:ℝ) ≤ w := le_trans hu hw
      simp [gammaQuad, Real.coe_toNNReal _ hw0]
    · simp [gammaQuad, Real.coe_toNNReal _ hu]

theorem no_semiflow_realizes_sqrtField :
    ¬ ∃ φ : Semiflow ℝ, ∀ γ : ℝ≥0 → ℝ,
      IsClassicalSolOn sqrtField Set.univ γ →
        γ = fun t => φ.flow t (γ 0) := by
  rintro ⟨φ, h⟩
  have h1 := h gammaZero gammaZero_classical
  have h2 := h gammaQuad gammaQuad_classical
  have e1 := congrFun h1 2
  have e2 := congrFun h2 2
  have hz : gammaZero 0 = (0:ℝ) := rfl
  have hq : gammaQuad 0 = (0:ℝ) := by simp [gammaQuad]
  rw [hz] at e1
  rw [hq] at e2
  have hz2 : gammaZero 2 = (0:ℝ) := rfl
  have hq2 : gammaQuad 2 = (1:ℝ) := by norm_num [gammaQuad]
  rw [hz2] at e1
  rw [hq2] at e2
  have : (0:ℝ) = 1 := e1.trans e2.symm
  norm_num at this

end Witness

end Behavior

namespace Semiflow

def behavior (φ : Semiflow X) : Behavior X where
  fwd := {γ | ∃ x, γ = fun t => φ.flow t x}
  cpl := {γ | φ.CompleteOrbit γ}
  shift_fwd := by
    rintro γ ⟨x, rfl⟩ s
    exact ⟨φ.flow s x, funext fun t => φ.flow_add s t x⟩
  shift_cpl := fun γ hγ s => hγ.shift s
  restrict_cpl := by
    rintro γ hγ
    refine ⟨γ 0, funext fun t => ?_⟩
    have h := hγ 0 t
    simpa using h

/-- The semiflow model class discharges the properness/existence
stratum outright: from every point, the flow trajectory itself is a
member of the behaviour. One theorem per model class — no
per-judgment existence rows are needed where a well-posed flow is
part of the model's presentation. -/
theorem behavior_nonvacuous (φ : Semiflow X) (X0 : Set X) :
    (φ.behavior).Nonvacuous X0 :=
  fun x _ => ⟨fun t => φ.flow t x, ⟨x, rfl⟩, φ.flow_zero x⟩

/-- Basin soundness in option-A form over a semiflow: within the flow
model class the properness conjunct is free, so the rule needs no
input beyond its classical premises. -/
theorem behavior_qBasin_optionA (φ : Semiflow X) {S X0 Bad : Set X}
    (hscope : (φ.behavior).InvScopeSat S X0) (hAvoid : S ∩ Bad = ∅) :
    (φ.behavior).SafetySat X0 Bad ∧ (φ.behavior).Nonvacuous X0 :=
  Behavior.qBasin_sound_optionA hscope hAvoid (φ.behavior_nonvacuous X0)

theorem behavior_safetySat_iff {φ : Semiflow X} {X0 Bad : Set X} :
    (φ.behavior).SafetySat X0 Bad ↔ φ.SafetySat X0 Bad := by
  constructor
  · intro h x hx t
    exact h (fun t => φ.flow t x) ⟨x, rfl⟩
      (by simpa [φ.flow_zero] using hx) t
  · rintro h γ ⟨x, rfl⟩ h0 t
    exact h x (by simpa [φ.flow_zero] using h0) t

theorem behavior_invariant_iff {φ : Semiflow X} {S : Set X} :
    (φ.behavior).Invariant S ↔ φ.Invariant S := by
  constructor
  · intro h x hx t
    exact h (fun t => φ.flow t x) ⟨x, rfl⟩
      (by simpa [φ.flow_zero] using hx) t
  · rintro h γ ⟨x, rfl⟩ h0 t
    exact h x (by simpa [φ.flow_zero] using h0) t

theorem behavior_maxInv (φ : Semiflow X) (C : Set X) :
    (φ.behavior).MaxInv C = φ.MaxInv C := by
  ext x
  constructor
  · rintro ⟨γ, hγ, h0, hr⟩
    exact ⟨γ, hγ, h0, hr⟩
  · rintro ⟨γ, hγ, h0, hr⟩
    exact ⟨γ, hγ, h0, hr⟩

theorem behavior_hasTransitCert_iff {φ : Semiflow X} {C : Set X} :
    (φ.behavior).HasTransitCert C ↔ φ.HasTransitCert C := by
  constructor
  · rintro ⟨V, ε, hε, hbdd, hdec⟩
    refine ⟨V, ε, hε, hbdd, fun x hx t hconf => ?_⟩
    simpa [φ.flow_zero] using
      hdec (fun t => φ.flow t x) ⟨x, rfl⟩ t hconf
  · rintro ⟨V, ε, hε, hbdd, hdec⟩
    refine ⟨V, ε, hε, hbdd, ?_⟩
    rintro γ ⟨x, rfl⟩ t hconf
    have hx : x ∈ C := by
      simpa [φ.flow_zero] using hconf 0 (by simp)
    simpa [φ.flow_zero] using hdec x hx t hconf

theorem behavior_derivOn_iff {φ : Semiflow X} {V W : X → ℝ} {C : Set X} :
    (φ.behavior).DerivOn V W C ↔ φ.FlowDerivOn V W C := by
  constructor
  · intro h x hx
    have := h (fun t => φ.flow t x) ⟨x, rfl⟩
      (by simpa [φ.flow_zero] using hx)
    simpa [φ.flow_zero] using this
  · rintro h γ ⟨x, rfl⟩ h0
    have hx : x ∈ C := by simpa [φ.flow_zero] using h0
    have := h x hx
    simpa [φ.flow_zero] using this

theorem behavior_diniLeOn_iff {φ : Semiflow X} {V W : X → ℝ} {C : Set X} :
    (φ.behavior).DiniLeOn V W C ↔ φ.FlowDiniLeOn V W C := by
  constructor
  · intro h x hx r hr
    have := h (fun t => φ.flow t x) ⟨x, rfl⟩
      (by simpa [φ.flow_zero] using hx) r (by simpa [φ.flow_zero] using hr)
    exact this
  · rintro h γ ⟨x, rfl⟩ h0 r hr
    have hx : x ∈ C := by simpa [φ.flow_zero] using h0
    have hr' : W x < r := by simpa [φ.flow_zero] using hr
    exact h x hx r hr'

section Chains

variable [PseudoMetricSpace X]

theorem behavior_epsChainIn_iff {φ : Semiflow X} {D : Set X} {ε : ℝ}
    {T : ℝ≥0} {x y : X} :
    Behavior.EpsChainIn (φ.behavior) D ε T x y ↔ EpsChainIn φ D ε T x y := by
  constructor
  · intro h
    induction h with
    | step hγ hγ0 hx hy ht hjump =>
        rename_i x' y' γ t
        obtain ⟨x₀, rfl⟩ := hγ
        have hx0 : x₀ = x' := by
          have := hγ0
          simpa [φ.flow_zero] using this
        subst hx0
        exact EpsChainIn.step hx hy ht hjump
    | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2
  · intro h
    induction h with
    | step hx hy ht hjump =>
        exact .step ⟨_, rfl⟩ (φ.flow_zero _) hx hy ht hjump
    | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2

theorem behavior_chainRecurrentIn_iff {φ : Semiflow X} {D : Set X} {x : X} :
    Behavior.ChainRecurrentIn (φ.behavior) D x ↔ ChainRecurrentIn φ D x :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    behavior_epsChainIn_iff

theorem morseSat_of_behavior {Vtx : Type*} [PartialOrder Vtx]
    {φ : Semiflow X} {D : Set X} {ρ : Vtx → Set X}
    (h : (φ.behavior).MorseSat D ρ) : MorseSat φ D ρ := by
  obtain ⟨W⟩ := h
  refine ⟨{ M := W.M
            isCompact := W.isCompact
            invariant := fun v => ?_
            located := W.located
            disjoint := W.disjoint
            crCover := fun x hx hcr =>
              W.crCover x hx (behavior_chainRecurrentIn_iff.mpr hcr)
            order := fun γ horb hr hnot => W.order γ horb hr hnot }⟩
  have hweak : W.M v ⊆ φ.MaxInv (W.M v) := by
    have hw := W.invariant v
    rwa [Behavior.IsInvariantIn, behavior_maxInv] at hw
  exact ⟨fun x hx t => maxInv_forward_confined (hweak hx) t, hweak⟩

end Chains

section Demotion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SolvesODEOn.shift {φ : Semiflow E} {f : E → E} {C : Set E}
    (h : φ.SolvesODEOn f C) {x : E} {s : ℝ} (hs : 0 ≤ s)
    (hyC : φ.flow s.toNNReal x ∈ C) :
    HasDerivWithinAt (fun u : ℝ => φ.flow u.toNNReal x)
      (f (φ.flow s.toNNReal x)) (Set.Ici s) s := by
  set y := φ.flow s.toNNReal x with hy
  have hbase' : HasDerivWithinAt (fun v : ℝ => φ.flow v.toNNReal y) (f y)
      (Set.Ici 0) ((fun u : ℝ => u - s) s) := by
    simpa using h y hyC
  have htrans : HasDerivWithinAt (fun u : ℝ => u - s) 1 (Set.Ici s) s := by
    simpa using (hasDerivWithinAt_id s (Set.Ici s)).sub_const s
  have hmaps : Set.MapsTo (fun u : ℝ => u - s) (Set.Ici s) (Set.Ici 0) := by
    intro u hu
    simpa using sub_nonneg.mpr (Set.mem_Ici.mp hu)
  have hcomp := HasDerivWithinAt.scomp (h := fun u : ℝ => u - s)
    (g₁ := fun v : ℝ => φ.flow v.toNNReal y) s hbase' htrans hmaps
  have heq : ∀ u ∈ Set.Ici s, (fun u : ℝ => φ.flow u.toNNReal x) u =
      ((fun v : ℝ => φ.flow v.toNNReal y) ∘ fun u : ℝ => u - s) u := by
    intro u hu
    have hnn : (0 : ℝ) ≤ u - s := sub_nonneg.mpr hu
    have hsplit : s.toNNReal + (u - s).toNNReal = u.toNNReal := by
      rw [← Real.toNNReal_add hs hnn]
      congr 1
      ring
    show φ.flow u.toNNReal x = φ.flow (u - s).toNNReal y
    rw [hy, ← φ.flow_add, hsplit]
  have hfinal := hcomp.congr heq (heq s Set.self_mem_Ici)
  simpa using hfinal

theorem solvesODEOn_iff_orbit_classical {φ : Semiflow E} {f : E → E}
    {C : Set E}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x) :
    φ.SolvesODEOn f C ↔
      ∀ x, Behavior.IsClassicalSolOn f C (fun t => φ.flow t x) := by
  constructor
  · exact fun h x => ⟨htraj x, fun u hu hmem => h.shift hu hmem⟩
  · intro h x hx
    have hx' : (fun t : ℝ≥0 => φ.flow t x) ((0:ℝ).toNNReal) ∈ C := by
      simpa [Real.toNNReal_zero, φ.flow_zero] using hx
    have := (h x).2 0 le_rfl hx'
    simpa [Real.toNNReal_zero, φ.flow_zero] using this

end Demotion

end Semiflow

end Qtsl

#print axioms Qtsl.Behavior.maxInv_subset
#print axioms Qtsl.Behavior.maxInv_isInvariant
#print axioms Qtsl.Behavior.HasTransitCert.not_forward_confined
#print axioms Qtsl.Behavior.HasTransitCert.maxInv_empty
#print axioms Qtsl.Behavior.HasCrossingCert.maxInv_empty
#print axioms Qtsl.Behavior.not_forward_confined_of_crossingCerts
#print axioms Qtsl.Behavior.invariant_of_boundaryDwell
#print axioms Qtsl.Behavior.HasFacetRows.boundaryDwell
#print axioms Qtsl.Behavior.qBlockInv_sound_of_facetRows
#print axioms Qtsl.Behavior.qBasin_sound
#print axioms Qtsl.Behavior.qBasin_batch
#print axioms Qtsl.Behavior.crCover_assemble
#print axioms Qtsl.Behavior.qMorseDischarge_sound
#print axioms Qtsl.Behavior.DiniLeOn.frequently_slope_lt
#print axioms Qtsl.Behavior.integrated_le_of_diniLe
#print axioms Qtsl.Behavior.integrated_ge_of_diniGe
#print axioms Qtsl.Behavior.hasTransitCert_of_dini_rows
#print axioms Qtsl.Behavior.hasFacetRows_of_dini_rows
#print axioms Qtsl.Behavior.qBlockInv_sound_of_dini_rows
#print axioms Qtsl.Behavior.hasCrossingCert_of_dini
#print axioms Qtsl.Behavior.diniLeOn_of_switched
#print axioms Qtsl.Behavior.hasTransitCert_of_switched_rows
#print axioms Qtsl.Behavior.FilippovWindow.shift
#print axioms Qtsl.Behavior.filippovBehavior
#print axioms Qtsl.Behavior.hasTransitCert_of_filippov
#print axioms Qtsl.Behavior.gammaZero_classical
#print axioms Qtsl.Behavior.gammaQuad_classical
#print axioms Qtsl.Behavior.no_semiflow_realizes_sqrtField
#print axioms Qtsl.Behavior.qBasin_sound_optionA
#print axioms Qtsl.Behavior.qBasin_batch_optionA
#print axioms Qtsl.Semiflow.behavior
#print axioms Qtsl.Semiflow.behavior_nonvacuous
#print axioms Qtsl.Semiflow.behavior_qBasin_optionA
#print axioms Qtsl.Semiflow.behavior_safetySat_iff
#print axioms Qtsl.Semiflow.behavior_invariant_iff
#print axioms Qtsl.Semiflow.behavior_maxInv
#print axioms Qtsl.Semiflow.behavior_hasTransitCert_iff
#print axioms Qtsl.Semiflow.behavior_derivOn_iff
#print axioms Qtsl.Semiflow.behavior_diniLeOn_iff
#print axioms Qtsl.Semiflow.behavior_epsChainIn_iff
#print axioms Qtsl.Semiflow.morseSat_of_behavior
#print axioms Qtsl.Semiflow.SolvesODEOn.shift
#print axioms Qtsl.Semiflow.solvesODEOn_iff_orbit_classical

end PPLC
