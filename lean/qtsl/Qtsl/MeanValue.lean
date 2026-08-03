import Qtsl.Crossing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The interval mean-value bridge

One pointwise-to-integrated lemma family covering both remaining
integrated row shapes: a derivative bound along a confined trajectory
prefix integrates to an interval bound
(`integrated_le_of_flowDeriv_le`, `integrated_ge_of_flowDeriv_ge`),
instantiated at `±V` for the transit-decrease and facet-growth
certificates respectively.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology

variable {X : Type*}

def FlowDerivOn (φ : Semiflow X) (V W : X → ℝ) (C : Set X) : Prop :=
  ∀ x ∈ C, HasDerivWithinAt (fun s : ℝ => V (φ.flow s.toNNReal x)) (W x) (Set.Ici 0) 0

theorem FlowDerivOn.neg {φ : Semiflow X} {V W : X → ℝ} {C : Set X}
    (h : φ.FlowDerivOn V W C) :
    φ.FlowDerivOn (fun z => -V z) (fun z => -W z) C :=
  fun x hx => (h x hx).neg

theorem FlowDerivOn.shift {φ : Semiflow X} {V W : X → ℝ} {C : Set X}
    (hW : φ.FlowDerivOn V W C) {x : X} {s : ℝ} (hs : 0 ≤ s)
    (hyC : φ.flow s.toNNReal x ∈ C) :
    HasDerivWithinAt (fun u : ℝ => V (φ.flow u.toNNReal x))
      (W (φ.flow s.toNNReal x)) (Set.Ici s) s := by
  set y := φ.flow s.toNNReal x with hy
  have hbase' : HasDerivWithinAt (fun v : ℝ => V (φ.flow v.toNNReal y)) (W y)
      (Set.Ici 0) ((fun u : ℝ => u - s) s) := by
    simpa using hW y hyC
  have htrans : HasDerivWithinAt (fun u : ℝ => u - s) 1 (Set.Ici s) s := by
    simpa using (hasDerivWithinAt_id s (Set.Ici s)).sub_const s
  have hmaps : Set.MapsTo (fun u : ℝ => u - s) (Set.Ici s) (Set.Ici 0) := by
    intro u hu
    simpa using sub_nonneg.mpr (Set.mem_Ici.mp hu)
  have hcomp := HasDerivWithinAt.comp (h := fun u : ℝ => u - s)
    (h₂ := fun v : ℝ => V (φ.flow v.toNNReal y)) s hbase' htrans hmaps
  have heq : ∀ u ∈ Set.Ici s, (fun u : ℝ => V (φ.flow u.toNNReal x)) u =
      ((fun v : ℝ => V (φ.flow v.toNNReal y)) ∘ fun u : ℝ => u - s) u := by
    intro u hu
    have hnn : (0 : ℝ) ≤ u - s := sub_nonneg.mpr hu
    have hsplit : s.toNNReal + (u - s).toNNReal = u.toNNReal := by
      rw [← Real.toNNReal_add hs hnn]
      congr 1
      ring
    show V (φ.flow u.toNNReal x) = V (φ.flow (u - s).toNNReal y)
    rw [hy, ← φ.flow_add, hsplit]
  simpa using hcomp.congr heq (heq s Set.self_mem_Ici)

section Bridge

variable [TopologicalSpace X]

theorem integrated_le_of_flowDeriv_le {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hV : ContinuousOn V C)
    (hW : φ.FlowDerivOn V W C)
    (hrow : ∀ y ∈ C, W y ≤ c)
    {x : X} {t : ℝ≥0} (hconf : ∀ s ≤ t, φ.flow s x ∈ C) :
    V (φ.flow t x) ≤ V x + c * t := by
  set g : ℝ → ℝ := fun u => V (φ.flow u.toNNReal x) with hg
  have htraj' : Continuous fun u : ℝ => φ.flow u.toNNReal x :=
    (htraj x).comp continuous_real_toNNReal
  have hmapsC : ∀ u ∈ Set.Icc (0 : ℝ) (t : ℝ), φ.flow u.toNNReal x ∈ C :=
    fun u hu => hconf _ (Real.toNNReal_le_iff_le_coe.mpr hu.2)
  have hcont : ContinuousOn g (Set.Icc 0 (t : ℝ)) :=
    hV.comp htraj'.continuousOn hmapsC
  have hderiv : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ),
      HasDerivWithinAt g (W (φ.flow u.toNNReal x)) (Set.Ici u) u :=
    fun u hu => hW.shift hu.1 (hmapsC u ⟨hu.1, hu.2.le⟩)
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ), W (φ.flow u.toNNReal x) ≤ c :=
    fun u hu => hrow _ (hmapsC u ⟨hu.1, hu.2.le⟩)
  set B : ℝ → ℝ := fun u => g 0 + c * u with hB
  have hBc : ContinuousOn B (Set.Icc 0 (t : ℝ)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hB' : ∀ u ∈ Set.Ico (0 : ℝ) (t : ℝ),
      HasDerivWithinAt B ((fun _ : ℝ => c) u) (Set.Ici u) u := by
    intro u _
    show HasDerivWithinAt B c (Set.Ici u) u
    rw [hB]
    have h1 := ((hasDerivWithinAt_id u (Set.Ici u)).const_mul c).const_add (g 0)
    simpa only [id_eq, mul_one] using h1
  have hfence := image_le_of_deriv_right_le_deriv_boundary
    (f := g) (f' := fun u : ℝ => W (φ.flow u.toNNReal x))
    (a := 0) (b := (t : ℝ)) (B := B) (B' := fun _ : ℝ => c)
    hcont hderiv (by simp [hB]) hBc hB' hbound
  have hend := hfence ⟨t.coe_nonneg, le_refl (t : ℝ)⟩
  have hg0 : g 0 = V x := by simp [hg, φ.flow_zero]
  have hgt : g (t : ℝ) = V (φ.flow t x) := by simp [hg]
  simp only [hB] at hend
  rw [hg0, hgt] at hend
  exact hend

theorem integrated_ge_of_flowDeriv_ge {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {c : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hV : ContinuousOn V C)
    (hW : φ.FlowDerivOn V W C)
    (hrow : ∀ y ∈ C, c ≤ W y)
    {x : X} {t : ℝ≥0} (hconf : ∀ s ≤ t, φ.flow s x ∈ C) :
    V x + c * t ≤ V (φ.flow t x) := by
  have h := integrated_le_of_flowDeriv_le (V := fun z => -V z)
    (W := fun z => -W z) (c := -c) htraj hV.neg hW.neg
    (fun y hy => neg_le_neg (hrow y hy)) hconf
  simp only [neg_mul] at h
  linarith

end Bridge

section TransitShadow

variable [TopologicalSpace X]

theorem hasTransitCert_of_rows {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : 0 < ε) (hV : ContinuousOn V C) (hbdd : BddBelow (V '' C))
    (hW : φ.FlowDerivOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    φ.HasTransitCert C := by
  refine ⟨V, ε, hε, hbdd, fun x hx t hconf => ?_⟩
  have h := integrated_le_of_flowDeriv_le htraj hV hW hrow hconf
  simpa [neg_mul, sub_eq_add_neg] using h

theorem hasTransitCert_of_rows_isCompact {φ : Semiflow X} {C : Set X}
    {V W : X → ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hC : IsCompact C) (hε : 0 < ε) (hV : ContinuousOn V C)
    (hW : φ.FlowDerivOn V W C) (hrow : ∀ y ∈ C, W y ≤ -ε) :
    φ.HasTransitCert C :=
  hasTransitCert_of_rows htraj hε hV (hC.bddBelow_image hV) hW hrow

end TransitShadow

section FacetShadow

variable [TopologicalSpace X]

theorem hasFacetRows_of_rows {φ : Semiflow X} {D N : Set X}
    {n : ℕ} {ℓ : Fin n → X → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set X}
    (W : Fin n → X → ℝ)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : ∀ i, 0 < ε i)
    (hℓ : ∀ i, ContinuousOn (ℓ i) (F i))
    (hW : ∀ i, φ.FlowDerivOn (ℓ i) (W i) (F i))
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ W i y)
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N) :
    φ.HasFacetRows D N :=
  ⟨n, ℓ, ε, F, hε,
    fun i _ _ _ hconf =>
      integrated_ge_of_flowDeriv_ge htraj (hℓ i) (hW i) (hrow i) hconf,
    hlocal⟩

theorem qBlockInv_sound_of_rows {φ : Semiflow X} {D N X0 : Set X}
    {n : ℕ} {ℓ : Fin n → X → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set X}
    (W : Fin n → X → ℝ)
    (hN : IsClosed N)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hND : N ⊆ D) (hD : φ.Invariant D)
    (hε : ∀ i, 0 < ε i)
    (hℓ : ∀ i, ContinuousOn (ℓ i) (F i))
    (hW : ∀ i, φ.FlowDerivOn (ℓ i) (W i) (F i))
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ W i y)
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set X), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N)
    (hInit : X0 ⊆ N) : φ.InvScopeSat N X0 :=
  qBlockInv_sound_of_facetRows hN htraj hND hD
    (hasFacetRows_of_rows W htraj hε hℓ hW hrow hlocal) hInit

end FacetShadow

theorem hasCrossingCert_of_flowDeriv {φ : Semiflow X} {O : Set X}
    {V W : X → ℝ} {c : ℝ}
    (hlevel : ∀ x ∈ O, V x = c) (hW : φ.FlowDerivOn V W O)
    (hneg : ∀ x ∈ O, W x < 0) :
    φ.HasCrossingCert O :=
  hasCrossingCert_of_deriv V c hlevel fun x hx => ⟨W x, hneg x hx, hW x hx⟩

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.FlowDerivOn.neg
#print axioms Qtsl.Semiflow.FlowDerivOn.shift
#print axioms Qtsl.Semiflow.integrated_le_of_flowDeriv_le
#print axioms Qtsl.Semiflow.integrated_ge_of_flowDeriv_ge
#print axioms Qtsl.Semiflow.hasTransitCert_of_rows
#print axioms Qtsl.Semiflow.hasTransitCert_of_rows_isCompact
#print axioms Qtsl.Semiflow.hasFacetRows_of_rows
#print axioms Qtsl.Semiflow.qBlockInv_sound_of_rows
#print axioms Qtsl.Semiflow.hasCrossingCert_of_flowDeriv

end PPLC
