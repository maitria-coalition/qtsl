import Qtsl.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The ODE profile

Where the differential equation meets the semiflow: `SolvesODEOn` ties
trajectories to a vector field, the flow-derivative interface is
discharged from the chain rule for the smooth-profile case, and the
row-floor assembly connects per-cell row data to the integrated
certificates of the mean-value bridge.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology

section RowFloor

variable {X : Type*} {Vtx ι : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [Finite ι]

theorem qMorseDischarge_sound_of_rows (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hflow : ∀ t, Continuous (φ.flow t))
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hCross : ∀ v w, v ≠ w → ∀ i j, hmap i = some v → hmap j = some w →
      ∃ (ℓ : X → ℝ) (c : ℝ) (W : X → ℝ),
        (∀ y ∈ cells i ∩ cells j, ℓ y = c) ∧
        φ.FlowDerivOn ℓ W (cells i ∩ cells j) ∧
        ∀ y ∈ cells i ∩ cells j, W y < 0)
    (hTransit : ∀ i, hmap i = none →
      ∃ (V W : X → ℝ) (ε : ℝ), 0 < ε ∧ ContinuousOn V (cells i) ∧
        φ.FlowDerivOn V W (cells i) ∧ ∀ y ∈ cells i, W y ≤ -ε)
    (hCell : ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i))
    (hOrder : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      (∀ v, ¬ Set.range γ ⊆ φ.MaxInv (fiberUnion cells hmap v)) →
      ∃ v w, w < v ∧ alphaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap v) ∧
        omegaSet γ ⊆ φ.MaxInv (fiberUnion cells hmap w)) :
    MorseSat φ D ρ := by
  refine qMorseDischarge_sound_cellCover φ D ρ cells hmap hflow htraj hcells
    hContain (fun v w hvw i j hi hj => ?_) hCell (fun i hi => ?_) hOrder
  · obtain ⟨ℓ, c, W, hlevel, hW, hneg⟩ := hCross v w hvw i j hi hj
    exact hasCrossingCert_of_flowDeriv hlevel hW hneg
  · obtain ⟨V, W, ε, hε, hV, hW, hrow⟩ := hTransit i hi
    exact hasTransitCert_of_rows_isCompact htraj (hcells i) hε hV hW hrow

end RowFloor

section OdeProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SolvesODEOn (φ : Semiflow E) (f : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, HasDerivWithinAt (fun s : ℝ => φ.flow s.toNNReal x) (f x) (Set.Ici 0) 0

theorem SolvesODEOn.mono {φ : Semiflow E} {f : E → E} {C D : Set E}
    (h : φ.SolvesODEOn f D) (hCD : C ⊆ D) : φ.SolvesODEOn f C :=
  fun x hx => h x (hCD hx)

theorem FlowDerivOn.of_solvesODE {φ : Semiflow E} {f : E → E} {V : E → ℝ}
    {DV : E → E →L[ℝ] ℝ} {C : Set E}
    (hode : φ.SolvesODEOn f C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x) :
    φ.FlowDerivOn V (fun x => DV x (f x)) C := by
  intro x hx
  have hcomp := (hV x hx).comp_hasDerivWithinAt_of_eq (0 : ℝ) (hode x hx)
    (by simp [Real.toNNReal_zero, φ.flow_zero])
  exact hcomp

end OdeProfile

section Gradient

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem FlowDerivOn.of_gradient {φ : Semiflow E} {f : E → E} {V : E → ℝ}
    {gradV : E → E} {C : Set E}
    (hode : φ.SolvesODEOn f C)
    (hV : ∀ x ∈ C, HasGradientAt V (gradV x) x) :
    φ.FlowDerivOn V (fun x => ⟪gradV x, f x⟫_ℝ) C := by
  intro x hx
  have h := FlowDerivOn.of_solvesODE hode
    (fun x hx => (hV x hx).hasFDerivAt) x hx
  simpa [InnerProductSpace.toDual_apply_apply] using h

end Gradient

section Specimens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasTransitCert_of_ode_rows {φ : Semiflow E} {C : Set E}
    {f : E → E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {ε : ℝ}
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hC : IsCompact C) (hε : 0 < ε)
    (hode : φ.SolvesODEOn f C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ y ∈ C, DV y (f y) ≤ -ε) :
    φ.HasTransitCert C :=
  hasTransitCert_of_rows_isCompact htraj hC hε
    (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
    (FlowDerivOn.of_solvesODE hode hV) hrow

theorem hasCrossingCert_of_ode {φ : Semiflow E} {O : Set E}
    {f : E → E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {c : ℝ}
    (hlevel : ∀ x ∈ O, V x = c)
    (hode : φ.SolvesODEOn f O)
    (hV : ∀ x ∈ O, HasFDerivAt V (DV x) x)
    (hneg : ∀ x ∈ O, DV x (f x) < 0) :
    φ.HasCrossingCert O :=
  hasCrossingCert_of_flowDeriv hlevel (FlowDerivOn.of_solvesODE hode hV) hneg

theorem hasFacetRows_of_ode_rows {φ : Semiflow E} {D N : Set E}
    {n : ℕ} {ℓ : Fin n → E → ℝ} {ε : Fin n → ℝ} {F : Fin n → Set E}
    {f : E → E} (Dℓ : Fin n → E → E →L[ℝ] ℝ)
    (htraj : ∀ x, Continuous fun t : ℝ≥0 => φ.flow t x)
    (hε : ∀ i, 0 < ε i)
    (hode : ∀ i, φ.SolvesODEOn f (F i))
    (hDℓ : ∀ i, ∀ x ∈ F i, HasFDerivAt (ℓ i) (Dℓ i x) x)
    (hrow : ∀ i, ∀ y ∈ F i, ε i ≤ Dℓ i y (f y))
    (hlocal : ∀ x ∈ frontier N, ∃ (A : Set (Fin n)) (U : Set E), U ∈ 𝓝 x ∧
      (∀ i ∈ A, ℓ i x = 0 ∧ F i ∈ 𝓝 x) ∧
      ∀ y ∈ U, y ∈ D → (∀ i ∈ A, 0 ≤ ℓ i y) → y ∈ N) :
    φ.HasFacetRows D N :=
  hasFacetRows_of_rows (fun i x => Dℓ i x (f x)) htraj hε
    (fun i x hx => (hDℓ i x hx).continuousAt.continuousWithinAt)
    (fun i => FlowDerivOn.of_solvesODE (hode i) (hDℓ i))
    hrow hlocal

end Specimens

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.qMorseDischarge_sound_of_rows
#print axioms Qtsl.Semiflow.SolvesODEOn.mono
#print axioms Qtsl.Semiflow.FlowDerivOn.of_solvesODE
#print axioms Qtsl.Semiflow.FlowDerivOn.of_gradient
#print axioms Qtsl.Semiflow.hasTransitCert_of_ode_rows
#print axioms Qtsl.Semiflow.hasCrossingCert_of_ode
#print axioms Qtsl.Semiflow.hasFacetRows_of_ode_rows

end PPLC
