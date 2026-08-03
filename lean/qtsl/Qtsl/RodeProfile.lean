import Qtsl.OdeProfile

/-!
# The random-ODE layer

A RODE in normal form is an ODE family `ẋ = f(θ, x)` with the
realization `θ` drawn from a declared uncertainty box and constant
along each realization. The universal quantification over realizations
lives entirely on the row side: a single Bernstein-cone row family over
the product box (θ adjoined as extra axes) yields the `∀ θ` property
form, with no new analytic machinery.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open Set Topology
open scoped NNReal

section RodeProfile

variable {Θ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SolvesRODEOn (φ : Θ → Semiflow E) (f : Θ → E → E) (Θs : Set Θ)
    (C : Set E) : Prop :=
  ∀ θ ∈ Θs, (φ θ).SolvesODEOn (f θ) C

theorem SolvesRODEOn.mono {φ : Θ → Semiflow E} {f : Θ → E → E}
    {Θs : Set Θ} {C D : Set E} (h : SolvesRODEOn φ f Θs D) (hCD : C ⊆ D) :
    SolvesRODEOn φ f Θs C :=
  fun θ hθ => (h θ hθ).mono hCD

theorem hasTransitCert_of_rode_rows {φ : Θ → Semiflow E} {Θs : Set Θ}
    {C : Set E} {f : Θ → E → E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {ε : ℝ}
    (htraj : ∀ θ ∈ Θs, ∀ x, Continuous fun t : ℝ≥0 => (φ θ).flow t x)
    (hC : IsCompact C) (hε : 0 < ε)
    (hode : SolvesRODEOn φ f Θs C)
    (hV : ∀ x ∈ C, HasFDerivAt V (DV x) x)
    (hrow : ∀ θ ∈ Θs, ∀ y ∈ C, DV y (f θ y) ≤ -ε) :
    ∀ θ ∈ Θs, (φ θ).HasTransitCert C :=
  fun θ hθ =>
    hasTransitCert_of_ode_rows (htraj θ hθ) hC hε (hode θ hθ) hV (hrow θ hθ)

theorem hasTransitCert_of_rode_rows_family {φ : Θ → Semiflow E}
    {Θs : Set Θ} {C : Set E} {f : Θ → E → E} {V : Θ → E → ℝ}
    {DV : Θ → E → E →L[ℝ] ℝ} {ε : Θ → ℝ}
    (htraj : ∀ θ ∈ Θs, ∀ x, Continuous fun t : ℝ≥0 => (φ θ).flow t x)
    (hC : IsCompact C) (hε : ∀ θ ∈ Θs, 0 < ε θ)
    (hode : SolvesRODEOn φ f Θs C)
    (hV : ∀ θ ∈ Θs, ∀ x ∈ C, HasFDerivAt (V θ) (DV θ x) x)
    (hrow : ∀ θ ∈ Θs, ∀ y ∈ C, DV θ y (f θ y) ≤ -(ε θ)) :
    ∀ θ ∈ Θs, (φ θ).HasTransitCert C :=
  fun θ hθ =>
    hasTransitCert_of_ode_rows (htraj θ hθ) hC (hε θ hθ) (hode θ hθ)
      (hV θ hθ) (hrow θ hθ)

theorem hasCrossingCert_of_rode {φ : Θ → Semiflow E} {Θs : Set Θ}
    {O : Set E} {f : Θ → E → E} {V : E → ℝ} {DV : E → E →L[ℝ] ℝ} {c : ℝ}
    (hlevel : ∀ x ∈ O, V x = c)
    (hode : SolvesRODEOn φ f Θs O)
    (hV : ∀ x ∈ O, HasFDerivAt V (DV x) x)
    (hneg : ∀ θ ∈ Θs, ∀ x ∈ O, DV x (f θ x) < 0) :
    ∀ θ ∈ Θs, (φ θ).HasCrossingCert O :=
  fun θ hθ => hasCrossingCert_of_ode hlevel (hode θ hθ) hV (hneg θ hθ)

end RodeProfile

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.SolvesRODEOn.mono
#print axioms Qtsl.Semiflow.hasTransitCert_of_rode_rows
#print axioms Qtsl.Semiflow.hasTransitCert_of_rode_rows_family
#print axioms Qtsl.Semiflow.hasCrossingCert_of_rode

end PPLC
