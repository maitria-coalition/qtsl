import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! # Discharging certificate side conditions along wires

This module provides the analytic ingredients for discharging the side
conditions that arise when guarantee bounds are passed along the wires of a
composed system.

* `IsClassK0Inf`: class-`K∞` comparison functions — zero at zero, monotone
  on `[0, ∞)`, and unbounded — the standard currency in which gain bounds
  along wires are expressed. The class is closed under addition
  (`IsClassK0Inf.add`) and composition (`IsClassK0Inf.comp`), matching
  parallel and series interconnection of wires, and is nonnegative on
  `[0, ∞)` (`IsClassK0Inf.nonneg`).
* `polynomial_discharge`: a checkable sufficient condition for a real
  polynomial to be class-`K∞` — zero constant coefficient, nonnegative
  derivative on `[0, ∞)`, positive degree, and nonnegative leading
  coefficient — so that polynomial gain certificates can be verified from
  their coefficients.
* `slack_triangle`: additive slack composes along a chain of two
  comparisons, with the slacks adding.
* `guarantee_leg_comp`: guarantee bounds compose contravariantly along a
  chain of wiring maps: bounds for `w₁` and `w₂` yield a bound for
  `w₂ ∘ w₁`.
-/

open Filter Set Polynomial

namespace Qtsl.QtslCompose

/-- A class-`K∞` comparison function: `κ 0 = 0`, `κ` is monotone on
`[0, ∞)`, and `κ` tends to infinity. (The usual definition also demands
continuity and strict monotonicity; this weaker predicate suffices for the
discharge lemmas here.) -/
structure IsClassK0Inf (κ : ℝ → ℝ) : Prop where
  zero_at_zero : κ 0 = 0
  mono : MonotoneOn κ (Ici 0)
  unbounded : Tendsto κ atTop atTop

namespace IsClassK0Inf

variable {κ κ₁ κ₂ : ℝ → ℝ}

theorem nonneg (h : IsClassK0Inf κ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ κ x :=
  h.zero_at_zero ▸ h.mono (Set.self_mem_Ici) hx hx

/-- The sum of two class-`K∞` functions is class-`K∞` (parallel
combination of wire gains). -/
theorem add (h₁ : IsClassK0Inf κ₁) (h₂ : IsClassK0Inf κ₂) :
    IsClassK0Inf (fun x => κ₁ x + κ₂ x) where
  zero_at_zero := by rw [h₁.zero_at_zero, h₂.zero_at_zero, add_zero]
  mono := fun a ha b hb hab => add_le_add (h₁.mono ha hb hab) (h₂.mono ha hb hab)
  unbounded := by
    have h0 : ∀ᶠ x in atTop, 0 ≤ κ₂ x := h₂.unbounded.eventually_ge_atTop 0
    exact tendsto_atTop_mono' _
      (h0.mono fun x hx => le_add_of_nonneg_right hx) h₁.unbounded

/-- The composition of two class-`K∞` functions is class-`K∞` (series
combination of wire gains). -/
theorem comp (h₁ : IsClassK0Inf κ₁) (h₂ : IsClassK0Inf κ₂) :
    IsClassK0Inf (κ₁ ∘ κ₂) where
  zero_at_zero := by
    simp only [Function.comp_apply, h₂.zero_at_zero, h₁.zero_at_zero]
  mono := h₁.mono.comp h₂.mono fun x hx => h₂.nonneg hx
  unbounded := h₁.unbounded.comp h₂.unbounded

end IsClassK0Inf

/-- Checkable discharge for polynomial gains: a real polynomial with zero
constant coefficient, derivative nonnegative on `[0, ∞)`, positive degree,
and nonnegative leading coefficient is a class-`K∞` function. -/
theorem polynomial_discharge (p : Polynomial ℝ)
    (h0 : p.coeff 0 = 0)
    (hderiv : ∀ x : ℝ, 0 ≤ x → 0 ≤ p.derivative.eval x)
    (hdeg : 0 < p.degree) (hlead : 0 ≤ p.leadingCoeff) :
    IsClassK0Inf (fun x => p.eval x) where
  zero_at_zero := by rw [← Polynomial.coeff_zero_eq_eval_zero, h0]
  mono := by
    have hconv : Convex ℝ (Ici (0 : ℝ)) := convex_Ici 0
    refine monotoneOn_of_deriv_nonneg hconv
      (Polynomial.continuous p).continuousOn
      (Polynomial.differentiable p).differentiableOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [Polynomial.deriv]
    exact hderiv x (le_of_lt hx)
  unbounded := p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead

/-- Additive slacks compose: `f ≤ g + c₁` and `g ≤ h + c₂` yield
`f ≤ h + (c₁ + c₂)`. -/
theorem slack_triangle {X : Type*} {f g h : X → ℝ} {c₁ c₂ : ℝ}
    (h₁ : ∀ x, f x ≤ g x + c₁) (h₂ : ∀ x, g x ≤ h x + c₂) :
    ∀ x, f x ≤ h x + (c₁ + c₂) := fun x => by linarith [h₁ x, h₂ x]

/-- Guarantee bounds compose along chained wiring maps: if `γ₂ ∘ w₁ ≤ γ₁`
and `γ₃ ∘ w₂ ≤ γ₂`, then `γ₃ ∘ (w₂ ∘ w₁) ≤ γ₁`. -/
theorem guarantee_leg_comp {A B C : Type*} {w₁ : A → B} {w₂ : B → C}
    {γ₁ : A → ℝ} {γ₂ : B → ℝ} {γ₃ : C → ℝ}
    (h₁ : ∀ a, γ₂ (w₁ a) ≤ γ₁ a) (h₂ : ∀ b, γ₃ (w₂ b) ≤ γ₂ b) :
    ∀ a, γ₃ (w₂ (w₁ a)) ≤ γ₁ a := fun a => (h₂ (w₁ a)).trans (h₁ a)

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.IsClassK0Inf.add
#print axioms Qtsl.QtslCompose.IsClassK0Inf.comp
#print axioms Qtsl.QtslCompose.polynomial_discharge
#print axioms Qtsl.QtslCompose.slack_triangle
#print axioms Qtsl.QtslCompose.guarantee_leg_comp
