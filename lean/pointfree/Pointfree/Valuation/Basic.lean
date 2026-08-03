import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

/-! # Valuations on frames

The ground floor of the point-free stochastics library: **valuations** on
a frame `L` — strict (`⊥ ↦ 0`), monotone, modular functions `L → ℝ≥0∞`.
When `L = Opens X` these are the point-free shadow of Borel measures
(the bridge module makes that precise, with τ-additivity as the exact
hypothesis class); on a general frame they are the objects of the
valuation-locale storey of the semantic-universe fibre column.

Design notes.

* **Modularity is the load-bearing axiom**: `μ a + μ b = μ (a ⊔ b) + μ (a ⊓ b)`.
  It is the lattice face of finite additivity — on opens it is exactly
  `measure_union_add_inter` — and it alone drives the subprobability
  promotion (see `Pointfree.Valuation.Promotion`), with no σ-algebra,
  no null sets, and no measurable-embedding machinery.
* **Scott continuity** (directed suprema preserved) is kept as a
  *mixin predicate*, not a structure field: the classical bridge
  produces it exactly on the τ-additive stratum, and the promotion and
  pushforward constructions preserve it, so each theorem carries
  precisely the continuity it needs.
* Heights land in `ℝ≥0∞`, matching the penalty scale of the semantic
  universe; subprobability (`μ ⊤ ≤ 1`) and probability (`μ ⊤ = 1`)
  are subtypes of the raw valuation type.
-/

namespace Pointfree

open scoped ENNReal

variable {L M : Type*}

/-- A **valuation** on a frame (only the lattice structure is consumed
at this ground floor; the frame structure feeds the Scott-continuity
predicate and the tower above): strict, monotone, modular. -/
structure Valuation (L : Type*) [Order.Frame L] where
  /-- The underlying function into extended nonnegative reals. -/
  toFun : L → ℝ≥0∞
  /-- Strictness: the bottom of the frame carries no mass. -/
  map_bot' : toFun ⊥ = 0
  /-- Monotonicity. -/
  monotone' : Monotone toFun
  /-- Modularity: the lattice face of finite additivity. -/
  modular' : ∀ a b : L, toFun a + toFun b = toFun (a ⊔ b) + toFun (a ⊓ b)

namespace Valuation

variable [Order.Frame L] [Order.Frame M]

instance : FunLike (Valuation L) L ℝ≥0∞ where
  coe := Valuation.toFun
  coe_injective := by
    rintro ⟨f, _, _, _⟩ ⟨g, _, _, _⟩ h
    simpa using h

@[ext]
theorem ext {μ ν : Valuation L} (h : ∀ a, μ a = ν a) : μ = ν :=
  DFunLike.ext _ _ h

@[simp] theorem map_bot (μ : Valuation L) : μ ⊥ = 0 := μ.map_bot'

theorem mono (μ : Valuation L) : Monotone μ := μ.monotone'

theorem modular (μ : Valuation L) (a b : L) :
    μ a + μ b = μ (a ⊔ b) + μ (a ⊓ b) := μ.modular' a b

@[simp] theorem coe_mk (f : L → ℝ≥0∞) (h₀ hm hmod) :
    ⇑(⟨f, h₀, hm, hmod⟩ : Valuation L) = f := rfl

theorem le_top_apply (μ : Valuation L) (a : L) : μ a ≤ μ ⊤ :=
  μ.mono le_top

/-- Frame homomorphisms are monotone (recorded here through the meet
operation alone, so no instance-path assumptions enter). -/
theorem _root_.FrameHom.monotone' (φ : FrameHom M L) : Monotone φ := by
  intro a b hab
  have h : a ⊓ b = a := inf_eq_left.mpr hab
  calc φ a = φ (a ⊓ b) := by rw [h]
    _ = φ a ⊓ φ b := map_inf φ a b
    _ ≤ φ b := inf_le_right

/-- **Scott continuity**: nonempty directed suprema are preserved.  On
`Opens X` this is τ-additivity of the underlying measure; on a general
frame it is the continuity clause of the valuation-locale literature. -/
def IsScottContinuous (μ : Valuation L) : Prop :=
  ∀ d : Set L, d.Nonempty → DirectedOn (· ≤ ·) d → μ (sSup d) = ⨆ a ∈ d, μ a

/-! ## The algebra of valuations -/

/-- The zero valuation. -/
instance : Zero (Valuation L) :=
  ⟨{ toFun := fun _ => 0
     map_bot' := rfl
     monotone' := monotone_const
     modular' := fun _ _ => rfl }⟩

@[simp] theorem zero_apply (a : L) : (0 : Valuation L) a = 0 := rfl

/-- Pointwise sum of valuations (modularity adds). -/
instance : Add (Valuation L) :=
  ⟨fun μ ν =>
    { toFun := fun a => μ a + ν a
      map_bot' := by simp
      monotone' := fun a b hab => add_le_add (μ.mono hab) (ν.mono hab)
      modular' := fun a b => by
        have hμ := μ.modular a b
        have hν := ν.modular a b
        calc μ a + ν a + (μ b + ν b) = μ a + μ b + (ν a + ν b) := by ring
          _ = μ (a ⊔ b) + μ (a ⊓ b) + (ν (a ⊔ b) + ν (a ⊓ b)) := by rw [hμ, hν]
          _ = μ (a ⊔ b) + ν (a ⊔ b) + (μ (a ⊓ b) + ν (a ⊓ b)) := by ring }⟩

@[simp] theorem add_apply (μ ν : Valuation L) (a : L) : (μ + ν) a = μ a + ν a := rfl

/-- Scaling of a valuation by an extended nonnegative real. -/
noncomputable instance : SMul ℝ≥0∞ (Valuation L) :=
  ⟨fun c μ =>
    { toFun := fun a => c * μ a
      map_bot' := by simp
      monotone' := fun a b hab => mul_le_mul' le_rfl (μ.mono hab)
      modular' := fun a b => by
        rw [← mul_add, μ.modular a b, mul_add] }⟩

@[simp] theorem smul_apply (c : ℝ≥0∞) (μ : Valuation L) (a : L) :
    (c • μ) a = c * μ a := rfl

/-- The pointwise order on valuations. -/
instance : PartialOrder (Valuation L) :=
  PartialOrder.lift (⇑) DFunLike.coe_injective

theorem le_def {μ ν : Valuation L} : μ ≤ ν ↔ ∀ a, μ a ≤ ν a := Iff.rfl

/-! ## Transport along frame homomorphisms

A frame homomorphism `φ : FrameHom M L` (the point-free face of a
continuous map `X → Y` when `M = Opens Y`, `L = Opens X`, `φ = comap`)
transports valuations by precomposition — the point-free pushforward. -/

/-- Pushforward of a valuation along a frame homomorphism, by
precomposition. -/
def map (φ : FrameHom M L) (μ : Valuation L) : Valuation M where
  toFun a := μ (φ a)
  map_bot' := by
    rw [show φ ⊥ = ⊥ from BotHomClass.map_bot φ]
    exact μ.map_bot
  monotone' := fun a b hab => μ.mono (φ.monotone' hab)
  modular' := fun a b => by
    have h := μ.modular (φ a) (φ b)
    rwa [← map_sup, ← map_inf] at h

@[simp] theorem map_apply (φ : FrameHom M L) (μ : Valuation L) (a : M) :
    μ.map φ a = μ (φ a) := rfl

/-- Pushforward preserves Scott continuity (frame homomorphisms
preserve directed suprema). -/
theorem IsScottContinuous.map {μ : Valuation L} (hμ : IsScottContinuous μ)
    (φ : FrameHom M L) : IsScottContinuous (μ.map φ) := by
  intro d hd hdir
  have himage : DirectedOn (· ≤ ·) (φ '' d) :=
    hdir.mono_comp fun _ _ h => φ.monotone' h
  have hsup : φ (sSup d) = sSup (φ '' d) := map_sSup φ d
  rw [map_apply, hsup, hμ (φ '' d) (hd.image φ) himage, iSup_image]
  simp only [map_apply]

/-! ## Point valuations

A *point* of a frame is a frame homomorphism into `Prop`; the
associated Dirac valuation asks whether the point lies in an element.
This is the point-free Dirac measure, and its Scott continuity is free
(frame points preserve arbitrary joins). -/

open Classical in
/-- The Dirac valuation of a frame point. -/
noncomputable def dirac (p : FrameHom L Prop) : Valuation L where
  toFun a := if p a then 1 else 0
  map_bot' := by
    have hbot : ¬ p ⊥ := fun h => by
      rw [BotHomClass.map_bot p] at h
      exact h
    show (if p ⊥ then (1 : ℝ≥0∞) else 0) = 0
    rw [if_neg hbot]
  monotone' := by
    intro a b hab
    show (if p a then (1 : ℝ≥0∞) else 0) ≤ (if p b then 1 else 0)
    by_cases ha : p a
    · have hb : p b := (p.monotone' hab) ha
      rw [if_pos ha, if_pos hb]
    · rw [if_neg ha]
      exact zero_le
  modular' := by
    intro a b
    show (if p a then (1 : ℝ≥0∞) else 0) + (if p b then 1 else 0)
      = (if p (a ⊔ b) then 1 else 0) + (if p (a ⊓ b) then 1 else 0)
    have hsup : p (a ⊔ b) ↔ p a ∨ p b := by
      rw [map_sup]
      exact Iff.rfl
    have hinf : p (a ⊓ b) ↔ p a ∧ p b := by
      rw [map_inf]
      exact Iff.rfl
    by_cases ha : p a <;> by_cases hb : p b <;>
      simp [ha, hb, hsup, hinf, add_comm]

open Classical in
theorem dirac_apply (p : FrameHom L Prop) (a : L) :
    dirac p a = if p a then 1 else 0 := rfl

@[simp] theorem dirac_top (p : FrameHom L Prop) : dirac p ⊤ = 1 := by
  have htop : p ⊤ := by
    rw [show p ⊤ = ⊤ from map_top p]
    trivial
  rw [dirac_apply, if_pos htop]

/-- Dirac valuations are Scott continuous: a frame point preserves
arbitrary joins, and the indicator of an existential is the supremum
of the indicators. -/
theorem isScottContinuous_dirac (p : FrameHom L Prop) :
    IsScottContinuous (dirac p) := by
  classical
  intro d hd hdir
  have hsup : p (sSup d) ↔ ∃ a ∈ d, p a := by
    rw [map_sSup, sSup_Prop_eq]
    constructor
    · rintro ⟨q, ⟨a, ha, rfl⟩, hq⟩
      exact ⟨a, ha, hq⟩
    · rintro ⟨a, ha, hpa⟩
      exact ⟨p a, ⟨a, ha, rfl⟩, hpa⟩
  by_cases h : ∃ a ∈ d, p a
  · obtain ⟨x, hx, hp⟩ := h
    have hx1 : dirac p x = 1 := by rw [dirac_apply, if_pos hp]
    rw [dirac_apply, if_pos (hsup.mpr ⟨x, hx, hp⟩)]
    apply le_antisymm
    · calc (1 : ℝ≥0∞) = dirac p x := hx1.symm
        _ ≤ ⨆ y ∈ d, dirac p y := le_iSup₂ (f := fun y (_ : y ∈ d) => dirac p y) x hx
    · refine iSup₂_le fun y _ => ?_
      rw [dirac_apply]
      split <;> simp
  · have h0 : ∀ y ∈ d, dirac p y = 0 := fun y hy => by
      rw [dirac_apply, if_neg (fun hpy => h ⟨y, hy, hpy⟩)]
    rw [dirac_apply, if_neg (fun hs => h (hsup.mp hs))]
    exact (le_antisymm (iSup₂_le fun y hy => le_of_eq (h0 y hy)) zero_le).symm

end Valuation

/-! ## Subprobability and probability valuations -/

variable (L) in
/-- The **subprobability carrier**: valuations of total mass at most
one.  Mass strictly below one is meaningful — a model licensed to lose
mass — which is why the carrier is the probability face's lower closure
and not the probability face. -/
def SubProb [Order.Frame L] : Type _ := {μ : Valuation L // μ ⊤ ≤ 1}

variable (L) in
/-- The **probability face**: valuations of total mass exactly one. -/
def Prob [Order.Frame L] : Type _ := {μ : Valuation L // μ ⊤ = 1}

namespace SubProb

variable [Order.Frame L]

instance : FunLike (SubProb L) L ℝ≥0∞ where
  coe μ := ⇑μ.1
  coe_injective := by
    rintro ⟨μ, _⟩ ⟨ν, _⟩ h
    exact Subtype.ext (DFunLike.coe_injective h)

@[ext]
theorem ext {μ ν : SubProb L} (h : ∀ a, μ a = ν a) : μ = ν :=
  DFunLike.ext _ _ h

/-- The underlying valuation. -/
def toValuation (μ : SubProb L) : Valuation L := μ.1

@[simp] theorem toValuation_apply (μ : SubProb L) (a : L) :
    μ.toValuation a = μ a := rfl

theorem mass_le_one (μ : SubProb L) : μ ⊤ ≤ 1 := μ.2

theorem apply_le_one (μ : SubProb L) (a : L) : μ a ≤ 1 :=
  le_trans (μ.1.le_top_apply a) μ.mass_le_one

theorem apply_ne_top (μ : SubProb L) (a : L) : μ a ≠ ∞ :=
  fun h => by simpa [h] using μ.apply_le_one a

@[simp] theorem map_bot (μ : SubProb L) : μ ⊥ = 0 := μ.1.map_bot

theorem mono (μ : SubProb L) : Monotone μ := μ.1.mono

theorem modular (μ : SubProb L) (a b : L) :
    μ a + μ b = μ (a ⊔ b) + μ (a ⊓ b) := μ.1.modular a b

/-- The zero subprobability valuation: the model that has lost all of
its mass. -/
instance : Zero (SubProb L) :=
  ⟨⟨0, by rw [Valuation.zero_apply]; exact zero_le⟩⟩

@[simp] theorem zero_apply (a : L) : (0 : SubProb L) a = 0 := rfl

end SubProb

namespace Prob

variable [Order.Frame L]

instance : FunLike (Prob L) L ℝ≥0∞ where
  coe μ := ⇑μ.1
  coe_injective := by
    rintro ⟨μ, _⟩ ⟨ν, _⟩ h
    exact Subtype.ext (DFunLike.coe_injective h)

@[ext]
theorem ext {μ ν : Prob L} (h : ∀ a, μ a = ν a) : μ = ν :=
  DFunLike.ext _ _ h

/-- The underlying valuation. -/
def toValuation (μ : Prob L) : Valuation L := μ.1

@[simp] theorem toValuation_apply (μ : Prob L) (a : L) :
    μ.toValuation a = μ a := rfl

@[simp] theorem mass_eq_one (μ : Prob L) : μ ⊤ = 1 := μ.2

theorem apply_le_one (μ : Prob L) (a : L) : μ a ≤ 1 :=
  μ.mass_eq_one ▸ μ.1.le_top_apply a

theorem apply_ne_top (μ : Prob L) (a : L) : μ a ≠ ∞ :=
  fun h => by simpa [h] using μ.apply_le_one a

@[simp] theorem map_bot (μ : Prob L) : μ ⊥ = 0 := μ.1.map_bot

theorem mono (μ : Prob L) : Monotone μ := μ.1.mono

theorem modular (μ : Prob L) (a b : L) :
    μ a + μ b = μ (a ⊔ b) + μ (a ⊓ b) := μ.1.modular a b

/-- Every probability valuation is a subprobability valuation. -/
def toSubProb (μ : Prob L) : SubProb L := ⟨μ.1, le_of_eq μ.2⟩

@[simp] theorem toSubProb_apply (μ : Prob L) (a : L) :
    μ.toSubProb a = μ a := rfl

end Prob

end Pointfree
