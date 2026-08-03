import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! # Presentation layer for composite systems

This module defines the data with which a composite dynamical system is
presented to the QTSL composition theorems, together with the tier
classification that decides which composition results apply.

* `Profile`: the dynamical species of a single chart — `ode` (deterministic
  drift), `sde` (diffusion), `gshs` (general stochastic hybrid system, i.e.
  jumps beyond counter-time ones), or `discrete` (counter-time jumps only).
* `ChartShape`: which generator fields a chart populates (drift, diffusion,
  jumps, and whether jumps are counter-time only); `ChartShape.profile`
  computes the induced profile, with `simp` lemmas for the standard shapes.
* `Tier` and `Profile.certConstructible`: the `admissible` tier is the
  fragment for which certificates can be constructed directly (`ode` and
  `discrete` profiles); everything else falls to the `core` tier.
* `System n`: `n` charts wired by `upstream` dependency sets, with a `rank`
  function whose `causality` field witnesses acyclicity (upstream
  components have strictly smaller rank).
* `System.qagTier`, with the characterizations
  `System.qagTier_admissible_iff` and `System.qagTier_core_iff`.
* `admissible_constructs`: soundness of the admissible-tier certificate
  constructor — a nonnegative combination of nonpositive inequality
  residuals plus arbitrary multiples of vanishing equality residuals is
  nonpositive on the region where those residual conditions hold.
-/

namespace Qtsl.QtslCompose

/-- The dynamical species of a chart: deterministic drift (`ode`),
diffusion (`sde`), general stochastic hybrid system (`gshs`), or
counter-time jumps only (`discrete`). -/
inductive Profile : Type where
  | ode | sde | gshs | discrete
  deriving DecidableEq, Repr

/-- The shape of a chart's generator: which of the drift, diffusion, and
jump fields are populated, and whether all jumps are triggered by counter
time (sampling clocks) rather than by state. -/
structure ChartShape : Type where
  drift : Bool
  diffusion : Bool
  jumps : Bool
  jumpsCounterTimeOnly : Bool
  deriving DecidableEq, Repr

/-- The profile induced by a chart shape: jumps beyond counter-time ones
(or combined with drift/diffusion) give `gshs`; pure counter-time jumps give
`discrete`; otherwise diffusion gives `sde` and the residual case is
`ode`. -/
def ChartShape.profile (c : ChartShape) : Profile :=
  if c.jumps then
    if c.jumpsCounterTimeOnly && !c.drift && !c.diffusion then .discrete
    else .gshs
  else if c.diffusion then .sde
  else .ode

@[simp] theorem profile_drift_only :
    ChartShape.profile ⟨true, false, false, false⟩ = .ode := rfl

@[simp] theorem profile_sde :
    ChartShape.profile ⟨true, true, false, false⟩ = .sde := rfl

theorem profile_gshs_of_jumps (dr di : Bool) :
    ChartShape.profile ⟨dr, di, true, false⟩ = .gshs := by
  simp [ChartShape.profile]

@[simp] theorem profile_discrete :
    ChartShape.profile ⟨false, false, true, true⟩ = .discrete := rfl

theorem profile_stochastic_of_diffusion (c : ChartShape) (h : c.diffusion = true) :
    c.profile = .sde ∨ c.profile = .gshs := by
  unfold ChartShape.profile
  rcases hj : c.jumps with _ | _
  · simp [hj, h]
  · rcases hc : c.jumpsCounterTimeOnly with _ | _ <;> simp [hj, hc, h]

/-- Tiers of the composition theory: `admissible` systems support direct
certificate construction, `core` systems require the general theory, and
`alias` marks derived presentations of an existing system. -/
inductive Tier : Type where
  | core | admissible | alias
  deriving DecidableEq, Repr

/-- Whether certificates for a profile are directly constructible: `ode`
and `discrete` are; the stochastic profiles `sde` and `gshs` are not. -/
def Profile.certConstructible : Profile → Bool
  | .ode => true
  | .discrete => true
  | .sde => false
  | .gshs => false

/-- A composite system of `n` charts: each chart has a shape, a finite set
of upstream dependencies, and a rank; the `causality` field witnesses that
the dependency relation is acyclic (every upstream component has strictly
smaller rank). -/
structure System (n : ℕ) : Type where
  charts : Fin n → ChartShape
  upstream : Fin n → Finset (Fin n)
  rank : Fin n → ℕ
  causality : ∀ j, ∀ i ∈ upstream j, rank i < rank j

/-- The assume-guarantee tier of a system: `admissible` when every chart's
profile admits direct certificate construction, `core` otherwise. -/
def System.qagTier {n : ℕ} (S : System n) : Tier :=
  if ∀ i, (S.charts i).profile.certConstructible then .admissible else .core

/-- A system is in the `admissible` tier if and only if every chart's
profile is `ode` or `discrete`. -/
theorem System.qagTier_admissible_iff {n : ℕ} (S : System n) :
    S.qagTier = .admissible ↔
      ∀ i, (S.charts i).profile = .ode ∨ (S.charts i).profile = .discrete := by
  unfold System.qagTier
  constructor
  · intro h i
    by_cases hall : ∀ i, (S.charts i).profile.certConstructible
    · have := hall i
      cases hp : (S.charts i).profile <;>
        simp_all [Profile.certConstructible]
    · rw [if_neg hall] at h
      exact absurd h (by simp)
  · intro h
    rw [if_pos]
    intro i
    rcases h i with hi | hi <;> simp [hi, Profile.certConstructible]

/-- A system falls to the `core` tier if and only if some chart has a
stochastic profile (`sde` or `gshs`). -/
theorem System.qagTier_core_iff {n : ℕ} (S : System n) :
    S.qagTier = .core ↔
      ∃ i, (S.charts i).profile = .sde ∨ (S.charts i).profile = .gshs := by
  have hsplit : S.qagTier = .admissible ∨ S.qagTier = .core := by
    unfold System.qagTier
    split <;> simp
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    have : S.qagTier = .admissible := by
      rw [S.qagTier_admissible_iff]
      intro i
      have := hno i
      cases hp : (S.charts i).profile <;> simp_all
    rw [this] at h
    exact absurd h (by simp)
  · intro ⟨i, hi⟩
    rcases hsplit with h | h
    · rw [S.qagTier_admissible_iff] at h
      rcases h i with ho | hd <;> rcases hi with hs | hs <;> simp_all
    · exact h

/-- Soundness of the admissible-tier certificate constructor: on a region
`R` where the inequality residuals `e i` are nonpositive and the equality
residuals `g k` vanish, any combination with nonnegative multipliers `lam`
on the inequalities and arbitrary multipliers `nu` on the equalities is
nonpositive. -/
theorem admissible_constructs {ι κIdx X : Type*} [Fintype ι] [Fintype κIdx]
    {R : Set X} (lam : ι → ℝ) (e : ι → X → ℝ) (nu : κIdx → ℝ) (g : κIdx → X → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (he : ∀ i, ∀ x ∈ R, e i x ≤ 0)
    (hg : ∀ k, ∀ x ∈ R, g k x = 0) :
    ∀ x ∈ R, (∑ i, lam i * e i x) + (∑ k, nu k * g k x) ≤ 0 := by
  intro x hx
  have h1 : (∑ i, lam i * e i x) ≤ 0 :=
    Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hlam i) (he i x hx)
  have h2 : (∑ k, nu k * g k x) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hg k x hx, mul_zero]
  linarith

end Qtsl.QtslCompose

#print axioms Qtsl.QtslCompose.System.qagTier_admissible_iff
#print axioms Qtsl.QtslCompose.System.qagTier_core_iff
#print axioms Qtsl.QtslCompose.admissible_constructs
