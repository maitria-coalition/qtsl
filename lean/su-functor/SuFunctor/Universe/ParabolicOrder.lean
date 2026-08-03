import Mathlib.Data.Real.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Antichain

/-! # The degenerate causal order of the parabolic (cylinder) column

The spacetime-sites design (its Column P)
instantiates the structured-site axioms at *cylinder* windows
`U × I` whose stage poset carries the **degenerate causal order**

  `(x, s) ≤ (y, t)  ↔  s < t  ∨  (x, s) = (y, t)`,

the order-theoretic meaning of infinite propagation speed: every
strictly earlier stage precedes every later stage, at arbitrary spatial
displacement, while distinct simultaneous stages are incomparable
(equal-time slices are antichains).  This module is the order-tier Lean
shadow of that column — the part available
before any site formalization exists:

* `CylPt X` with its `PartialOrder`;
* `mk_lt_mk_of_time_lt` — infinite propagation speed, as a theorem;
* `isAntichain_timeSlice` — simultaneity slices are antichains
  (spacelike separation exists exactly at equal times);
* `IsChain.time_injOn` — chains are worldlines: along a chain, time
  determines the point, so (T2)'s timelines are graphs over time;
* `punitOrderIso : CylPt PUnit ≃o ℝ` — **the temporal site is the
  one-spatial-cell case**: at a trivial spatial factor the degenerate
  causal order *is* the classical order of the timeline.  This is the
  order-tier half of the sites memo's specialization theorem; the
  full-stack statement (coverage, duration valuations, tangency,
  carrier pullback on the nose) stays at design tier, gated on a site
  formalization that does not exist yet, per the memo's own pricing.

The heat-on-torus instance (`SuFunctor.Adequacy.HeatTorus`) is the
first consumer: its window is `𝕋¹ × I`, i.e. `CylPt ℝ` restricted to a
cylinder, with the spatial mesh living at the composition tier (walls),
never in the stage order — parabolic dependence structure is wiring
data, not order data, which is why nothing below mentions the heat
equation. -/

namespace SuFunctor.Universe

/-- A stage point of a cylinder window: a spatial position and a time.
The order is the degenerate causal order of the parabolic column. -/
structure CylPt (X : Type*) where
  /-- The spatial position. -/
  pos : X
  /-- The time coordinate. -/
  time : ℝ

namespace CylPt

variable {X : Type*}

instance : PartialOrder (CylPt X) where
  le p q := p.time < q.time ∨ p = q
  le_refl _ := Or.inr rfl
  le_trans p q r := by
    rintro (h₁ | rfl) (h₂ | rfl)
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inl h₁
    · exact Or.inl h₂
    · exact Or.inr rfl
  le_antisymm p q h₁ h₂ := by
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact absurd (h₁.trans h₂) (lt_irrefl _)
      · exact h₂.symm
    · exact h₁

theorem le_iff {p q : CylPt X} : p ≤ q ↔ p.time < q.time ∨ p = q :=
  Iff.rfl

/-- **Infinite propagation speed**: a strictly earlier stage precedes
every later stage, at arbitrary spatial displacement.  This is the
degenerate causal order's defining feature — the parabolic column's
"cone" is the whole earlier cylinder. -/
theorem mk_lt_mk_of_time_lt {s t : ℝ} (h : s < t) (x y : X) :
    (⟨x, s⟩ : CylPt X) < ⟨y, t⟩ := by
  refine lt_of_le_of_ne (Or.inl h) fun hxy => ?_
  exact absurd (congrArg time hxy) (ne_of_lt h)

/-- Comparability forces a time inequality or equality of points. -/
theorem time_le_of_le {p q : CylPt X} (h : p ≤ q) : p.time ≤ q.time := by
  rcases h with h | rfl
  · exact h.le
  · exact le_rfl

/-- Distinct simultaneous stages are incomparable. -/
theorem not_le_of_ne_of_time_eq {p q : CylPt X} (hne : p ≠ q)
    (ht : p.time = q.time) : ¬ p ≤ q := by
  rintro (h | rfl)
  · exact absurd ht (ne_of_lt h)
  · exact hne rfl

/-- **Simultaneity slices are antichains**: at equal times, spacelike
separation is total.  Together with `mk_lt_mk_of_time_lt` this
characterizes the degenerate causal order — all of space is spacelike
at equal times and timelike across any time gap. -/
theorem isAntichain_timeSlice (t : ℝ) :
    IsAntichain (· ≤ ·) {p : CylPt X | p.time = t} := by
  intro p hp q hq hne
  exact not_le_of_ne_of_time_eq hne (hp.trans hq.symm)

/-- **Chains are worldlines**: along a chain of the degenerate causal
order, time determines the point — (T2)'s timelines are graphs over
time, traversed at arbitrary (unbounded) speed. -/
theorem _root_.IsChain.time_injOn {S : Set (CylPt X)}
    (hS : IsChain (· ≤ ·) S) : S.InjOn time := by
  intro p hp q hq ht
  by_contra hne
  rcases hS hp hq hne with h | h
  · exact not_le_of_ne_of_time_eq hne ht h
  · exact not_le_of_ne_of_time_eq (Ne.symm hne) ht.symm h

/-- **The temporal site is the one-spatial-cell case** (order tier): at
a trivial spatial factor, the degenerate causal order is the classical
linear order of the timeline.  The sites memo's specialization theorem,
mechanized at the tier that exists today. -/
def punitOrderIso : CylPt PUnit ≃o ℝ where
  toFun p := p.time
  invFun t := ⟨PUnit.unit, t⟩
  left_inv p := by cases p with | mk x t => cases x; rfl
  right_inv _ := rfl
  map_rel_iff' {p q} := by
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · cases p with | mk x s => cases q with | mk y t =>
          cases x; cases y
          exact Or.inr (by simpa using h)
    · exact time_le_of_le

end CylPt

end SuFunctor.Universe

#print axioms SuFunctor.Universe.CylPt.mk_lt_mk_of_time_lt
#print axioms SuFunctor.Universe.CylPt.isAntichain_timeSlice
#print axioms SuFunctor.Universe.CylPt.punitOrderIso
