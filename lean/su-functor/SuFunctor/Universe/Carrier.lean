import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The semantic universe: real-valued distributions and lsc penalty functionals

This module carries the semantic (real-valued) stratum of the universe of
penalty functionals, at the finite-outcome tier:

* `Universe.belCarrier V` / `Universe.BelState V` — the carrier
  $\Delta_{\le 1}(V)$: subprobability distributions on a finite outcome
  space, as a compact convex subset of `V → ℝ` (compactness is proved
  here; the subtype inherits the metric topology, so the carrier is a
  compact metric space).
* `Universe.Penalty V` — penalty functionals `BelState V → ℝ≥0∞`,
  the points of the universe.  Specifications and systems both denote
  penalty functionals; the satisfaction judgment is the pointwise order
  (see `SuFunctor.Universe.Judgment`).  Vocabulary: the **belief
  states** of the epistemology are these penalty functionals — a
  belief state penalizes distributions; the carrier points it
  penalizes are distributions, never themselves "belief states".
* **Citizenship is lower semicontinuity, and nothing else.**  No shape
  axiom (convexity, quasiconvexity) is imposed on citizens: convexity
  re-enters as a *certification chart* (see
  `SuFunctor.Universe.ConvexChart`), not as a citizenship requirement.
* `Universe.wall C` — the `{0, ⊤}`-valued penalty of a set of
  distributions (`0` inside, `⊤` outside).  Walls are citizens exactly for
  closed `C` (`lowerSemicontinuous_wall_iff`) — closed, *not*
  convex-closed: the non-convex walls are deliberate citizens (an
  independence assertion is one; see the witness section of
  `SuFunctor.Universe.ConvexChart`).

This is the real-valued face of the graded layer whose exact-rational
face shipped in the retired graded tier (`SuFunctorLegacy.Bridge`: `SuFunctor.Penalty`, heights in
`ENNRat`, walls as `SuFunctor.specPenalty`): rational data live at the
certificate boundary, real data in the semantics.  The two layers share
their vocabulary — walls, the pointwise order, conjunction as join — by
design.

**Stratum honesty.**  Everything here is the finite-`V` stratum.  The
carrier is compact and finite-dimensional, so the operations table of
`SuFunctor.Universe.Closure` holds without side conditions; on Polish
record spaces, marginalization (inf-projection) and the duality pairing
acquire tightness riders that are vacuous here (compact fibres,
finite-dimensional separation).
-/

namespace SuFunctor.Universe

open scoped ENNReal

variable (V : Type*) [Fintype V]

/-- The carrier $\Delta_{\le 1}(V)$ of subprobability distributions, as a
subset of `V → ℝ`: pointwise nonnegative weight functions of total mass
at most one.  Mass strictly below one is meaningful (a model licensed to
lose mass), which is why the carrier is the simplex's lower closure and
not the simplex. -/
def belCarrier : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v ≤ 1}

variable {V}

theorem mem_belCarrier_iff {x : V → ℝ} :
    x ∈ belCarrier V ↔ (∀ v, 0 ≤ x v) ∧ ∑ v, x v ≤ 1 :=
  Iff.rfl

theorem convex_belCarrier : Convex ℝ (belCarrier V) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun v => add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v)), ?_⟩
  have hsum : ∑ v, (a • x + b • y) v = a * ∑ v, x v + b * ∑ v, y v := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  calc a * ∑ v, x v + b * ∑ v, y v ≤ a * 1 + b * 1 := by
        gcongr
        · exact hx.2
        · exact hy.2
    _ = 1 := by rw [mul_one, mul_one, hab]

theorem isClosed_belCarrier : IsClosed (belCarrier V) := by
  have h1 : IsClosed {x : V → ℝ | ∀ v, 0 ≤ x v} := by
    have : {x : V → ℝ | ∀ v, 0 ≤ x v} = ⋂ v, {x : V → ℝ | 0 ≤ x v} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  have h2 : IsClosed {x : V → ℝ | ∑ v, x v ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  exact h1.inter h2

/-- Each coordinate of a distribution is at most `1`. -/
theorem apply_le_one_of_mem_belCarrier {x : V → ℝ} (hx : x ∈ belCarrier V)
    (v : V) : x v ≤ 1 := by
  have h : x v ≤ ∑ w, x w :=
    Finset.single_le_sum (fun w _ => hx.1 w) (Finset.mem_univ v)
  exact h.trans hx.2

theorem belCarrier_subset_box :
    belCarrier V ⊆ Set.univ.pi fun _ : V => Set.Icc (0 : ℝ) 1 := by
  intro x hx v _
  exact ⟨hx.1 v, apply_le_one_of_mem_belCarrier hx v⟩

/-- The carrier is compact: it is a closed subset of the unit box. -/
theorem isCompact_belCarrier : IsCompact (belCarrier V) :=
  IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
    isClosed_belCarrier belCarrier_subset_box

variable (V) in
/-- A subprobability distribution on the finite outcome space `V`: a
point of `belCarrier V`.  As a subtype of the (finite-dimensional,
metric) space `V → ℝ` it is a compact metric space — the honest topology
statement of the finite stratum.  (The identifier `BelState` predates
the vocabulary convention that reserves "belief state" for penalty
functionals; a `BelState` is a distribution — a point a belief state
penalizes.) -/
abbrev BelState : Type _ := ↥(belCarrier V)

instance : CompactSpace (BelState V) :=
  isCompact_iff_compactSpace.mp isCompact_belCarrier

namespace BelState

theorem nonneg (μ : BelState V) (v : V) : 0 ≤ (μ : V → ℝ) v := μ.2.1 v

theorem apply_le_one (μ : BelState V) (v : V) : (μ : V → ℝ) v ≤ 1 :=
  apply_le_one_of_mem_belCarrier μ.2 v

/-- The total mass of a distribution. -/
def mass (μ : BelState V) : ℝ := ∑ v, (μ : V → ℝ) v

theorem mass_nonneg (μ : BelState V) : 0 ≤ μ.mass :=
  Finset.sum_nonneg fun v _ => μ.nonneg v

theorem mass_le_one (μ : BelState V) : μ.mass ≤ 1 := μ.2.2

variable (V) in
/-- The zero distribution: the model that has lost all of its mass.  It
exists over every carrier and is the bottom of every liveness
consideration (compare `SuFunctor.SubPMF.zero` at the rational
stratum). -/
def zero : BelState V :=
  ⟨0, fun _ => le_rfl, by simp⟩

@[simp] theorem zero_apply (v : V) : ((zero V : BelState V) : V → ℝ) v = 0 := rfl

@[simp] theorem mass_zero : (zero V).mass = 0 := by simp [mass]

/-- The point mass at an outcome. -/
def dirac [DecidableEq V] (v : V) : BelState V :=
  ⟨Pi.single v 1, by
    constructor
    · intro w
      rcases eq_or_ne w v with rfl | h
      · simp
      · simp [h]
    · rw [Finset.sum_eq_single v (fun w _ hw => by simp [hw])
        (fun h => absurd (Finset.mem_univ v) h)]
      simp⟩

@[simp] theorem dirac_apply_same [DecidableEq V] (v : V) :
    ((dirac v : BelState V) : V → ℝ) v = 1 := by
  simp [dirac]

theorem dirac_apply_of_ne [DecidableEq V] {v w : V} (h : w ≠ v) :
    ((dirac v : BelState V) : V → ℝ) w = 0 := by
  simp [dirac, h]

@[simp] theorem mass_dirac [DecidableEq V] (v : V) : (dirac v : BelState V).mass = 1 := by
  rw [mass, Finset.sum_eq_single v (fun w _ hw => dirac_apply_of_ne hw)
    (fun h => absurd (Finset.mem_univ v) h)]
  simp

/-- The convex combination of two distributions (the carrier is convex,
so the combination stays inside). -/
def mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : BelState V) : BelState V :=
  ⟨t • (μ : V → ℝ) + (1 - t) • (ν : V → ℝ),
    convex_belCarrier μ.2 ν.2 h0 (by linarith) (by ring)⟩

@[simp] theorem mix_apply (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : BelState V)
    (v : V) :
    ((mix t h0 h1 μ ν : BelState V) : V → ℝ) v
      = t * (μ : V → ℝ) v + (1 - t) * (ν : V → ℝ) v := rfl

theorem mix_coe (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : BelState V) :
    ((mix t h0 h1 μ ν : BelState V) : V → ℝ)
      = t • (μ : V → ℝ) + (1 - t) • (ν : V → ℝ) := rfl

end BelState

variable (V) in
/-- A penalty functional: a point of the semantic universe.  Heights are
extended nonnegative reals; `⊤` is hard violation, `0` perfect
compatibility.  Specifications and systems both denote penalty
functionals, and the satisfaction judgment is the pointwise order
(`SuFunctor.Universe.Sat`).

Citizenship in the universe is lower semicontinuity
(`LowerSemicontinuous`, with respect to the compact metric topology of
`BelState V`) — and nothing else; see the module docstring. -/
abbrev Penalty : Type _ := BelState V → ℝ≥0∞

/-- The sublevel reading of citizenship: a penalty is lower
semicontinuous iff every tolerance slice `{μ | σ μ ≤ s}` is closed.
This is the form the tolerance-indexed certification chart consumes. -/
theorem lowerSemicontinuous_iff_isClosed_sublevel {σ : Penalty V} :
    LowerSemicontinuous σ ↔ ∀ s : ℝ≥0∞, IsClosed {μ : BelState V | σ μ ≤ s} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  simp only [Set.preimage, Set.mem_Iic]

/-! ## Walls

The `{0, ⊤}`-valued penalties: `wall C` is `0` on `C` and `⊤` off it.
These are the denotations of crisp (allowed-or-forbidden) claims; the
judgment restricted to walls is containment
(`SuFunctor.Universe.sat_wall_wall_iff`).  At the exact-rational
stratum the same objects ship as `SuFunctor.specPenalty`. -/

open Classical in
/-- The wall of a set of distributions: `0` inside, `⊤` outside. -/
noncomputable def wall (C : Set (BelState V)) : Penalty V :=
  fun μ => if μ ∈ C then 0 else ⊤

theorem wall_apply_of_mem {C : Set (BelState V)} {μ : BelState V} (h : μ ∈ C) :
    wall C μ = 0 := by simp [wall, h]

theorem wall_apply_of_not_mem {C : Set (BelState V)} {μ : BelState V}
    (h : μ ∉ C) : wall C μ = ⊤ := by simp [wall, h]

@[simp] theorem wall_univ : wall (Set.univ : Set (BelState V)) = 0 := by
  funext μ; simp [wall]

@[simp] theorem wall_empty : wall (∅ : Set (BelState V)) = ⊤ := by
  funext μ; simp [wall]

theorem wall_le_iff {C : Set (BelState V)} {σ : Penalty V} :
    wall C ≤ σ ↔ ∀ μ, μ ∉ C → σ μ = ⊤ := by
  constructor
  · intro h μ hμ
    have := h μ
    rw [wall_apply_of_not_mem hμ] at this
    exact top_le_iff.mp this
  · intro h μ
    by_cases hμ : μ ∈ C
    · rw [wall_apply_of_mem hμ]; exact zero_le
    · rw [wall_apply_of_not_mem hμ, h μ hμ]

theorem le_wall_iff {C : Set (BelState V)} {σ : Penalty V} :
    σ ≤ wall C ↔ ∀ μ ∈ C, σ μ = 0 := by
  constructor
  · intro h μ hμ
    have := h μ
    rw [wall_apply_of_mem hμ] at this
    exact le_antisymm this zero_le
  · intro h μ
    by_cases hμ : μ ∈ C
    · rw [wall_apply_of_mem hμ, h μ hμ]
    · rw [wall_apply_of_not_mem hμ]; exact le_top

/-- The wall order is containment, contravariantly: a larger permitted
set is a weaker requirement. -/
theorem wall_le_wall_iff {C D : Set (BelState V)} :
    wall D ≤ wall C ↔ C ⊆ D := by
  rw [wall_le_iff]
  constructor
  · intro h μ hμ
    by_contra hD
    have := h μ hD
    rw [wall_apply_of_mem hμ] at this
    exact ENNReal.zero_ne_top this
  · intro hCD μ hμ
    exact wall_apply_of_not_mem fun hC => hμ (hCD hC)

theorem wall_anti {C D : Set (BelState V)} (h : C ⊆ D) : wall D ≤ wall C :=
  wall_le_wall_iff.mpr h

/-- Walls are citizens exactly on closed sets — closedness, **not**
convexity, is the membership condition.  (The non-convex walls this
admits are load-bearing: see the independence witness in
`SuFunctor.Universe.ConvexChart`.) -/
theorem lowerSemicontinuous_wall_iff {C : Set (BelState V)} :
    LowerSemicontinuous (wall C) ↔ IsClosed C := by
  constructor
  · intro h
    have : C = {μ : BelState V | wall C μ ≤ 0} := by
      ext μ
      constructor
      · intro hμ; simp [wall_apply_of_mem hμ]
      · intro hμ
        by_contra hC
        rw [Set.mem_setOf_eq, wall_apply_of_not_mem hC, top_le_iff] at hμ
        exact ENNReal.zero_ne_top hμ
    rw [this]
    exact lowerSemicontinuous_iff_isClosed_sublevel.mp h 0
  · intro hC μ y hy
    by_cases hμ : μ ∈ C
    · rw [wall_apply_of_mem hμ] at hy
      exact absurd hy (by simp)
    · have htop : y < ⊤ := by
        rw [wall_apply_of_not_mem hμ] at hy; exact hy
      have hmem : ∀ᶠ ν in nhds μ, ν ∈ Cᶜ :=
        hC.isOpen_compl.mem_nhds hμ
      filter_upwards [hmem] with ν hν
      rw [wall_apply_of_not_mem hν]
      exact htop

/-- A `{0, ⊤}`-valued penalty is a wall — the wall of its zero set.  The
crisp fragment of the universe is exactly the walls. -/
theorem eq_wall_of_two_valued {σ : Penalty V}
    (h : ∀ μ, σ μ = 0 ∨ σ μ = ⊤) : σ = wall {μ | σ μ = 0} := by
  funext μ
  rcases h μ with h0 | htop
  · rw [wall_apply_of_mem h0, h0]
  · rw [htop, wall_apply_of_not_mem]
    rw [Set.mem_setOf_eq, htop]
    exact ENNReal.top_ne_zero

end SuFunctor.Universe
