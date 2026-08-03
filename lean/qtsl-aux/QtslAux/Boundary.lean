import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Boundary values of piecewise certificates: the convexified value map

For a family of cells `C : ι → Set E` with per-cell drift values
`f : ι → E → ℝ`, this module studies the set-valued map
`hcValue C f x = closedConvexHull ℝ (activeValues C f x)`, the closed convex
hull of the values of all cells active at `x`. This is the natural value set
of a piecewise-defined vector field or Lie derivative on cell boundaries, in
the style of Filippov regularization.

Main results:

* `hcValue_le_of_forall_cell_le` and `sSup_hcValue_le`: a uniform bound
  `f i ≤ -ε` on every cell transfers to every element of `hcValue`, so a
  strict-decrease margin certified cell-by-cell survives convexification at
  boundaries.
* `upperHemicontinuous_hcValue`: for finitely many closed cells and
  continuous `f i`, the map `x ↦ hcValue C f x` is upper hemicontinuous
  (with `isCompact_hcValue`, it is a compact convex valued u.h.c. map).
* `convex_thickening`: the metric thickening of a convex set is convex.

The `Skeletons` section packages, as `Prop`-level statements, the bridges to
three consumers of this value map: upper semicontinuous envelopes
(`BoundaryUSCStatement`), almost-everywhere derivatives of `V` along Filippov
solutions (`BoundaryFilippovStatement`), and Clarke generalized derivatives
(`BoundaryClarkeStatement`), each with the lemma that a per-cell margin
bounds the corresponding derivative object (`uscEnvelope_le_of_bridge`,
`filippov_deriv_le_of_bridge`, `clarke_le_of_bridge`).
-/

namespace Qtsl.Boundary

open Set Filter Topology MeasureTheory
open scoped Pointwise

theorem convex_thickening {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set F} (hs : Convex ℝ s) (δ : ℝ) :
    Convex ℝ (Metric.thickening δ s) := by
  have h : Metric.thickening δ s = s + Metric.ball (0 : F) δ := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp hy
      have hball : y - z ∈ Metric.ball (0 : F) δ := by
        rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
        exact hyz
      have hmem := Set.add_mem_add hz hball
      simpa using hmem
    · intro hy
      obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.mp hy
      refine Metric.mem_thickening_iff.mpr ⟨b, hb, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left]
      simpa [Metric.mem_ball, dist_zero_right] using hc
  rw [h]
  exact hs.add (convex_ball (0 : F) δ)

section HcValue

variable {E : Type*} {ι : Type*}
variable (C : ι → Set E) (f : ι → E → ℝ)

def activeCells (x : E) : Set ι := {i | x ∈ C i}

def activeValues (x : E) : Set ℝ := (fun i => f i x) '' activeCells C x

theorem mem_activeValues {x : E} {y : ℝ} :
    y ∈ activeValues C f x ↔ ∃ i, x ∈ C i ∧ f i x = y := by
  simp [activeValues, activeCells]

def region : Set E := ⋃ i, C i

def hcValue (x : E) : Set ℝ := closedConvexHull ℝ (activeValues C f x)

theorem activeValues_subset_hcValue (x : E) :
    activeValues C f x ⊆ hcValue C f x :=
  subset_closedConvexHull

theorem convex_hcValue (x : E) : Convex ℝ (hcValue C f x) :=
  convex_closedConvexHull

theorem isClosed_hcValue (x : E) : IsClosed (hcValue C f x) :=
  isClosed_closedConvexHull

theorem hcValue_nonempty {x : E} (hx : x ∈ region C) :
    (hcValue C f x).Nonempty := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨f i x, activeValues_subset_hcValue C f x ⟨i, hi, rfl⟩⟩

theorem hcValue_le_of_forall_cell_le {ε : ℝ} (h : ∀ i, ∀ x ∈ C i, f i x ≤ -ε)
    (x : E) : ∀ y ∈ hcValue C f x, y ≤ -ε := by
  have hsub : activeValues C f x ⊆ Set.Iic (-ε) := by
    rintro y ⟨i, hi, rfl⟩
    exact h i x hi
  intro y hy
  exact closedConvexHull_min hsub (convex_Iic (-ε)) isClosed_Iic hy

theorem sSup_hcValue_le {ε : ℝ} (h : ∀ i, ∀ x ∈ C i, f i x ≤ -ε)
    {x : E} (hx : x ∈ region C) : sSup (hcValue C f x) ≤ -ε :=
  csSup_le (hcValue_nonempty C f hx) (hcValue_le_of_forall_cell_le C f h x)

variable [Finite ι]

theorem activeValues_finite (x : E) : (activeValues C f x).Finite :=
  Set.Finite.image _ (Set.toFinite _)

theorem hcValue_eq_convexHull (x : E) :
    hcValue C f x = convexHull ℝ (activeValues C f x) := by
  rw [hcValue, closedConvexHull_eq_closure_convexHull]
  exact ((activeValues_finite C f x).isClosed_convexHull ℝ).closure_eq

theorem isCompact_hcValue (x : E) : IsCompact (hcValue C f x) := by
  rw [hcValue_eq_convexHull]
  exact (activeValues_finite C f x).isCompact_convexHull ℝ

variable [TopologicalSpace E]

theorem eventually_activeCells_subset (hC : ∀ i, IsClosed (C i)) (x : E) :
    ∀ᶠ x' in 𝓝 x, activeCells C x' ⊆ activeCells C x := by
  have h : ∀ᶠ x' in 𝓝 x, ∀ i, x' ∈ C i → x ∈ C i := by
    rw [eventually_all]
    intro i
    by_cases hx : x ∈ C i
    · exact Eventually.of_forall fun _ _ => hx
    · filter_upwards [(hC i).isOpen_compl.mem_nhds hx] with x' hx'
      exact fun hmem => absurd hmem hx'
  exact h.mono fun x' hx' i hi => hx' i hi

theorem upperHemicontinuousAt_hcValue (hC : ∀ i, IsClosed (C i))
    (hf : ∀ i, Continuous (f i)) (x : E) :
    UpperHemicontinuousAt (hcValue C f) x := by
  refine UpperHemicontinuousAt.of_forall_isOpen fun U hU hxU => ?_
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_hcValue C f x).exists_thickening_subset_open hU hxU
  have h1 := eventually_activeCells_subset C hC x
  have h2 : ∀ᶠ x' in 𝓝 x, ∀ i, dist (f i x') (f i x) < δ := by
    rw [eventually_all]
    exact fun i => Metric.tendsto_nhds.mp ((hf i).tendsto x) δ hδ
  filter_upwards [h1, h2] with x' hsub hclose
  refine subset_trans ?_ hthick
  rw [hcValue_eq_convexHull]
  refine convexHull_min ?_ (convex_thickening (convex_hcValue C f x) δ)
  rintro y ⟨i, hi, rfl⟩
  exact Metric.mem_thickening_iff.mpr
    ⟨f i x, activeValues_subset_hcValue C f x ⟨i, hsub hi, rfl⟩, hclose i⟩

theorem upperHemicontinuous_hcValue (hC : ∀ i, IsClosed (C i))
    (hf : ∀ i, Continuous (f i)) :
    UpperHemicontinuous (hcValue C f) :=
  upperHemicontinuous_iff.mpr fun x => upperHemicontinuousAt_hcValue C f hC hf x

end HcValue

section Skeletons

variable {E : Type*} {ι : Type*}
variable (C : ι → Set E) (f : ι → E → ℝ)

structure IsUSCEnvelope {X : Type*} [TopologicalSpace X]
    (env : (X → ℝ) → X → ℝ) : Prop where
  usc : ∀ g, UpperSemicontinuous (env g)
  le_env : ∀ g, g ≤ env g
  env_min : ∀ g u, UpperSemicontinuous u → g ≤ u → env g ≤ u

def USCEnvelopeBridge (env : (E → ℝ) → E → ℝ) (g : E → ℝ) : Prop :=
  ∀ x ∈ region C, env g x ∈ hcValue C f x

theorem uscEnvelope_le_of_bridge {env : (E → ℝ) → E → ℝ} {g : E → ℝ} {ε : ℝ}
    (hbridge : USCEnvelopeBridge C f env g)
    (h : ∀ i, ∀ x ∈ C i, f i x ≤ -ε) :
    ∀ x ∈ region C, env g x ≤ -ε :=
  fun x hx => hcValue_le_of_forall_cell_le C f h x (env g x) (hbridge x hx)

def BoundaryUSCStatement [TopologicalSpace E]
    (env : (E → ℝ) → E → ℝ) (g : E → ℝ) : Prop :=
  (∀ i, IsClosed (C i)) → (∀ i, Continuous (f i)) →
  IsUSCEnvelope env →
  (∀ x ∈ region C, g x ∈ activeValues C f x) →
  USCEnvelopeBridge C f env g

def FilippovSelectionBridge (sol : (ℝ → E) → Prop) (V : E → ℝ) : Prop :=
  ∀ z : ℝ → E, sol z →
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∃ y ∈ hcValue C f (z t), HasDerivAt (fun s => V (z s)) y t

theorem filippov_deriv_le_of_bridge {sol : (ℝ → E) → Prop} {V : E → ℝ} {ε : ℝ}
    (hbridge : FilippovSelectionBridge C f sol V)
    (h : ∀ i, ∀ x ∈ C i, f i x ≤ -ε)
    {z : ℝ → E} (hz : sol z) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∀ y : ℝ, HasDerivAt (fun s => V (z s)) y t → y ≤ -ε := by
  filter_upwards [hbridge z hz] with t ht y hy
  obtain ⟨y₀, hy₀, hd₀⟩ := ht
  have hbound := hcValue_le_of_forall_cell_le C f h (z t) y₀ hy₀
  rwa [hy.unique hd₀]

def BoundaryFilippovStatement [TopologicalSpace E]
    (sol : (ℝ → E) → Prop) (V : E → ℝ) : Prop :=
  (∀ i, IsClosed (C i)) → (∀ i, Continuous (f i)) →
  FilippovSelectionBridge C f sol V

def ClarkeCoincidenceBridge (clarkeLie : (E → ℝ) → E → Set ℝ) (V : E → ℝ) : Prop :=
  ∀ x ∈ region C, clarkeLie V x ⊆ hcValue C f x

theorem clarke_le_of_bridge {clarkeLie : (E → ℝ) → E → Set ℝ} {V : E → ℝ} {ε : ℝ}
    (hbridge : ClarkeCoincidenceBridge C f clarkeLie V)
    (h : ∀ i, ∀ x ∈ C i, f i x ≤ -ε) :
    ∀ x ∈ region C, ∀ y ∈ clarkeLie V x, y ≤ -ε :=
  fun x hx y hy => hcValue_le_of_forall_cell_le C f h x y (hbridge x hx hy)

def BoundaryClarkeStatement [TopologicalSpace E]
    (clarkeLie : (E → ℝ) → E → Set ℝ) (V : E → ℝ) : Prop :=
  (∀ i, IsClosed (C i)) → (∀ i, Continuous (f i)) →
  ClarkeCoincidenceBridge C f clarkeLie V

def GraphPathConnectedStatement [TopologicalSpace E] : Prop :=
  (∀ i, IsClosed (C i)) → (∀ i, Continuous (f i)) →
  IsPathConnected (region C) →
  IsPathConnected {p : E × ℝ | p.1 ∈ region C ∧ p.2 ∈ hcValue C f p.1}

end Skeletons

end Qtsl.Boundary
