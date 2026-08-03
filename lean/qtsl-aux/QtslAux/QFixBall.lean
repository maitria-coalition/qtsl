import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Certified fixed-point localization in a closed ball

This module proves soundness of a Banach-type certificate that localizes a
fixed point of a map `f` near an approximate fixed point `x₀`. The certificate
data are a Lipschitz constant `K < 1` valid on `closedBall x₀ r`, a residual
bound `dist (f x₀) x₀ ≤ δ`, and the radius side condition `δ + K * r ≤ r`.

Principal declarations:

* `mapsTo_closedBall`: under the certificate, `f` maps the ball into itself.
* `sound_QFixBall`: existence and uniqueness of a fixed point of `f` in
  `closedBall x₀ r` (Banach fixed-point theorem on the complete ball, plus a
  contraction uniqueness argument `fixedPoint_unique`).
* `dist_fixedPoint_le`: the a-posteriori location bound
  `dist x₀ y ≤ δ / (1 - K)` for any fixed point `y` in the ball, and
  `anchored_le_radius`: this radius is at most `r`.
* `lipschitzWith_affine`, `sound_QFixBall_affine`: the affine specialization
  `x ↦ A x + c` on a finite-dimensional Euclidean space, where the Lipschitz
  datum is an operator-norm bound `‖A‖₊ ≤ K`.
-/

namespace Qtsl

namespace QFixBall

open Metric Function
open scoped NNReal

variable {α : Type*} [MetricSpace α] {f : α → α} {x₀ : α} {K : ℝ≥0} {δ r : ℝ}

theorem delta_nonneg (hres : dist (f x₀) x₀ ≤ δ) : 0 ≤ δ :=
  dist_nonneg.trans hres

theorem radius_nonneg (hK : K < 1) (hres : dist (f x₀) x₀ ≤ δ)
    (hrad : δ + K * r ≤ r) : 0 ≤ r := by
  have hδ0 : (0 : ℝ) ≤ δ := delta_nonneg hres
  have h1K : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  nlinarith

theorem mapsTo_closedBall (hK : K < 1)
    (hlip : LipschitzOnWith K f (closedBall x₀ r))
    (hres : dist (f x₀) x₀ ≤ δ) (hrad : δ + K * r ≤ r) :
    Set.MapsTo f (closedBall x₀ r) (closedBall x₀ r) := by
  intro x hx
  have hr0 : 0 ≤ r := radius_nonneg hK hres hrad
  have hx₀ : x₀ ∈ closedBall x₀ r := mem_closedBall_self hr0
  have hxr : dist x x₀ ≤ r := mem_closedBall.mp hx
  have hstep : dist (f x) (f x₀) ≤ K * dist x x₀ := hlip.dist_le_mul x hx x₀ hx₀
  have hKd : (K : ℝ) * dist x x₀ ≤ K * r :=
    mul_le_mul_of_nonneg_left hxr K.coe_nonneg
  have := dist_triangle (f x) (f x₀) x₀
  exact mem_closedBall.mpr (by linarith)

theorem dist_fixedPoint_le (hK : K < 1)
    (hlip : LipschitzOnWith K f (closedBall x₀ r))
    (hres : dist (f x₀) x₀ ≤ δ) (hrad : δ + K * r ≤ r)
    {y : α} (hy : y ∈ closedBall x₀ r) (hfy : IsFixedPt f y) :
    dist x₀ y ≤ δ / (1 - K) := by
  have hr0 : 0 ≤ r := radius_nonneg hK hres hrad
  have h1K : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  have hx₀ : x₀ ∈ closedBall x₀ r := mem_closedBall_self hr0
  have hstep : dist (f x₀) (f y) ≤ K * dist x₀ y := hlip.dist_le_mul x₀ hx₀ y hy
  have htri : dist x₀ y ≤ dist x₀ (f x₀) + dist (f x₀) y := dist_triangle _ _ _
  rw [le_div_iff₀ h1K]
  have h₁ : dist x₀ (f x₀) ≤ δ := by rwa [dist_comm]
  have h₂ : dist (f x₀) y = dist (f x₀) (f y) := by rw [hfy.eq]
  nlinarith [dist_nonneg (x := x₀) (y := y)]

theorem fixedPoint_unique (hK : K < 1)
    (hlip : LipschitzOnWith K f (closedBall x₀ r))
    {y z : α} (hy : y ∈ closedBall x₀ r) (hz : z ∈ closedBall x₀ r)
    (hfy : IsFixedPt f y) (hfz : IsFixedPt f z) : y = z := by
  have hstep : dist (f y) (f z) ≤ K * dist y z := hlip.dist_le_mul y hy z hz
  rw [hfy.eq, hfz.eq] at hstep
  have h1K : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  have h0 : dist y z ≤ 0 := by nlinarith
  exact eq_of_dist_eq_zero (le_antisymm h0 dist_nonneg)

theorem sound_QFixBall [CompleteSpace α] (hK : K < 1)
    (hlip : LipschitzOnWith K f (closedBall x₀ r))
    (hres : dist (f x₀) x₀ ≤ δ) (hrad : δ + K * r ≤ r) :
    ∃! y, y ∈ closedBall x₀ r ∧ IsFixedPt f y := by
  have hr0 : 0 ≤ r := radius_nonneg hK hres hrad
  have hmaps := mapsTo_closedBall hK hlip hres hrad
  have hsc : IsComplete (closedBall x₀ r) := isClosed_closedBall.isComplete
  have hrf : ContractingWith K (hmaps.restrict f _ _) :=
    ⟨hK, (hmaps.lipschitzOnWith_iff_restrict).mp hlip⟩
  obtain ⟨y, hys, hfy, -, -⟩ :=
    hrf.exists_fixedPoint' hsc hmaps (mem_closedBall_self hr0)
      (edist_ne_top x₀ (f x₀))
  exact ⟨y, ⟨hys, hfy⟩, fun z ⟨hzs, hfz⟩ =>
    fixedPoint_unique hK hlip hzs hys hfz hfy⟩

theorem anchored_le_radius (hK : K < 1)
    (hrad : δ + K * r ≤ r) : δ / (1 - K) ≤ r := by
  have h1K : (0 : ℝ) < 1 - K := by
    have : (K : ℝ) < 1 := by exact_mod_cast hK
    linarith
  rw [div_le_iff₀ h1K]
  nlinarith

section Affine

theorem lipschitzWith_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : E →L[ℝ] E) (c : E) (hA : ‖A‖₊ ≤ K) :
    LipschitzWith K fun x => A x + c :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_add_right]
    exact (A.lipschitz.weaken hA).dist_le_mul x y

theorem sound_QFixBall_affine {M : ℕ}
    (A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M))
    (c x₀ : EuclideanSpace ℝ (Fin M)) {K : ℝ≥0} {δ r : ℝ}
    (hK : K < 1) (hA : ‖A‖₊ ≤ K)
    (hres : dist (A x₀ + c) x₀ ≤ δ) (hrad : δ + K * r ≤ r) :
    ∃! y, y ∈ closedBall x₀ r ∧ IsFixedPt (fun x => A x + c) y :=
  sound_QFixBall hK ((lipschitzWith_affine A c hA).lipschitzOnWith) hres hrad

end Affine

end QFixBall

end Qtsl

