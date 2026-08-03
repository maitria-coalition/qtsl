import SuFunctor.Universe.CredalPoset.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Prevision bodies are exactly the homogeneous ultracontributions

This module proves the one genuinely analytic identification of the
credal-body poset: on a finite outcome space, the class of
prevision-shaped bodies (`IsPrevisionBody` — sets cut out by families of
one-sided constraints `∑ v, x v * h v ≤ 1` with nonnegative gambles `h`,
the finite-stratum face of Goubault-Larrecq's superlinear-prevision
hyperspace `𝒞P^{≤1}_super`) coincides with the class of Kosoy–Appel
homogeneous ultracontributions (`IsUltra` — nonempty, closed, convex,
pointwise-down-closed sets of subprobability states).

* `IsPrevisionBody.isUltra` — constraint bookkeeping: an intersection of
  closed half-spaces with nonnegative normals is nonempty (the zero
  state satisfies every constraint), closed, convex, and
  pointwise-down-closed.
* `IsUltra.isPrevisionBody` — the separation direction: a point outside
  the body is strictly separated from its (compact, convex) coercion
  image by a continuous linear functional (geometric Hahn–Banach); the
  functional's coefficients are then replaced by their positive parts
  via the *down-closure mask trick* — zeroing the coordinates with
  nonpositive coefficient maps any member to a smaller member (by
  pointwise-down closure), so the positive-part pairing still lies
  strictly below the separating gap on the body while strictly above it
  at the excluded point — and normalized by the gap, which is positive
  because the body owns the zero state.
* `isPrevisionBody_iff_isUltra` — the identification, stated as the
  poset expects it.
* `IsPrevisionBody.isConvexCredalBody` — hence prevision bodies sit
  inside the convex credal bodies.
-/

namespace SuFunctor.Universe

namespace CredalPoset

variable {V : Type*} [Fintype V]

/-- **Constraint bookkeeping direction**: a body cut out by one-sided
constraints `∑ v, x v * h v ≤ 1` with nonnegative gambles `h` is a
homogeneous ultracontribution.  Nonemptiness is witnessed by the zero
state; closedness is an intersection of continuous sublevels; convexity
and pointwise-down closure hold constraint by constraint, by linearity
and by nonnegativity of the gambles respectively. -/
theorem IsPrevisionBody.isUltra {S : Set (BelState V)}
    (hP : IsPrevisionBody S) : IsUltra S := by
  obtain ⟨H, hH, rfl⟩ := hP
  refine ⟨⟨BelState.zero V, fun h _ => by simp⟩, ?_, ?_, ?_⟩
  · -- closed: an intersection of closed sublevels of continuous maps
    have hrw : {x : BelState V | ∀ h ∈ H, ∑ v, (x : V → ℝ) v * h v ≤ 1}
        = ⋂ h ∈ H, {x : BelState V | ∑ v, (x : V → ℝ) v * h v ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    refine isClosed_biInter fun h _ => isClosed_le ?_ continuous_const
    exact continuous_finsetSum _ fun v _ =>
      ((continuous_apply v).comp continuous_subtype_val).mul continuous_const
  · -- convex: each constraint is linear in the state
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ s t hs ht hst
    have hmem : s • (y : V → ℝ) + t • (z : V → ℝ) ∈ belCarrier V :=
      convex_belCarrier y.2 z.2 hs ht hst
    refine ⟨⟨_, hmem⟩, fun h hh => ?_, rfl⟩
    show ∑ v, (s • (y : V → ℝ) + t • (z : V → ℝ)) v * h v ≤ 1
    calc ∑ v, (s • (y : V → ℝ) + t • (z : V → ℝ)) v * h v
        = s * ∑ v, (y : V → ℝ) v * h v + t * ∑ v, (z : V → ℝ) v * h v := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      _ ≤ s * 1 + t * 1 := by
          gcongr
          · exact hy h hh
          · exact hz h hh
      _ = 1 := by rw [mul_one, mul_one, hst]
  · -- pointwise-down: the gambles are nonnegative
    intro y hy x hxy h hh
    calc ∑ v, (x : V → ℝ) v * h v
        ≤ ∑ v, (y : V → ℝ) v * h v :=
          Finset.sum_le_sum fun v _ =>
            mul_le_mul_of_nonneg_right (hxy v) (hH h hh v)
      _ ≤ 1 := hy h hh

/-- **Separation direction**: a homogeneous ultracontribution is cut out
by its own family of valid one-sided constraints — the set of *all*
nonnegative gambles whose prevision constraint the body satisfies.  A
point outside the body is strictly separated from the body's compact
convex coercion image by geometric Hahn–Banach; the separating
functional is positivized by the down-closure mask trick (zeroing the
coordinates with nonpositive coefficient sends members to members, by
pointwise-down closure) and normalized by the separation gap, which is
positive because the zero state belongs to every nonempty
pointwise-down-closed set.  The resulting gamble is a valid constraint
that the outside point violates. -/
theorem IsUltra.isPrevisionBody {S : Set (BelState V)}
    (hS : IsUltra S) : IsPrevisionBody S := by
  classical
  obtain ⟨hne, hcl, hcv, hdn⟩ := hS
  refine ⟨{h : V → ℝ | (∀ v, 0 ≤ h v)
      ∧ ∀ y ∈ S, ∑ v, (y : V → ℝ) v * h v ≤ 1},
    fun h hh => hh.1, ?_⟩
  refine Set.Subset.antisymm (fun x hx h hh => hh.2 x hx) ?_
  intro x hx
  by_contra hxS
  -- the coercion image is a compact convex closed set omitting `↑x`
  have hAconv : Convex ℝ (carrierImage S) := hcv
  have hAcl : IsClosed (carrierImage S) :=
    (hcl.isCompact.image continuous_subtype_val).isClosed
  have hxA : (x : V → ℝ) ∉ carrierImage S := by
    rintro ⟨y, hyS, hyx⟩
    exact hxS (Subtype.coe_injective hyx ▸ hyS)
  obtain ⟨φ, u, hφA, hφx⟩ := geometric_hahn_banach_closed_point hAconv hAcl hxA
  -- the separation level is positive: the body owns the zero state
  have hu : (0 : ℝ) < u := by
    have h0 : (0 : V → ℝ) ∈ carrierImage S :=
      ⟨BelState.zero V, zero_mem_of_isRadial hne hdn.isRadial, rfl⟩
    simpa using hφA 0 h0
  -- coordinate representation of the separating functional
  have hrep : ∀ y : V → ℝ, φ y = ∑ v, y v * φ (Pi.single v 1) := by
    intro y
    conv_lhs => rw [pi_eq_sum_univ' y]
    simp only [map_sum, map_smul, smul_eq_mul]
  -- the positive-part pairing is φ evaluated at the masked vector
  have hmask_eq : ∀ y : V → ℝ,
      ∑ v, y v * max (φ (Pi.single v 1)) 0
        = φ fun v => if 0 < φ (Pi.single v 1) then y v else 0 := by
    intro y
    rw [hrep fun v => if 0 < φ (Pi.single v 1) then y v else 0]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : 0 < φ (Pi.single v 1)
    · rw [if_pos hv, max_eq_left hv.le]
    · rw [if_neg hv, zero_mul, max_eq_right (not_lt.mp hv), mul_zero]
  -- the mask trick: masking a member yields a member
  have hmaskA : ∀ y ∈ carrierImage S,
      (fun v => if 0 < φ (Pi.single v 1) then y v else 0)
        ∈ carrierImage S := by
    rintro _ ⟨z, hzS, rfl⟩
    have hmem : (fun v => if 0 < φ (Pi.single v 1) then (z : V → ℝ) v else 0)
        ∈ belCarrier V := by
      have hle : ∀ v, (if 0 < φ (Pi.single v 1) then (z : V → ℝ) v else 0)
          ≤ (z : V → ℝ) v := fun v => by
        by_cases hv : 0 < φ (Pi.single v 1)
        · rw [if_pos hv]
        · rw [if_neg hv]; exact z.nonneg v
      refine ⟨fun v => ?_, (Finset.sum_le_sum fun v _ => hle v).trans z.2.2⟩
      show (0 : ℝ) ≤ if 0 < φ (Pi.single v 1) then (z : V → ℝ) v else 0
      by_cases hv : 0 < φ (Pi.single v 1)
      · rw [if_pos hv]; exact z.nonneg v
      · rw [if_neg hv]
    have hlemask : ((⟨_, hmem⟩ : BelState V) : V → ℝ) ≤ (z : V → ℝ) := by
      refine Pi.le_def.mpr fun v => ?_
      show (if 0 < φ (Pi.single v 1) then (z : V → ℝ) v else 0) ≤ (z : V → ℝ) v
      by_cases hv : 0 < φ (Pi.single v 1)
      · rw [if_pos hv]
      · rw [if_neg hv]; exact z.nonneg v
    exact mem_carrierImage (hdn z hzS ⟨_, hmem⟩ hlemask)
  -- on the body, the positive-part pairing stays strictly below the gap
  have hbound : ∀ y ∈ carrierImage S,
      ∑ v, y v * max (φ (Pi.single v 1)) 0 < u := by
    intro y hy
    rw [hmask_eq y]
    exact hφA _ (hmaskA y hy)
  -- at the excluded point it lies strictly above
  have hxgt : u < ∑ v, (x : V → ℝ) v * max (φ (Pi.single v 1)) 0 := by
    refine hφx.trans_le ?_
    rw [hrep]
    exact Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (x.nonneg v)
  -- normalize by the gap and read off the violated constraint
  have hdiv : ∀ y : V → ℝ,
      ∑ v, y v * (max (φ (Pi.single v 1)) 0 / u)
        = (∑ v, y v * max (φ (Pi.single v 1)) 0) / u := by
    intro y
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => (mul_div_assoc _ _ _).symm
  have hmem : (fun v => max (φ (Pi.single v 1)) 0 / u)
      ∈ {h : V → ℝ | (∀ v, 0 ≤ h v)
        ∧ ∀ y ∈ S, ∑ v, (y : V → ℝ) v * h v ≤ 1} := by
    refine ⟨fun v => div_nonneg (le_max_right _ _) hu.le, fun y hyS => ?_⟩
    show ∑ v, (y : V → ℝ) v * (max (φ (Pi.single v 1)) 0 / u) ≤ 1
    rw [hdiv, div_le_one hu]
    exact (hbound _ (mem_carrierImage hyS)).le
  have hle : ∑ v, (x : V → ℝ) v * (max (φ (Pi.single v 1)) 0 / u) ≤ 1 :=
    hx _ hmem
  rw [hdiv, div_le_one hu] at hle
  exact absurd hle (not_le.mpr hxgt)

/-- **Prevision bodies are exactly the homogeneous ultracontributions**
(the finite-stratum identification).  A set of subprobability states is
cut out by a family of one-sided constraints `∑ v, x v * h v ≤ 1` with
nonnegative gambles `h` — the shape of Goubault-Larrecq's hyperspace
`𝒞P^{≤1}_super` of sublinear/superlinear prevision objects
(arXiv 2605.10173, the `HDia` hyperspace definition; on a finite outcome
space every gamble is continuous, so the lower-semicontinuity rider is
vacuous) — if and only if it is a Kosoy–Appel homogeneous
ultracontribution: nonempty, topologically closed, convex, and
pointwise-down-closed.  The two literatures name one class; the poset
carries it as a single node. -/
theorem isPrevisionBody_iff_isUltra {S : Set (BelState V)} :
    IsPrevisionBody S ↔ IsUltra S :=
  ⟨IsPrevisionBody.isUltra, IsUltra.isPrevisionBody⟩

/-- Prevision bodies are convex credal bodies: the identification with
the ultracontributions composed with `IsUltra.isConvexCredalBody`.  In
particular the prevision shape enters the house poset strictly inside
the convex subclass, sharing its node with the ultracontributions. -/
theorem IsPrevisionBody.isConvexCredalBody {S : Set (BelState V)}
    (h : IsPrevisionBody S) : IsConvexCredalBody S :=
  h.isUltra.isConvexCredalBody

end CredalPoset

end SuFunctor.Universe
