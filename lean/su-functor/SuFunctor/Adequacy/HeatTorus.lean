import SuFunctor.Adequacy.DelayLine
import SuFunctor.Adequacy.MarginalGlue
import SuFunctor.Universe.ParabolicOrder
import Mathlib.Algebra.Ring.Periodic

/-! # Adequacy: heat on the torus — the cyclic spatial mesh

The first instance where the cover tier genuinely bites: the heat
equation `∂ₜu = D·∂ₓₓu` on the circle `𝕋¹ = ℝ/L`, discretized as a
**cyclic spatial mesh** — three overlapping arcs whose intersection
pattern is the Vorob'ev ring (`SuFunctor.Adequacy.MarginalGlue`).  The
delay line (`SuFunctor.Adequacy.DelayLine`) was a single spatial cell
plus wires; here the record is a *family* of cell fields, the walls are
seam constraints on open overlap collars, and one wall — the
ring-closing wall at `L ≡ 0`, which composes with the periodic
identification — carries the mesh's **holonomy obligation**: the global
consistency demand that per-cell and pairwise-chain checks do not
discharge.

Everything is presented on the universal chart: fields
`u : ℝ → ℝ → E`, `L`-periodicity in `x` as the descended-record row.
The three arcs are `I₁ = (−δ, a+δ)`, `I₂ = (a−δ, b+δ)`,
`I₃ = (b−δ, L+δ)` with `0 < a < b < L` and `0 < δ < L`; seams at `a`,
`b` (chain collars) and at `L ≡ 0` (the wrap collar `I₃ ∩ (I₁ + L)`,
wall `c₃ x = c₁ (x − L)`).

Design notes, load-bearing:

* **Locality is the engine.**  The heat rows (`HeatAt`) are pointwise
  and germ-determined: agreement on an open rectangle transports them
  (`HeatAt.congr`).  This is the instance-level form of "differential
  operators are local", and it is the entire mechanism by which the
  mesh glues: pasted fields are locally equal to cell fields, so
  solution-hood transfers point by point.  No parabolic theory — no
  semigroup, no maximum principle, no regularity theorem — appears
  anywhere in the module.
* **Why heat glues where the frustrated ring does not.**  The Vorob'ev
  obstruction (`vorobev_no_joint`) lives at the measure tier: marginal
  constraints are not local predicates on records, and pairwise
  consistency of laws carries no global witness.  The heat mesh's
  constraints are record-tier and local, so wall-compatible families
  glue (`heat_mesh_glues` — the con-obligation discharge), and the
  compiled conjunction is satisfiable (`heatAtoms_consistent`,
  constants as equilibria).  The contrast is stated as one theorem
  (`heat_ring_glues_vorobev_ring_not`) and at the credal stratum
  (`credalCompile_heatAtoms_ne_bot` against
  `credalCompile_vorobevGlue`): the heat ring's lawful denotation is
  not the bottom object; the frustrated ring's is exactly bottom.
* **The ring's con obligation is a holonomy wall, visible and
  refusable.**  The cyclic cover adds exactly one constraint beyond
  the chain: the wrap wall.  It is genuinely load-bearing — the linear
  field `x ↦ x • e` satisfies every cell row and both chain walls and
  refuses the wrap wall (`not_wrap_lin`), and no global periodic field
  restricts to it (`no_periodic_glue_lin`): the non-descending family
  is *detected by a wall*, where the frustrated ring's failure is an
  invisible missing joint.  Cutting the ring to an interval removes
  the obligation: the chain glues from chain walls alone
  (`heat_chain_glues` — decomposable covers are Vorob'ev-free).
* **The record-tier square is two-sided.**  At the pointwise-record
  stratum the paste closes the converse, so the adequacy square is an
  invertible cell (`heat_adequacy`), the delay-line pattern one
  instance wider.  What is one-sided about PDE squares lives at the
  *finite/certificate* stratum (finite row families are implied by
  solution-hood and do not pin it — the mesh-refinement limit is where
  the iff returns) and at the *enclosure* stratum: heat transients
  `e^{−λt}` are transcendental at rational times (Lindemann), so
  exact-ℚ time-evolution rows are outward-rounded sandwiches, never
  equalities — the delay line's exact two-sided dynamics has no heat
  analogue except the conserved zero mode.  Neither stratum is
  mechanized here; the two preceding caveats state that gap
  explicitly.
* **`D`'s sign appears nowhere.**  No statement below consumes
  `0 < D`: the record-stratum square is satisfied by backward heat
  (`D < 0`) verbatim.  Well-posedness direction is wiring-tier
  content (the dependence-boundary judgment of the spacetime-sites
  design), not a satisfaction clause — the (T1) fence, corroborated
  by an instance that never needed to consult it.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Set Topology Filter

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The heat rows, pointwise -/

/-- The heat rows at a single spacetime point: joint continuity of the
field, spatial differentiability twice (in canonical-value form, so
that junk-value satisfaction is excluded), and the heat equation
`∂ₜu = D • ∂ₓₓu` with the time derivative a genuine derivative and the
spatial second derivative the canonical `deriv (deriv ·)`.  Pointwise
and germ-determined (`HeatAt.congr`) — the constraint-row form of a
second-order differential operator, mentioning only the field's values
near the point. -/
structure HeatAt (D : ℝ) (u : ℝ → ℝ → E) (x t : ℝ) : Prop where
  /-- Joint continuity of the field at the point (record-class row). -/
  cont : ContinuousAt (fun q : ℝ × ℝ => u q.1 q.2) (x, t)
  /-- Spatial differentiability. -/
  diff : DifferentiableAt ℝ (fun y => u y t) x
  /-- Spatial differentiability of the spatial derivative. -/
  diff2 : DifferentiableAt ℝ (deriv fun y => u y t) x
  /-- The heat equation. -/
  heat : HasDerivAt (fun s => u x s) (D • deriv (deriv fun y => u y t) x) t

/-- A field solves the heat equation on a cell `S × T`: the rows hold
at every point of the cell.  (Records live over domains; a total
function chart's off-cell values are not observables, exactly as in
the delay line's `RecMatches` convention.) -/
def IsHeatSol (D : ℝ) (S T : Set ℝ) (u : ℝ → ℝ → E) : Prop :=
  ∀ x ∈ S, ∀ t ∈ T, HeatAt D u x t

/-! ## Locality: the rows are germ-determined -/

/-- **Locality of the heat rows.**  Agreement on an open rectangle
transports the rows: differential operators are local, so a field that
locally coincides with a solution is a solution at that point.  This
is the whole engine of mesh gluing. -/
theorem HeatAt.congr {D : ℝ} {u v : ℝ → ℝ → E} {x t : ℝ}
    {Sx St : Set ℝ} (hSx : IsOpen Sx) (hSt : IsOpen St)
    (hx : x ∈ Sx) (ht : t ∈ St)
    (hagree : ∀ y ∈ Sx, ∀ s ∈ St, u y s = v y s)
    (h : HeatAt D v x t) : HeatAt D u x t := by
  have hSxmem : Sx ∈ 𝓝 x := hSx.mem_nhds hx
  have hStmem : St ∈ 𝓝 t := hSt.mem_nhds ht
  have ev_x : (fun y => u y t) =ᶠ[𝓝 x] fun y => v y t :=
    Filter.eventually_of_mem hSxmem fun y hy => hagree y hy t ht
  have ev_dx : (deriv fun y => u y t) =ᶠ[𝓝 x] deriv fun y => v y t := by
    refine Filter.eventually_of_mem hSxmem fun y hy => ?_
    have hev : (fun z => u z t) =ᶠ[𝓝 y] fun z => v z t :=
      Filter.eventually_of_mem (hSx.mem_nhds hy) fun z hz => hagree z hz t ht
    exact hev.deriv_eq
  have ev_t : (fun s => u x s) =ᶠ[𝓝 t] fun s => v x s :=
    Filter.eventually_of_mem hStmem fun s hs => hagree x hx s hs
  refine ⟨?_, ev_x.differentiableAt_iff.mpr h.diff,
    ev_dx.differentiableAt_iff.mpr h.diff2, ?_⟩
  · have hne : Sx ×ˢ St ∈ 𝓝 (x, t) := (hSx.prod hSt).mem_nhds ⟨hx, ht⟩
    have hev : (fun q : ℝ × ℝ => u q.1 q.2) =ᶠ[𝓝 (x, t)] fun q => v q.1 q.2 :=
      Filter.eventually_of_mem hne fun q hq => hagree q.1 hq.1 q.2 hq.2
    have h2 : Filter.Tendsto (fun q : ℝ × ℝ => u q.1 q.2) (𝓝 (x, t))
        (𝓝 (v x t)) :=
      Filter.Tendsto.congr' hev.symm h.cont
    have h3 : v x t = u x t := (hagree x hx t ht).symm
    rw [h3] at h2
    exact h2
  · have hval : deriv (deriv fun y => u y t) x
        = deriv (deriv fun y => v y t) x := ev_dx.deriv_eq
    have h2 := h.heat.congr_of_eventuallyEq ev_t
    rwa [← hval] at h2

/-! ## Translation invariance -/

/-- Differentiability composes with translation, both ways. -/
theorem differentiableAt_sub_const_iff (f : ℝ → E) {y : ℝ} (c : ℝ) :
    DifferentiableAt ℝ (fun z => f (z - c)) y ↔ DifferentiableAt ℝ f (y - c) := by
  constructor
  · intro h
    have hinner : DifferentiableAt ℝ (fun z : ℝ => z + c) (y - c) :=
      differentiableAt_id.add_const c
    have hy : y - c + c = y := by ring
    rw [← hy] at h
    have h1 : DifferentiableAt ℝ
        ((fun z => f (z - c)) ∘ fun z : ℝ => z + c) (y - c) :=
      DifferentiableAt.comp (y - c) h hinner
    have hcomp : ((fun z => f (z - c)) ∘ fun z : ℝ => z + c) = f := by
      funext z
      show f (z + c - c) = f z
      congr 1
      ring
    rwa [hcomp] at h1
  · intro h
    have hinner : DifferentiableAt ℝ (fun z : ℝ => z - c) y :=
      differentiableAt_id.sub_const c
    have h1 : DifferentiableAt ℝ (f ∘ fun z : ℝ => z - c) y :=
      DifferentiableAt.comp y h hinner
    exact h1

/-- The derivative of a translate is the translated derivative —
uniformly, junk values included (translation is an equivalence, so
non-differentiability transfers too). -/
theorem deriv_sub_const' (f : ℝ → E) (y c : ℝ) :
    deriv (fun z => f (z - c)) y = deriv f (y - c) := by
  by_cases h : DifferentiableAt ℝ f (y - c)
  · have h1 : HasDerivAt (fun z => f (z - c)) (deriv f (y - c)) y := by
      have h2 := HasDerivAt.scomp (𝕜 := ℝ) y h.hasDerivAt
        ((hasDerivAt_id y).sub_const c)
      simpa [Function.comp_def] using h2
    exact h1.deriv
  · have h2 : ¬ DifferentiableAt ℝ (fun z => f (z - c)) y :=
      fun hc => h ((differentiableAt_sub_const_iff f c).mp hc)
    rw [deriv_zero_of_not_differentiableAt h2,
      deriv_zero_of_not_differentiableAt h]

/-- The heat rows are translation-invariant: a translated field
satisfies the rows at the translated point. -/
theorem HeatAt.comp_sub_const {D : ℝ} {w : ℝ → ℝ → E} {x t c : ℝ}
    (h : HeatAt D w (x - c) t) : HeatAt D (fun y s => w (y - c) s) x t := by
  have hev : (deriv fun y => w (y - c) t)
      = fun y => deriv (fun z => w z t) (y - c) :=
    funext fun y => deriv_sub_const' (fun z => w z t) y c
  refine ⟨?_, (differentiableAt_sub_const_iff _ c).mpr h.diff, ?_, ?_⟩
  · have h1 : ContinuousAt (fun q : ℝ × ℝ => (q.1 - c, q.2)) (x, t) := by
      fun_prop
    have h2 : ContinuousAt
        ((fun q : ℝ × ℝ => w q.1 q.2) ∘ fun q : ℝ × ℝ => (q.1 - c, q.2))
        (x, t) :=
      ContinuousAt.comp h.cont h1
    exact h2
  · rw [hev]
    exact (differentiableAt_sub_const_iff _ c).mpr h.diff2
  · show HasDerivAt (fun s => w (x - c) s)
      (D • deriv (deriv fun y => w (y - c) t) x) t
    rw [hev, deriv_sub_const' (deriv fun z => w z t) x c]
    exact h.heat

/-! ## The ring mesh -/

/-- The canonical cyclic three-arc mesh of the circle `ℝ/L`, on the
universal chart: breakpoints `0 < a < b < L`, collar half-width
`0 < δ < L`.  Three arcs, three seams — at `a`, at `b`, and at
`L ≡ 0` (the ring-closing seam, whose wall composes with the periodic
identification).  The minimal cover whose intersection pattern is the
Vorob'ev ring. -/
structure RingMesh where
  /-- The circumference. -/
  L : ℝ
  /-- First breakpoint. -/
  a : ℝ
  /-- Second breakpoint. -/
  b : ℝ
  /-- Collar half-width. -/
  δ : ℝ
  hδ : 0 < δ
  ha : 0 < a
  hab : a < b
  hbL : b < L
  hδL : δ < L

namespace RingMesh

/-- The first arc, around the chart origin side. -/
def I1 (M : RingMesh) : Set ℝ := Ioo (-M.δ) (M.a + M.δ)

/-- The middle arc. -/
def I2 (M : RingMesh) : Set ℝ := Ioo (M.a - M.δ) (M.b + M.δ)

/-- The closing arc, crossing `L ≡ 0`. -/
def I3 (M : RingMesh) : Set ℝ := Ioo (M.b - M.δ) (M.L + M.δ)

/-- The chart interval covering one full period with collars. -/
def chart (M : RingMesh) : Set ℝ := Ioo (-M.δ) (M.L + M.δ)

theorem hL0 (M : RingMesh) : 0 < M.L :=
  M.ha.trans (M.hab.trans M.hbL)

theorem haL (M : RingMesh) : M.a < M.L := M.hab.trans M.hbL

theorem I1_subset_chart (M : RingMesh) : M.I1 ⊆ M.chart := fun x hx =>
  ⟨hx.1, hx.2.trans (by have := M.haL; linarith)⟩

theorem I2_subset_chart (M : RingMesh) : M.I2 ⊆ M.chart := fun x hx =>
  ⟨lt_of_lt_of_le (by have := M.ha; have := M.hδ; linarith) hx.1.le,
    hx.2.trans_le (by have := M.hbL; linarith)⟩

theorem I3_subset_chart (M : RingMesh) : M.I3 ⊆ M.chart := fun x hx =>
  ⟨lt_of_lt_of_le (by have := M.ha; have := M.hab; have := M.hδ; linarith)
    hx.1.le, hx.2⟩

theorem isOpen_I1 (M : RingMesh) : IsOpen M.I1 := isOpen_Ioo
theorem isOpen_I2 (M : RingMesh) : IsOpen M.I2 := isOpen_Ioo
theorem isOpen_I3 (M : RingMesh) : IsOpen M.I3 := isOpen_Ioo

end RingMesh

/-- A concrete instance: `L = 3`, breakpoints `1, 2`, collars `1/4`.
The structure is inhabited; every parametric theorem below has a
concrete face. -/
noncomputable def ringMesh₃ : RingMesh where
  L := 3
  a := 1
  b := 2
  δ := 1/4
  hδ := by norm_num
  ha := by norm_num
  hab := by norm_num
  hbL := by norm_num
  hδL := by norm_num

/-! ## Walls -/

/-- The ring-closing wall: on the wrap collar `I₃ ∩ (I₁ + L)`, the
closing arc's field agrees with the first arc's field *one period
back*.  The only wall that mentions the periodic identification — the
mesh's holonomy constraint. -/
def WrapWall (M : RingMesh) (T : Set ℝ) (v1 v3 : ℝ → ℝ → E) : Prop :=
  ∀ x, x ∈ M.I3 → x - M.L ∈ M.I1 → ∀ t ∈ T, v3 x t = v1 (x - M.L) t

/-! ## The chain paste -/

/-- The pasted field of the three cell fields: a piecewise read on the
chart, breaking at `a` and `b`. -/
noncomputable def paste (M : RingMesh) (c1 c2 c3 : ℝ → ℝ → E) :
    ℝ → ℝ → E :=
  fun y => if y < M.a then c1 y else if y < M.b then c2 y else c3 y

theorem paste_of_lt_a {M : RingMesh} {c1 c2 c3 : ℝ → ℝ → E} {y : ℝ}
    (h : y < M.a) (t : ℝ) : paste M c1 c2 c3 y t = c1 y t := by
  simp [paste, h]

theorem paste_of_ge_a_lt_b {M : RingMesh} {c1 c2 c3 : ℝ → ℝ → E} {y : ℝ}
    (h1 : ¬ y < M.a) (h2 : y < M.b) (t : ℝ) :
    paste M c1 c2 c3 y t = c2 y t := by
  simp [paste, h1, h2]

theorem paste_of_ge_b {M : RingMesh} {c1 c2 c3 : ℝ → ℝ → E} {y : ℝ}
    (h2 : ¬ y < M.b) (t : ℝ) : paste M c1 c2 c3 y t = c3 y t := by
  have h1 : ¬ y < M.a := fun h => h2 (h.trans M.hab)
  simp [paste, h1, h2]

section Paste

variable {M : RingMesh} {D : ℝ} {T : Set ℝ} {c1 c2 c3 : ℝ → ℝ → E}

/-- The pasted field restricts to the first cell field on its whole
arc (through the chain walls where the piecewise read differs). -/
theorem paste_eqOn_c1
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    ∀ x ∈ M.I1, ∀ t ∈ T, paste M c1 c2 c3 x t = c1 x t := by
  intro x hx t ht
  obtain ⟨hx1, hx2⟩ := hx
  by_cases h1 : x < M.a
  · exact paste_of_lt_a h1 t
  · by_cases h2 : x < M.b
    · rw [paste_of_ge_a_lt_b h1 h2 t]
      refine (hs12 x ⟨⟨hx1, hx2⟩, ⟨?_, ?_⟩⟩ t ht).symm
      · have := M.hδ; linarith [not_lt.mp h1]
      · have := M.hδ; linarith
    · rw [paste_of_ge_b h2 t]
      have hxb : M.b ≤ x := not_lt.mp h2
      have hxI2 : x ∈ M.I2 := by
        constructor
        · have := M.hδ; have := M.ha; have := M.hab; linarith
        · have := M.hδ; have := M.hab; linarith
      have hxI3 : x ∈ M.I3 := by
        constructor
        · have := M.hδ; linarith
        · have := M.hδ; have := M.hab; have := M.hbL; linarith
      rw [← hs23 x ⟨hxI2, hxI3⟩ t ht, ← hs12 x ⟨⟨hx1, hx2⟩, hxI2⟩ t ht]

/-- The pasted field restricts to the middle cell field. -/
theorem paste_eqOn_c2
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    ∀ x ∈ M.I2, ∀ t ∈ T, paste M c1 c2 c3 x t = c2 x t := by
  intro x hx t ht
  obtain ⟨hx1, hx2⟩ := hx
  by_cases h1 : x < M.a
  · rw [paste_of_lt_a h1 t]
    refine hs12 x ⟨⟨?_, ?_⟩, ⟨hx1, hx2⟩⟩ t ht
    · have := M.hδ; have := M.ha; linarith
    · have := M.hδ; linarith
  · by_cases h2 : x < M.b
    · exact paste_of_ge_a_lt_b h1 h2 t
    · rw [paste_of_ge_b h2 t]
      refine (hs23 x ⟨⟨hx1, hx2⟩, ⟨?_, ?_⟩⟩ t ht).symm
      · have := M.hδ; linarith [not_lt.mp h2]
      · have := M.hδ; have := M.hbL; linarith
        
/-- The pasted field restricts to the closing cell field. -/
theorem paste_eqOn_c3
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    ∀ x ∈ M.I3, ∀ t ∈ T, paste M c1 c2 c3 x t = c3 x t := by
  intro x hx t ht
  obtain ⟨hx1, hx2⟩ := hx
  by_cases h2 : x < M.b
  · have hxI2 : x ∈ M.I2 := by
      constructor
      · have := M.hδ; have := M.hab; linarith
      · have := M.hδ; linarith
    by_cases h1 : x < M.a
    · rw [paste_of_lt_a h1 t]
      have hxI1 : x ∈ M.I1 := by
        constructor
        · have := M.hδ; have := M.ha; have := M.hab; linarith
        · have := M.hδ; linarith
      rw [hs12 x ⟨hxI1, hxI2⟩ t ht, hs23 x ⟨hxI2, ⟨hx1, hx2⟩⟩ t ht]
    · rw [paste_of_ge_a_lt_b h1 h2 t]
      exact hs23 x ⟨hxI2, ⟨hx1, hx2⟩⟩ t ht
  · exact paste_of_ge_b h2 t

/-- **The chain paste solves on the chart** — and, with it,
`heat_chain_glues`: the decomposable (interval) sub-mesh glues from
the chain walls alone, no global consistency datum consumed.  This is
the m2 mutant's positive control: cutting the ring trivializes the con
obligation. -/
theorem paste_isHeatSol (hT : IsOpen T)
    (h1 : IsHeatSol D M.I1 T c1) (h2 : IsHeatSol D M.I2 T c2)
    (h3 : IsHeatSol D M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    IsHeatSol D M.chart T (paste M c1 c2 c3) := by
  have hδ' := M.hδ
  have ha' := M.ha
  have hab' := M.hab
  have hbL' := M.hbL
  intro x hx t ht
  obtain ⟨hxl, hxr⟩ := hx
  rcases lt_trichotomy x M.a with hxa | hxa | hxa
  · -- left of the first seam: locally the first field
    refine HeatAt.congr (Sx := Ioo (-M.δ) M.a) isOpen_Ioo hT ⟨hxl, hxa⟩ ht
      ?_ (h1 x ⟨hxl, by linarith⟩ t ht)
    intro y hy s hs
    exact paste_of_lt_a hy.2 s
  · -- the first seam: locally the middle field, through the walls
    subst hxa
    refine HeatAt.congr (Sx := Ioo (M.a - M.δ) (M.a + M.δ)) isOpen_Ioo hT
      ⟨by linarith, by linarith⟩ ht ?_
      (h2 M.a ⟨by linarith, by linarith⟩ t ht)
    intro y hy s hs
    obtain ⟨hyl, hyr⟩ := hy
    by_cases hya : y < M.a
    · rw [paste_of_lt_a hya s]
      refine hs12 y ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩ s hs
    · by_cases hyb : y < M.b
      · exact paste_of_ge_a_lt_b hya hyb s
      · rw [paste_of_ge_b hyb s]
        refine (hs23 y ⟨⟨by linarith, by linarith⟩,
          ⟨by linarith [not_lt.mp hyb], by linarith⟩⟩ s hs).symm
  · rcases lt_trichotomy x M.b with hxb | hxb | hxb
    · -- strictly between the seams: locally the middle field
      refine HeatAt.congr (Sx := Ioo M.a M.b) isOpen_Ioo hT ⟨hxa, hxb⟩ ht
        ?_ (h2 x ⟨by linarith, by linarith⟩ t ht)
      intro y hy s hs
      exact paste_of_ge_a_lt_b (not_lt.mpr hy.1.le) hy.2 s
    · -- the second seam: locally the closing field, through the walls
      subst hxb
      refine HeatAt.congr (Sx := Ioo (M.b - M.δ) (M.b + M.δ)) isOpen_Ioo hT
        ⟨by linarith, by linarith⟩ ht ?_
        (h3 M.b ⟨by linarith, by linarith⟩ t ht)
      intro y hy s hs
      obtain ⟨hyl, hyr⟩ := hy
      by_cases hya : y < M.a
      · rw [paste_of_lt_a hya s]
        have hyI1 : y ∈ M.I1 := ⟨by linarith, by linarith⟩
        have hyI2 : y ∈ M.I2 := ⟨by linarith, by linarith⟩
        have hyI3 : y ∈ M.I3 := ⟨by linarith, by linarith⟩
        rw [hs12 y ⟨hyI1, hyI2⟩ s hs, hs23 y ⟨hyI2, hyI3⟩ s hs]
      · by_cases hyb : y < M.b
        · rw [paste_of_ge_a_lt_b hya hyb s]
          refine hs23 y ⟨⟨by linarith, by linarith⟩,
            ⟨by linarith, by linarith⟩⟩ s hs
        · exact paste_of_ge_b hyb s
    · -- right of the second seam: locally the closing field
      refine HeatAt.congr (Sx := Ioo M.b (M.L + M.δ)) isOpen_Ioo hT
        ⟨hxb, hxr⟩ ht ?_ (h3 x ⟨by linarith, hxr⟩ t ht)
      intro y hy s hs
      exact paste_of_ge_b (not_lt.mpr hy.1.le) s

end Paste

/-! ## The torus (descended) record class -/

/-- A global torus solution: `L`-periodic in space, heat rows at every
point of the time window.  The left-edge object of the square, at the
pointwise-record stratum (the delta to the literature's `C^{2,1}`
class — continuity of the derivatives — is a named bridge obligation,
`bridge:regularity@strong`; see the memo). -/
structure IsHeatTorusSol (D L : ℝ) (T : Set ℝ) (u : ℝ → ℝ → E) : Prop where
  /-- Spatial periodicity: the field descends to the circle. -/
  periodic : ∀ t, Function.Periodic (fun y => u y t) L
  /-- The heat rows, globally in space. -/
  sol : IsHeatSol D Set.univ T u

/-- Cut a chain glue on the interval down to the standing hypotheses
of the ring theorems: `heat_chain_glues` packages `paste_isHeatSol` and
the three restriction lemmas — the decomposable control, stated as the
brief's "interval = chain = Vorob'ev-free". -/
theorem heat_chain_glues {M : RingMesh} {D : ℝ} {T : Set ℝ}
    (hT : IsOpen T) {c1 c2 c3 : ℝ → ℝ → E}
    (h1 : IsHeatSol D M.I1 T c1) (h2 : IsHeatSol D M.I2 T c2)
    (h3 : IsHeatSol D M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    ∃ w : ℝ → ℝ → E, IsHeatSol D M.chart T w ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, w x t = c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, w x t = c2 x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, w x t = c3 x t) :=
  ⟨paste M c1 c2 c3, paste_isHeatSol hT h1 h2 h3 hs12 hs23,
    paste_eqOn_c1 hs12 hs23, paste_eqOn_c2 hs12 hs23,
    paste_eqOn_c3 hs12 hs23⟩

/-! ## Periodization -/

/-- Descend a chart field to the whole line by periodic extension:
read at the canonical representative in `[0, L)`. -/
noncomputable def periodize (L : ℝ) (w : ℝ → ℝ → E) : ℝ → ℝ → E :=
  fun y => w (y - L * ⌊y / L⌋)

theorem periodize_apply (L : ℝ) (w : ℝ → ℝ → E) (y t : ℝ) :
    periodize L w y t = w (y - L * ⌊y / L⌋) t := rfl

/-- Periodization is periodic (for every time, observed or not). -/
theorem periodize_periodic (L : ℝ) (hL : L ≠ 0) (w : ℝ → ℝ → E) (t : ℝ) :
    Function.Periodic (fun y => periodize L w y t) L := by
  intro y
  show w (y + L - L * ⌊(y + L) / L⌋) t = w (y - L * ⌊y / L⌋) t
  have h1 : (y + L) / L = y / L + 1 := by field_simp
  rw [h1, Int.floor_add_one,
    show ((⌊y / L⌋ + 1 : ℤ) : ℝ) = (⌊y / L⌋ : ℝ) + 1 by push_cast; ring,
    show y + L - L * ((⌊y / L⌋ : ℝ) + 1) = y - L * ⌊y / L⌋ by ring]

/-- The canonical representative lies in `[0, L)`. -/
theorem sub_floor_mem_Ico {L : ℝ} (hL : 0 < L) (y : ℝ) :
    y - L * ⌊y / L⌋ ∈ Ico (0 : ℝ) L := by
  have hL' : L ≠ 0 := hL.ne'
  have hy : L * (y / L) = y := by field_simp
  have h1 : (⌊y / L⌋ : ℝ) ≤ y / L := Int.floor_le _
  have h2 : y / L < ⌊y / L⌋ + 1 := Int.lt_floor_add_one _
  have h3 : L * (⌊y / L⌋ : ℝ) ≤ y := by
    have h := mul_le_mul_of_nonneg_left h1 hL.le
    rwa [hy] at h
  have h4 : y < L * ((⌊y / L⌋ : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left h2 hL
    rwa [hy] at h
  constructor
  · linarith
  · nlinarith

/-- **The germ presentation of the descent**: near any point, the
periodized field agrees (at observed times) with a single translate of
the chart field, whose base point lies inside the chart.  The wrap
hypothesis is consumed exactly at points congruent to `0 mod L` — the
ring-closing collar, and nowhere else. -/
theorem periodize_germ {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδL : δ < L)
    {T : Set ℝ} {w : ℝ → ℝ → E}
    (hwrap : ∀ z ∈ Ioo (-δ) δ, ∀ t ∈ T, w (z + L) t = w z t) (x₀ : ℝ) :
    ∃ (k : ℤ) (r : ℝ), 0 < r ∧
      (∀ y ∈ Ioo (x₀ - r) (x₀ + r), ∀ t ∈ T,
        periodize L w y t = w (y - L * k) t) ∧
      x₀ - L * k ∈ Ioo (-δ) (L + δ) := by
  set k := ⌊x₀ / L⌋ with hk
  obtain ⟨hz0, hzL⟩ := sub_floor_mem_Ico hL x₀
  rcases eq_or_lt_of_le hz0 with hz | hz
  · -- the wrap point: `x₀ = L·k`; the wall carries the left half-ball
    have hx₀ : x₀ = L * k := by linarith
    refine ⟨k, δ, hδ, ?_, ?_⟩
    · intro y hy t ht
      rcases le_or_gt (L * k) y with hcase | hcase
      · have hfl : ⌊y / L⌋ = k := by
          rw [Int.floor_eq_iff]
          constructor
          · rw [le_div_iff₀ hL]
            linarith
          · rw [div_lt_iff₀ hL]
            have hy2 := hy.2
            rw [hx₀] at hy2
            push_cast
            linarith
        rw [periodize_apply, hfl]
      · have hfl : ⌊y / L⌋ = k - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · rw [le_div_iff₀ hL]
            have hy1 := hy.1
            rw [hx₀] at hy1
            push_cast
            linarith
          · rw [div_lt_iff₀ hL]
            push_cast
            linarith
        have hmem : y - L * k ∈ Ioo (-δ) δ := by
          constructor
          · have hy1 := hy.1
            rw [hx₀] at hy1
            linarith
          · linarith
        rw [periodize_apply, hfl,
          show y - L * ((k - 1 : ℤ) : ℝ) = (y - L * k) + L by push_cast; ring]
        exact hwrap _ hmem t ht
    · rw [show x₀ - L * (k : ℝ) = 0 by linarith]
      exact ⟨by linarith, by linarith⟩
  · -- interior: the representative sits in the open period
    refine ⟨k, min (x₀ - L * k) (L - (x₀ - L * k)),
      lt_min hz (by linarith), ?_, ⟨by linarith, by linarith⟩⟩
    intro y hy t ht
    have hm1 : min (x₀ - L * k) (L - (x₀ - L * k)) ≤ x₀ - L * k :=
      min_le_left _ _
    have hm2 : min (x₀ - L * k) (L - (x₀ - L * k)) ≤ L - (x₀ - L * k) :=
      min_le_right _ _
    have h1 : L * k < y := by
      have := hy.1
      linarith
    have h2 : y < L * k + L := by
      have := hy.2
      linarith
    have hfl : ⌊y / L⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hL]
        linarith
      · rw [div_lt_iff₀ hL]
        push_cast
        linarith
    rw [periodize_apply, hfl]

/-- The periodized field agrees with the chart field on the whole
chart (at observed times): both collar copies read back through the
wrap identity. -/
theorem periodize_eqOn_chart {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδL : δ < L) {T : Set ℝ} {w : ℝ → ℝ → E}
    (hwrap : ∀ z ∈ Ioo (-δ) δ, ∀ t ∈ T, w (z + L) t = w z t) :
    ∀ x ∈ Ioo (-δ) (L + δ), ∀ t ∈ T, periodize L w x t = w x t := by
  intro x hx t ht
  rcases lt_or_ge x 0 with h0 | h0
  · -- `x ∈ (−δ, 0)`: the representative is `x + L`
    have hfl : ⌊x / L⌋ = -1 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast
        rw [le_div_iff₀ hL]
        have := hx.1
        linarith
      · push_cast
        rw [div_lt_iff₀ hL]
        linarith
    rw [periodize_apply, hfl,
      show x - L * ((-1 : ℤ) : ℝ) = x + L by push_cast; ring]
    exact hwrap x ⟨hx.1, by linarith⟩ t ht
  · rcases lt_or_ge x L with hxL | hxL
    · -- `x ∈ [0, L)`: the representative is `x` itself
      have hfl : ⌊x / L⌋ = 0 := by
        rw [Int.floor_eq_zero_iff]
        exact ⟨div_nonneg h0 hL.le, (div_lt_one hL).mpr hxL⟩
      rw [periodize_apply, hfl,
        show x - L * ((0 : ℤ) : ℝ) = x by push_cast; ring]
    · -- `x ∈ [L, L+δ)`: the representative is `x − L`
      have hfl : ⌊x / L⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor
        · push_cast
          rw [le_div_iff₀ hL]
          linarith
        · push_cast
          rw [div_lt_iff₀ hL]
          have := hx.2
          linarith
      have hmem : x - L ∈ Ioo (-δ) δ := by
        constructor
        · linarith
        · have := hx.2
          linarith
      have h2 := hwrap (x - L) hmem t ht
      rw [show x - L + L = x by ring] at h2
      rw [periodize_apply, hfl,
        show x - L * ((1 : ℤ) : ℝ) = x - L by push_cast; ring]
      exact h2.symm

/-- Periodization preserves solution-hood: with the wrap identity on
the collar, the descent of a chart solution solves globally.  The germ
lemma routes every point through a translate of the chart field, and
`HeatAt.comp_sub_const` carries the rows across the translation. -/
theorem periodize_isHeatSol {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδL : δ < L) {D : ℝ} {T : Set ℝ} (hT : IsOpen T) {w : ℝ → ℝ → E}
    (hsol : IsHeatSol D (Ioo (-δ) (L + δ)) T w)
    (hwrap : ∀ z ∈ Ioo (-δ) δ, ∀ t ∈ T, w (z + L) t = w z t) :
    IsHeatSol D Set.univ T (periodize L w) := by
  intro x₀ _ t ht
  obtain ⟨k, r, hr, hagree, hmem⟩ := periodize_germ hL hδ hδL hwrap x₀
  refine HeatAt.congr (Sx := Ioo (x₀ - r) (x₀ + r)) isOpen_Ioo hT
    ⟨by linarith, by linarith⟩ ht hagree ?_
  exact HeatAt.comp_sub_const (hsol _ hmem t ht)

/-! ## The ring glue: the con-obligation discharge -/

section MeshGlue

variable {M : RingMesh} {D : ℝ} {T : Set ℝ} {c1 c2 c3 : ℝ → ℝ → E}

/-- **The cyclic mesh glues** — the con-obligation discharge.  Cell
rows, the two chain walls, and the ring-closing wall together produce
a global `L`-periodic solution restricting to every cell datum.  The
route: chain paste (`paste_isHeatSol`), then periodization, with the
wrap wall consumed exactly once — at the ring-closing collar, where it
becomes the periodization's consistency identity.  Compare
`vorobev_no_joint`: at the measure tier the analogous local-to-global
inference is *false*; here it is a theorem because record-tier
constraints are local predicates and the differential operator is
germ-determined. -/
theorem heat_mesh_glues (hT : IsOpen T)
    (h1 : IsHeatSol D M.I1 T c1) (h2 : IsHeatSol D M.I2 T c2)
    (h3 : IsHeatSol D M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t)
    (hw : WrapWall M T c1 c3) :
    ∃ u : ℝ → ℝ → E, IsHeatTorusSol D M.L T u ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, u x t = c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, u x t = c2 x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, u x t = c3 x t) := by
  set w := paste M c1 c2 c3 with hwdef
  have hwsol : IsHeatSol D M.chart T w :=
    paste_isHeatSol hT h1 h2 h3 hs12 hs23
  have he1 := paste_eqOn_c1 (M := M) (c3 := c3) hs12 hs23
  have he2 := paste_eqOn_c2 (M := M) (c3 := c3) hs12 hs23
  have he3 := paste_eqOn_c3 (M := M) (c1 := c1) hs12 hs23
  -- the wrap identity of the pasted field, from the ring wall
  have hwrap : ∀ z ∈ Ioo (-M.δ) M.δ, ∀ t ∈ T, w (z + M.L) t = w z t := by
    intro z hz t ht
    have hz1 : z ∈ M.I1 := ⟨hz.1, by have := M.ha; have := M.hδ; linarith [hz.2]⟩
    have hz3 : z + M.L ∈ M.I3 := by
      constructor
      · have := M.hbL; linarith [hz.1]
      · linarith [hz.2]
    have hz1' : z + M.L - M.L ∈ M.I1 := by
      rw [show z + M.L - M.L = z by ring]
      exact hz1
    calc w (z + M.L) t = c3 (z + M.L) t := he3 _ hz3 t ht
      _ = c1 (z + M.L - M.L) t := hw _ hz3 hz1' t ht
      _ = c1 z t := by rw [show z + M.L - M.L = z by ring]
      _ = w z t := (he1 _ hz1 t ht).symm
  have hL := M.hL0
  refine ⟨periodize M.L w,
    ⟨fun t => periodize_periodic M.L hL.ne' w t,
      periodize_isHeatSol hL M.hδ M.hδL hT hwsol hwrap⟩, ?_, ?_, ?_⟩
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I1_subset_chart hx) t ht]
    exact he1 x hx t ht
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I2_subset_chart hx) t ht]
    exact he2 x hx t ht
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I3_subset_chart hx) t ht]
    exact he3 x hx t ht

end MeshGlue

/-! ## The mesh record space, atoms, and compositor -/

/-- The mesh record: one chart field per arc. -/
structure HeatRec (E : Type) where
  /-- The field on the first arc. -/
  c1 : ℝ → ℝ → E
  /-- The field on the middle arc. -/
  c2 : ℝ → ℝ → E
  /-- The field on the closing arc. -/
  c3 : ℝ → ℝ → E

variable (M : RingMesh) (D : ℝ) (T : Set ℝ)

/-- The first cell's constraint set. -/
def cell1C : Set (HeatRec E) := {p | IsHeatSol D M.I1 T p.c1}

/-- The middle cell's constraint set. -/
def cell2C : Set (HeatRec E) := {p | IsHeatSol D M.I2 T p.c2}

/-- The closing cell's constraint set. -/
def cell3C : Set (HeatRec E) := {p | IsHeatSol D M.I3 T p.c3}

/-- The seam wall at `a`: agreement on the open overlap collar. -/
def seam12C : Set (HeatRec E) :=
  {p | ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, p.c1 x t = p.c2 x t}

/-- The seam wall at `b`. -/
def seam23C : Set (HeatRec E) :=
  {p | ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, p.c2 x t = p.c3 x t}

/-- The ring-closing wall at `L ≡ 0`: the holonomy constraint. -/
def wrapC : Set (HeatRec E) := {p | WrapWall M T p.c1 p.c3}

/-- A mesh solution: all cell rows and all three walls. -/
structure IsMeshSol (p : HeatRec E) : Prop where
  cell1 : IsHeatSol D M.I1 T p.c1
  cell2 : IsHeatSol D M.I2 T p.c2
  cell3 : IsHeatSol D M.I3 T p.c3
  seam12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, p.c1 x t = p.c2 x t
  seam23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, p.c2 x t = p.c3 x t
  wrap : WrapWall M T p.c1 p.c3

/-- The mesh-solution set. -/
def meshSols : Set (HeatRec E) := {p | IsMeshSol M D T p}

/-- The chain sub-family: cells and chain walls, the ring-closing wall
deleted — the interval mesh's compiled atoms. -/
def heatChainAtoms : List (SubPMF (HeatRec E) → Prop) :=
  [suppC (cell1C M D T), suppC (cell2C M D T), suppC (cell3C M D T),
    suppC (seam12C M T), suppC (seam23C M T)]

/-- The compiled atoms of the cyclic mesh: three cells, three walls,
**conjoined once** (the mesh compositor discipline — all cell floors
and all interface walls into a single premise floor). -/
def heatAtoms : List (SubPMF (HeatRec E) → Prop) :=
  [suppC (cell1C M D T), suppC (cell2C M D T), suppC (cell3C M D T),
    suppC (seam12C M T), suppC (seam23C M T), suppC (wrapC M T)]

theorem heatAtoms_eq_chain_append :
    heatAtoms M D T (E := E) = heatChainAtoms M D T ++ [suppC (wrapC M T)] :=
  rfl

/-- Bundling: the six-atom conjunction is the support constraint of
the mesh-solution set — the wiring diagram's conjunction, taken once,
at the mesh joint. -/
theorem heatAtoms_iff (μ : SubPMF (HeatRec E)) :
    looseConj (heatAtoms M D T) μ ↔ suppC (meshSols M D T) μ := by
  simp only [heatAtoms, looseConj, suppC]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, -⟩ p hp
    exact ⟨h1 p hp, h2 p hp, h3 p hp, h4 p hp, h5 p hp, h6 p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).cell1, fun p hp => (h p hp).cell2,
      fun p hp => (h p hp).cell3, fun p hp => (h p hp).seam12,
      fun p hp => (h p hp).seam23, fun p hp => (h p hp).wrap, trivial⟩

/-! ## Seam-order independence (the possibilistic-stratum face)

At the constraint stratum the mesh compositor is a plain conjunction,
so composition order is a `List.Perm` invariance — general stock,
minted here (natural home: `SuFunctor.Adequacy.Inclusions`; kept
module-local to avoid touching a shared landed file mid-wave).  The
envelope-stratum statement (sup-associativity *before the single
envelope*) is the sibling mesh-assoc leg's, not this one's. -/

/-- Conjunction of constraints is permutation-invariant: satisfaction
reads through list membership only. -/
theorem _root_.SuFunctor.looseConj_perm {V : Type u}
    {l l' : List (SubPMF V → Prop)} (h : l.Perm l') (μ : SubPMF V) :
    looseConj l μ ↔ looseConj l' μ := by
  rw [looseConj_iff, looseConj_iff]
  exact ⟨fun H c hc => H c (h.mem_iff.mpr hc),
    fun H c hc => H c (h.mem_iff.mp hc)⟩

/-- Any seam ordering compiles the same mesh: the compositor is
order-canonical at this stratum. -/
theorem heatAtoms_order_independent {l : List (SubPMF (HeatRec E) → Prop)}
    (h : (heatAtoms M D T).Perm l) (μ : SubPMF (HeatRec E)) :
    looseConj l μ ↔ suppC (meshSols M D T) μ :=
  (SuFunctor.looseConj_perm h.symm μ).trans (heatAtoms_iff M D T μ)

/-! ## The con-obligation adjudication: witnesses -/

variable {M D T}

/-- Constants satisfy the heat rows everywhere, for every `D` — the
equilibria of the closed torus. -/
theorem heatAt_const (D : ℝ) (k : E) (x t : ℝ) :
    HeatAt D (fun _ _ => k) x t := by
  refine ⟨continuousAt_const, differentiableAt_const k, ?_, ?_⟩
  · simp only [deriv_const']
    exact differentiableAt_const 0
  · simp only [deriv_const', deriv_const, smul_zero]
    exact hasDerivAt_const t k

/-- The constant record. -/
def constRec (k : E) : HeatRec E := ⟨fun _ _ => k, fun _ _ => k, fun _ _ => k⟩

/-- Constants are torus solutions (any `L`, any `D` — the sign of `D`
is never consulted; see the module docstring). -/
theorem isHeatTorusSol_const (D L : ℝ) (T : Set ℝ) (k : E) :
    IsHeatTorusSol D L T (fun _ _ => k) where
  periodic := fun _ _ => rfl
  sol := fun x _ t _ => heatAt_const D k x t

/-- The constant record is a mesh solution: the constructive
consistency witness for the full cyclic family. -/
theorem isMeshSol_const (k : E) : IsMeshSol M D T (constRec k) where
  cell1 := fun x _ t _ => heatAt_const D k x t
  cell2 := fun x _ t _ => heatAt_const D k x t
  cell3 := fun x _ t _ => heatAt_const D k x t
  seam12 := fun _ _ _ _ => rfl
  seam23 := fun _ _ _ _ => rfl
  wrap := fun _ _ _ _ _ => rfl

/-- **The heat ring is consistent**: the compiled conjunction of the
cyclic family is satisfiable by a non-vacuous model — the Dirac at the
constant record.  This, not any per-cell check, is what discharges the
cyclic cover's `con` obligation: a global witness. -/
theorem heatAtoms_consistent :
    ∃ μ : SubPMF (HeatRec E), looseConj (heatAtoms M D T) μ ∧
      μ ≠ SubPMF.zero (HeatRec E) := by
  refine ⟨SubPMF.dirac (constRec 0), ?_, SubPMF.dirac_ne_zero _⟩
  rw [heatAtoms_iff]
  exact (suppC_dirac _ _).mpr (isMeshSol_const 0)

/-! ### The holonomy witness: the ring's obligation is real

The linear field `x ↦ x • e` solves the heat equation on the chart
(for every `D`), agrees with itself across both chain seams — and does
not descend to the circle.  It satisfies every cell atom and both
chain walls, and refuses exactly the ring-closing wall: the cyclic
cover's extra obligation is a genuine holonomy demand, invisible to
all per-cell and pairwise-chain checks. -/

/-- The linear field solves the rows (any `D`): first derivative
constant, second zero, time-constant. -/
theorem heatAt_linear (D : ℝ) (e : E) (x t : ℝ) :
    HeatAt D (fun y _ => y • e) x t := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z • e) e y := by
    intro y
    simpa using (hasDerivAt_id y).smul_const e
  have hderiv : (deriv fun y : ℝ => y • e) = fun _ => e := by
    funext y
    exact (hlin y).deriv
  refine ⟨?_, (hlin x).differentiableAt, ?_, ?_⟩
  · exact (continuous_fst.smul continuous_const).continuousAt
  · rw [hderiv]
    exact differentiableAt_const e
  · simp only [hderiv, deriv_const, smul_zero]
    exact hasDerivAt_const t (x • e)

/-- The linear record: the same non-descending field on every arc. -/
def linRec (e : E) : HeatRec E := ⟨fun y _ => y • e, fun y _ => y • e, fun y _ => y • e⟩

/-- The linear record satisfies the whole chain sub-family: all cell
atoms and both chain walls. -/
theorem chainAtoms_dirac_lin (e : E) :
    looseConj (heatChainAtoms M D T) (SubPMF.dirac (linRec e)) := by
  simp only [heatChainAtoms, looseConj]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    refine (suppC_dirac _ _).mpr ?_
  · exact fun x _ t _ => heatAt_linear D e x t
  · exact fun x _ t _ => heatAt_linear D e x t
  · exact fun x _ t _ => heatAt_linear D e x t
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl

/-- The linear record refuses the ring-closing wall: the holonomy
defect `L • e ≠ 0` is exactly the wrap mismatch. -/
theorem not_wrap_lin {e : E} (he : e ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ suppC (wrapC M T) (SubPMF.dirac (linRec e)) := by
  rw [suppC_dirac]
  intro hmem
  have hL := M.hL0
  have hI3 : M.L ∈ M.I3 := ⟨by have := M.hbL; have := M.hδ; linarith,
    by have := M.hδ; linarith⟩
  have hI1 : M.L - M.L ∈ M.I1 := by
    rw [sub_self]
    exact ⟨by have := M.hδ; linarith, by have := M.ha; have := M.hδ; linarith⟩
  have h := hmem M.L hI3 hI1 t₀ ht₀
  simp only [linRec] at h
  -- h : M.L • e = (M.L − M.L) • e
  rw [sub_self, zero_smul] at h
  exact (smul_ne_zero hL.ne' he) h

/-- **No repair exists**: no `L`-periodic global field restricts to the
linear record — `heat_mesh_glues`' conclusion is *false* for the chain
sub-family, so the ring-closing wall is load-bearing at statement
level, not merely in the proof. -/
theorem no_periodic_glue_lin {e : E} (he : e ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ ∃ u : ℝ → ℝ → E, IsHeatTorusSol D M.L T u ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, u x t = (linRec e).c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, u x t = (linRec e).c2 x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, u x t = (linRec e).c3 x t) := by
  rintro ⟨u, hu, hm1, -, hm3⟩
  have hδ := M.hδ
  have hL := M.hL0
  have hz1 : -(M.δ / 2) ∈ M.I1 :=
    ⟨by linarith, by have := M.ha; linarith⟩
  have hz3 : M.L - M.δ / 2 ∈ M.I3 :=
    ⟨by have := M.hbL; linarith, by linarith⟩
  have h1 : u (-(M.δ / 2)) t₀ = (-(M.δ / 2)) • e := by
    have h := hm1 _ hz1 t₀ ht₀
    simpa only [linRec] using h
  have h3 : u (M.L - M.δ / 2) t₀ = (M.L - M.δ / 2) • e := by
    have h := hm3 _ hz3 t₀ ht₀
    simpa only [linRec] using h
  have hper := hu.periodic t₀ (-(M.δ / 2))
  rw [show -(M.δ / 2) + M.L = M.L - M.δ / 2 by ring] at hper
  have hper' : u (M.L - M.δ / 2) t₀ = u (-(M.δ / 2)) t₀ := hper
  rw [h1, h3] at hper'
  have h0 : M.L • e = 0 := by
    have h2 : (M.L - M.δ / 2) • e - (-(M.δ / 2)) • e = 0 := by
      rw [hper', sub_self]
    rw [← sub_smul] at h2
    rw [show M.L - M.δ / 2 - -(M.δ / 2) = M.L by ring] at h2
    exact h2
  exact (smul_ne_zero hL.ne' he) h0

/-! ### The seam walls are load-bearing too (m1's statement partner) -/

/-- Two constant fields differing on a collar: cells satisfied, seam
refused. -/
def mismatchRec (e : E) : HeatRec E :=
  ⟨fun _ _ => 0, fun _ _ => e, fun _ _ => e⟩

theorem cellAtoms_mismatch (e : E) : IsHeatSol D M.I1 T (mismatchRec e).c1 ∧
    IsHeatSol D M.I2 T (mismatchRec e).c2 ∧
    IsHeatSol D M.I3 T (mismatchRec e).c3 :=
  ⟨fun x _ t _ => heatAt_const D 0 x t, fun x _ t _ => heatAt_const D e x t,
    fun x _ t _ => heatAt_const D e x t⟩

/-- The mismatched record refuses the seam wall at `a`. -/
theorem not_seam12_mismatch {e : E} (he : e ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    mismatchRec e ∉ seam12C M T (E := E) := by
  intro hmem
  have hδ := M.hδ
  have haI : M.a ∈ M.I1 ∩ M.I2 :=
    ⟨⟨by have := M.ha; linarith, by linarith⟩,
      ⟨by linarith, by have := M.hab; linarith⟩⟩
  have h := hmem M.a haI t₀ ht₀
  simp only [mismatchRec] at h
  exact he h.symm

/-- No global field restricts to the mismatched record: the seam wall
is the exact obstruction it removes. -/
theorem no_glue_mismatch {e : E} (he : e ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    ¬ ∃ u : ℝ → ℝ → E,
      (∀ x ∈ M.I1, ∀ t ∈ T, u x t = (mismatchRec e).c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, u x t = (mismatchRec e).c2 x t) := by
  rintro ⟨u, hm1, hm2⟩
  have hδ := M.hδ
  have haI1 : M.a ∈ M.I1 := ⟨by have := M.ha; linarith, by linarith⟩
  have haI2 : M.a ∈ M.I2 := ⟨by linarith, by have := M.hab; linarith⟩
  have h1 : u M.a t₀ = 0 := by
    have h := hm1 _ haI1 t₀ ht₀
    simpa only [mismatchRec] using h
  have h2 : u M.a t₀ = e := by
    have h := hm2 _ haI2 t₀ ht₀
    simpa only [mismatchRec] using h
  rw [h1] at h2
  exact he h2.symm

/-! ## The contrast: two rings, side by side

The first consumption of the Vorob'ev mechanization by an instance.
Both covers are cyclic three-cell rings.  The heat ring's compiled
conjunction is satisfiable (a global witness exists — constants); the
frustrated marginal ring's is not, though every proper sub-family is.
The difference is not the cover shape (`corrRing_glues` already showed
the shape is innocent) but the *tier and provenance* of the cell data:
record-tier local predicates, presented as clips of a global class,
against measure-tier marginal constraints that are local predicates of
nothing. -/

theorem heat_ring_glues_vorobev_ring_not :
    (∃ μ : SubPMF (HeatRec E), looseConj (heatAtoms M D T) μ ∧
        μ ≠ SubPMF.zero (HeatRec E)) ∧
      ¬ ∃ μ : SubPMF (Bool × Bool × Bool), vorobevGlue μ :=
  ⟨heatAtoms_consistent, vorobev_unsatisfiable⟩

/-- The credal-stratum contrast: the heat mesh's lawful credal
completion is **not** the bottom object (`credalCompile_vorobevGlue`
computed the frustrated ring's to be exactly bottom).  Honest
inconsistency is representable — and the heat ring does not need the
representation. -/
theorem credalCompile_heatAtoms_ne_bot :
    credalCompile (looseConj (heatAtoms M D T)) ≠
      rayC (SubPMF.zero (HeatRec E)) := by
  intro h
  obtain ⟨μ, hμ, hμ0⟩ := heatAtoms_consistent (M := M) (D := D) (T := T) (E := E)
  have h1 : credalCompile (looseConj (heatAtoms M D T)) μ :=
    le_credalCompile _ _ hμ
  rw [h] at h1
  obtain ⟨s, -, -, hw⟩ := h1
  exact hμ0 ((SubPMF.eq_zero_iff_wt μ).mpr (by rw [hw, SubPMF.zero_wt, smul_zero]))

/-! ## The left edge and the square -/

/-- The record-matching relation: a mesh record presents a torus
solution when each cell field agrees with it on that cell (off-cell
chart values are not observables — the delay line's convention). -/
structure RecMatchesTorus (M : RingMesh) (T : Set ℝ) (u : ℝ → ℝ → E)
    (p : HeatRec E) : Prop where
  m1 : ∀ x ∈ M.I1, ∀ t ∈ T, p.c1 x t = u x t
  m2 : ∀ x ∈ M.I2, ∀ t ∈ T, p.c2 x t = u x t
  m3 : ∀ x ∈ M.I3, ∀ t ∈ T, p.c3 x t = u x t

/-- The classical object's record presentations: mesh records matching
some global periodic solution. -/
def heatClassicalRecs (M : RingMesh) (D : ℝ) (T : Set ℝ) : Set (HeatRec E) :=
  {p | ∃ u : ℝ → ℝ → E, IsHeatTorusSol D M.L T u ∧ RecMatchesTorus M T u p}

/-- **The wiring theorem, mesh form**: mesh solutions are exactly the
records of global periodic solutions.  Forward is the ring glue
(`heat_mesh_glues`); backward is clipping — restriction of rows is
free (locality again), walls hold because all cells read one field,
and the ring wall is the periodicity read on the wrap collar. -/
theorem meshSols_eq_classical (M : RingMesh) (D : ℝ) {T : Set ℝ}
    (hT : IsOpen T) :
    meshSols M D T (E := E) = heatClassicalRecs M D T := by
  ext p
  constructor
  · intro hp
    obtain ⟨u, hu, e1, e2, e3⟩ := heat_mesh_glues hT hp.cell1 hp.cell2
      hp.cell3 hp.seam12 hp.seam23 hp.wrap
    exact ⟨u, hu, ⟨fun x hx t ht => (e1 x hx t ht).symm,
      fun x hx t ht => (e2 x hx t ht).symm,
      fun x hx t ht => (e3 x hx t ht).symm⟩⟩
  · rintro ⟨u, hu, hm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx t ht
      exact HeatAt.congr M.isOpen_I1 hT hx ht hm.m1
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      exact HeatAt.congr M.isOpen_I2 hT hx ht hm.m2
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      exact HeatAt.congr M.isOpen_I3 hT hx ht hm.m3
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      rw [hm.m1 x hx.1 t ht, hm.m2 x hx.2 t ht]
    · intro x hx t ht
      rw [hm.m2 x hx.1 t ht, hm.m3 x hx.2 t ht]
    · intro x hx3 hx1 t ht
      rw [hm.m3 x hx3 t ht, hm.m1 _ hx1 t ht]
      have hper := hu.periodic t (x - M.L)
      rw [show x - M.L + M.L = x by ring] at hper
      exact hper

/-- **The heat-on-torus adequacy square** — an *invertible* globular
cell of `Crd (HeatRec E)`: compiling the cyclic mesh to its six atoms
and denoting agrees with interpreting classically (global periodic
solutions) and including the solution set at the possibilistic
stratum.  Two-sided at the pointwise-record stratum: the ring glue
closes the converse, so the cover-tier instance inherits the delay
line's invertibility — against the one-sided expectation, which turns
out to price the *finite/certificate* stratum, not the record stratum
(see the module docstring and the memo). -/
theorem heat_adequacy (M : RingMesh) (D : ℝ) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec E)} :
    ∃ α : Cell (looseConj (heatAtoms M D T) : Loose a a)
        (suppC (heatClassicalRecs M D T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [heatAtoms_iff, meshSols_eq_classical M D hT]

/-! ## The per-solution (Dirac) face -/

/-- The canonical record of a global solution: every cell reads the
same field. -/
def heatRecOf (u : ℝ → ℝ → E) : HeatRec E := ⟨u, u, u⟩

theorem recMatchesTorus_heatRecOf (M : RingMesh) (T : Set ℝ)
    (u : ℝ → ℝ → E) : RecMatchesTorus M T u (heatRecOf u) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem heatRecOf_mem_heatClassicalRecs {M : RingMesh} {D : ℝ} {T : Set ℝ}
    {u : ℝ → ℝ → E} (hu : IsHeatTorusSol D M.L T u) :
    heatRecOf u ∈ heatClassicalRecs M D T :=
  ⟨u, hu, recMatchesTorus_heatRecOf M T u⟩

/-- The per-solution Dirac face: each global solution's point mass
satisfies the compiled mesh atoms. -/
theorem heatAtoms_dirac_of_torusSol {M : RingMesh} {D : ℝ} {T : Set ℝ}
    (hT : IsOpen T) {u : ℝ → ℝ → E} (hu : IsHeatTorusSol D M.L T u) :
    looseConj (heatAtoms M D T) (SubPMF.dirac (heatRecOf u)) := by
  rw [heatAtoms_iff, meshSols_eq_classical M D hT]
  exact (suppC_dirac _ _).mpr (heatRecOf_mem_heatClassicalRecs hu)

/-- The deterministic inclusion entails the compiled constraints, per
solution: the `diracC` bottom edge at the per-solution grain. -/
theorem diracC_heatRecOf_entails_heat {M : RingMesh} {D : ℝ} {T : Set ℝ}
    (hT : IsOpen T) {u : ℝ → ℝ → E} (hu : IsHeatTorusSol D M.L T u) :
    ∀ μ : SubPMF (HeatRec E), diracC (heatRecOf u) μ →
      looseConj (heatAtoms M D T) μ := by
  intro μ hμ
  have hμ' : μ = SubPMF.dirac (heatRecOf u) := hμ
  rw [hμ']
  exact heatAtoms_dirac_of_torusSol hT hu

end Adequacy
end SuFunctor

#print axioms SuFunctor.Adequacy.HeatAt.congr
#print axioms SuFunctor.Adequacy.heat_chain_glues
#print axioms SuFunctor.Adequacy.heat_mesh_glues
#print axioms SuFunctor.Adequacy.heatAtoms_iff
#print axioms SuFunctor.Adequacy.meshSols_eq_classical
#print axioms SuFunctor.Adequacy.heat_adequacy
#print axioms SuFunctor.Adequacy.heatAtoms_consistent
#print axioms SuFunctor.Adequacy.chainAtoms_dirac_lin
#print axioms SuFunctor.Adequacy.not_wrap_lin
#print axioms SuFunctor.Adequacy.no_periodic_glue_lin
#print axioms SuFunctor.Adequacy.heat_ring_glues_vorobev_ring_not
#print axioms SuFunctor.Adequacy.credalCompile_heatAtoms_ne_bot
#print axioms SuFunctor.looseConj_perm
#print axioms SuFunctor.Adequacy.heatAtoms_order_independent
