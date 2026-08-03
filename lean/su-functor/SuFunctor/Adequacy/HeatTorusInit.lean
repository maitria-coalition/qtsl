import SuFunctor.Adequacy.HeatTorus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Adequacy: the initial face as exposed port (heat on the torus)

The heat-on-torus square (`SuFunctor.Adequacy.HeatTorus`) kept its time
windows open — interior discipline; no statement mentions `t = 0`.
This module wires the **initial condition as an exposed port**: the
initial face enters as a boundary *trace along the window's own
filter* (`InitTraceOn`, a `Tendsto` into `𝓝[T] 0`), never as a row at
an interior point.  The port datum `g : ℝ → E` is a chart function
whose off-arc values are not observables (the delay-line `RecMatches`
convention); three port atoms — one per arc — extend the six mesh
atoms to nine, and the ported adequacy square (`heat_init_adequacy`)
closes, still two-sided at the pointwise-record stratum.

Design notes, load-bearing:

* **Feeding the port is a named separate stratum.**  `PortFeed` (the
  existence of a global periodic solution attaining trace `g`) is a
  *definition* here, and the con-obligation discharge is deliberately
  **conditional** (`heatInitAtoms_consistent_of_feed`): for general
  admissible data, feeding the port IS the heat semigroup `e^{tDΔ}` on
  the circle — enclosure-stratum content, cited and never mechanized
  (`bridge:semigroup@enclosure`).  This is the heat analogue of the
  DTMC square's Ionescu–Tulcea stratum: there, the finite-horizon laws
  are proved and the σ-additive extension is named next door; here,
  the record-stratum square is proved and existence-for-given-data is
  named next door.  The unconditional consistency theorem is
  deliberately absent — that absence is this module's honesty content.
* **The port is constructively feedable without any semigroup.**
  Equilibria feed constant data (`portFeed_const`), and one honest
  transient exists in elementary calculus: the single Fourier mode
  `(exp (−D·ω²·t) · cos (ω·x)) • e` feeds the genuinely nonconstant
  datum `cos (ω·x) • e` (`portFeed_mode`, `modeDatum_ne_const`) — so
  the analytic floor is "general `g` needs the semigroup," not
  "nothing beyond equilibria is expressible."  Every *other* nonzero
  mode superposition is fed the same way; what the semigroup buys is
  the limit over infinitely many modes for merely-continuous data.
* **Compatibility conditions on the datum are derived, not assumed.**
  The delay line's corner-condition surprise (the PDE corner
  compatibility IS the DDE initial condition) recurs
  one cover-rung up: the wrap wall plus the traces force the datum's
  holonomy identity `g x = g (x − L)` on the wrap collar
  (`initFace_wrap_compat`), and periodicity of a global solution
  forces the same identity at the chart's self-overlap
  (`IsHeatTorusSolInit.trace_wrap_compat`).  No adequacy-side
  statement hypothesizes admissibility of `g`.
* **The face's only new fee is the filter's non-triviality.**
  Uniqueness-of-limits arguments consume `(𝓝[T] 0).NeBot` — "`0` is
  genuinely on the window's boundary" — and nothing else new; for the
  concrete face `T = Ioo 0 τ` the fee is discharged
  (`initFace_neBot`).  With a window not clinging to `0`, traces are
  vacuous and the compatibility statements are *false*: the fee is
  load-bearing (mutant m2 of the prereg).
* **`D`'s sign is still nowhere.**  The mode feed works verbatim for
  `D < 0` (backward heat feeds the same mode, growing); the record
  stratum cannot see well-posedness direction, corroborating the
  parent module's finding at the port.  Uniqueness of the fed
  solution is likewise not owed and not consumed: the square
  quantifies over solutions, and how many there are is
  enclosure-stratum business (maximum principle for `D > 0`; genuine
  non-uniqueness phenomena backward), cited with the semigroup.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Set Topology Filter

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The trace row -/

/-- The initial-trace row at a single spatial point: the field's value
on the ray `{x} × T` attains the port datum `g x` along the window's
own boundary filter `𝓝[T] 0`.  The face is the boundary of the window;
the filter says so without ever putting `0` inside it.  Even more
local than `HeatAt`: only the field on one spatial ray is mentioned. -/
def InitTraceOn (T : Set ℝ) (g : ℝ → E) (u : ℝ → ℝ → E) (x : ℝ) : Prop :=
  Filter.Tendsto (fun t => u x t) (𝓝[T] (0 : ℝ)) (𝓝 (g x))

/-- Traces transport under agreement on the ray × window: the row
mentions only observed values. -/
theorem InitTraceOn.congr {T : Set ℝ} {g : ℝ → E} {u v : ℝ → ℝ → E}
    {x : ℝ} (hagree : ∀ t ∈ T, u x t = v x t)
    (h : InitTraceOn T g v x) : InitTraceOn T g u x :=
  Filter.Tendsto.congr'
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht =>
      (hagree t ht).symm) h

/-- The concrete face pays its filter fee: for the window `Ioo 0 τ`,
the origin is genuinely on the boundary — `𝓝[Ioo 0 τ] 0` is
non-trivial.  This is the only new topological hypothesis anywhere in
the module. -/
theorem initFace_neBot {τ : ℝ} (hτ : 0 < τ) :
    (𝓝[Ioo (0 : ℝ) τ] (0 : ℝ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [closure_Ioo hτ.ne]
    exact ⟨le_refl 0, hτ.le⟩)

/-! ## The port atoms -/

/-- The first arc's port atom: the first cell field attains trace `g`
on `I₁`. -/
def init1C (M : RingMesh) (T : Set ℝ) (g : ℝ → E) : Set (HeatRec E) :=
  {p | ∀ x ∈ M.I1, InitTraceOn T g p.c1 x}

/-- The middle arc's port atom. -/
def init2C (M : RingMesh) (T : Set ℝ) (g : ℝ → E) : Set (HeatRec E) :=
  {p | ∀ x ∈ M.I2, InitTraceOn T g p.c2 x}

/-- The closing arc's port atom. -/
def init3C (M : RingMesh) (T : Set ℝ) (g : ℝ → E) : Set (HeatRec E) :=
  {p | ∀ x ∈ M.I3, InitTraceOn T g p.c3 x}

/-- A ported mesh solution: the six mesh constraints plus the three
per-cell traces. -/
structure IsInitMeshSol (M : RingMesh) (D : ℝ) (T : Set ℝ) (g : ℝ → E)
    (p : HeatRec E) : Prop extends IsMeshSol M D T p where
  trace1 : ∀ x ∈ M.I1, InitTraceOn T g p.c1 x
  trace2 : ∀ x ∈ M.I2, InitTraceOn T g p.c2 x
  trace3 : ∀ x ∈ M.I3, InitTraceOn T g p.c3 x

/-- The ported mesh-solution set. -/
def meshInitSols (M : RingMesh) (D : ℝ) (T : Set ℝ) (g : ℝ → E) :
    Set (HeatRec E) :=
  {p | IsInitMeshSol M D T g p}

/-- The ported atom list: the six mesh atoms and the three port atoms,
conjoined once (the mesh compositor discipline, unchanged — the port
is three more conjuncts at the same joint). -/
def heatInitAtoms (M : RingMesh) (D : ℝ) (T : Set ℝ) (g : ℝ → E) :
    List (SubPMF (HeatRec E) → Prop) :=
  heatAtoms M D T ++
    [suppC (init1C M T g), suppC (init2C M T g), suppC (init3C M T g)]

theorem heatInitAtoms_eq_append (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (g : ℝ → E) :
    heatInitAtoms M D T g (E := E) = heatAtoms M D T ++
      [suppC (init1C M T g), suppC (init2C M T g), suppC (init3C M T g)] :=
  rfl

/-- Bundling: the nine-atom conjunction is the support constraint of
the ported mesh-solution set. -/
theorem heatInitAtoms_iff (M : RingMesh) (D : ℝ) (T : Set ℝ) (g : ℝ → E)
    (μ : SubPMF (HeatRec E)) :
    looseConj (heatInitAtoms M D T g) μ ↔
      suppC (meshInitSols M D T g) μ := by
  simp only [heatInitAtoms, heatAtoms, List.cons_append, List.nil_append,
    looseConj, suppC]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ p hp
    exact ⟨⟨h1 p hp, h2 p hp, h3 p hp, h4 p hp, h5 p hp, h6 p hp⟩,
      h7 p hp, h8 p hp, h9 p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).cell1, fun p hp => (h p hp).cell2,
      fun p hp => (h p hp).cell3, fun p hp => (h p hp).seam12,
      fun p hp => (h p hp).seam23, fun p hp => (h p hp).wrap,
      fun p hp => (h p hp).trace1, fun p hp => (h p hp).trace2,
      fun p hp => (h p hp).trace3, trivial⟩

/-! ## The corner condition, one cover-rung up

The delay line's corner compatibility (`y(0) = φ(0)`) was the wiring's
theorem, not a hypothesis.  Here the analogous statement is the port
datum's *holonomy* identity: on the wrap collar the wall plus the two
traces force `g x = g (x − L)`.  No admissibility of `g` is ever
assumed on the adequacy side. -/

/-- **The port datum inherits the holonomy constraint** — derived from
wall + traces by uniqueness of limits, never assumed.  Consumes the
face's filter fee (`NeBot`): with a window not clinging to `0` the
statement would be false, traces being vacuous (prereg mutant m2). -/
theorem initFace_wrap_compat {M : RingMesh} {D : ℝ} {T : Set ℝ}
    {g : ℝ → E} {p : HeatRec E} (h : IsInitMeshSol M D T g p)
    (hne : (𝓝[T] (0 : ℝ)).NeBot) {x : ℝ} (hx3 : x ∈ M.I3)
    (hx1 : x - M.L ∈ M.I1) : g x = g (x - M.L) := by
  haveI := hne
  have h3 : InitTraceOn T g p.c3 x := h.trace3 x hx3
  have h1 : InitTraceOn T g p.c1 (x - M.L) := h.trace1 _ hx1
  have hagree : ∀ t ∈ T, p.c3 x t = p.c1 (x - M.L) t := fun t ht =>
    h.wrap x hx3 hx1 t ht
  have h3' : Filter.Tendsto (fun t => p.c1 (x - M.L) t) (𝓝[T] (0 : ℝ))
      (𝓝 (g x)) :=
    Filter.Tendsto.congr'
      (Filter.eventually_of_mem self_mem_nhdsWithin hagree) h3
  exact tendsto_nhds_unique h3' h1

/-! ## The ported left edge -/

/-- A global torus solution attaining the port datum: `L`-periodic,
heat rows everywhere on the window, and the trace `g` on the chart
(the chart covers the circle; off-chart trace is determined by
periodicity and not separately owed). -/
structure IsHeatTorusSolInit (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (u : ℝ → ℝ → E) (g : ℝ → E) : Prop
    extends IsHeatTorusSol D M.L T u where
  trace : ∀ x ∈ M.chart, InitTraceOn T g u x

/-- The global face of the corner condition: a periodic solution's
trace inherits the collar identity at the chart's self-overlap —
exactly where the chart double-covers the circle, and nowhere else is
anything forced. -/
theorem IsHeatTorusSolInit.trace_wrap_compat {M : RingMesh} {D : ℝ}
    {T : Set ℝ} {u : ℝ → ℝ → E} {g : ℝ → E}
    (h : IsHeatTorusSolInit M D T u g) (hne : (𝓝[T] (0 : ℝ)).NeBot)
    {x : ℝ} (hx : x ∈ M.chart) (hxL : x + M.L ∈ M.chart) :
    g (x + M.L) = g x := by
  haveI := hne
  have h1 : InitTraceOn T g u x := h.trace x hx
  have h2 : InitTraceOn T g u (x + M.L) := h.trace _ hxL
  have hper : ∀ t, u (x + M.L) t = u x t := fun t => h.periodic t x
  have h2' : Filter.Tendsto (fun t => u x t) (𝓝[T] (0 : ℝ))
      (𝓝 (g (x + M.L))) :=
    (Filter.tendsto_congr hper).mp h2
  exact tendsto_nhds_unique h2' h1

/-- The three arcs cover the chart (`δ > 0` makes the overlaps
nonempty, so the union is the whole interval). -/
theorem RingMesh.mem_arc_of_mem_chart (M : RingMesh) {x : ℝ}
    (hx : x ∈ M.chart) : x ∈ M.I1 ∨ x ∈ M.I2 ∨ x ∈ M.I3 := by
  obtain ⟨hxl, hxr⟩ := hx
  have hδ := M.hδ
  have ha := M.ha
  have hab := M.hab
  have hbL := M.hbL
  by_cases h1 : x < M.a + M.δ
  · exact Or.inl ⟨hxl, h1⟩
  · by_cases h2 : x < M.b + M.δ
    · exact Or.inr (Or.inl ⟨by linarith [not_lt.mp h1], h2⟩)
    · exact Or.inr (Or.inr ⟨by linarith [not_lt.mp h2], hxr⟩)

/-- The ported classical records: mesh records matching some global
periodic solution that attains the port datum. -/
def heatInitClassicalRecs (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (g : ℝ → E) : Set (HeatRec E) :=
  {p | ∃ u : ℝ → ℝ → E,
    IsHeatTorusSolInit M D T u g ∧ RecMatchesTorus M T u p}

/-! ## The ported wiring theorem and square -/

/-- **The ported wiring theorem**: ported mesh solutions are exactly
the records of global periodic solutions attaining the port datum.
Forward is the ring glue plus trace transfer through the restriction
identities (the trace row is local, so the glue carries it for free —
no uniform-in-x control, the stratum where parabolic smoothing would
first appear, is ever consumed); backward is clipping, and traces
restrict. -/
theorem meshInitSols_eq_classical (M : RingMesh) (D : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (g : ℝ → E) :
    meshInitSols M D T g (E := E) = heatInitClassicalRecs M D T g := by
  ext p
  constructor
  · intro hp
    obtain ⟨u, hu, e1, e2, e3⟩ := heat_mesh_glues hT hp.cell1 hp.cell2
      hp.cell3 hp.seam12 hp.seam23 hp.wrap
    refine ⟨u, ⟨hu, ?_⟩, ⟨fun x hx t ht => (e1 x hx t ht).symm,
      fun x hx t ht => (e2 x hx t ht).symm,
      fun x hx t ht => (e3 x hx t ht).symm⟩⟩
    intro x hx
    rcases M.mem_arc_of_mem_chart hx with h | h | h
    · exact InitTraceOn.congr (fun t ht => e1 x h t ht) (hp.trace1 x h)
    · exact InitTraceOn.congr (fun t ht => e2 x h t ht) (hp.trace2 x h)
    · exact InitTraceOn.congr (fun t ht => e3 x h t ht) (hp.trace3 x h)
  · rintro ⟨u, hu, hm⟩
    have hmesh : p ∈ meshSols M D T (E := E) := by
      rw [meshSols_eq_classical M D hT]
      exact ⟨u, hu.toIsHeatTorusSol, hm⟩
    refine ⟨hmesh, ?_, ?_, ?_⟩
    · intro x hx
      exact InitTraceOn.congr (fun t ht => hm.m1 x hx t ht)
        (hu.trace x (M.I1_subset_chart hx))
    · intro x hx
      exact InitTraceOn.congr (fun t ht => hm.m2 x hx t ht)
        (hu.trace x (M.I2_subset_chart hx))
    · intro x hx
      exact InitTraceOn.congr (fun t ht => hm.m3 x hx t ht)
        (hu.trace x (M.I3_subset_chart hx))

/-- **The ported adequacy square** — an invertible globular cell:
compiling the cyclic mesh *with its initial-condition port* to the
nine atoms and denoting agrees with interpreting classically (global
periodic solutions attaining the datum) and including at the
possibilistic stratum.  Still two-sided at the pointwise-record
stratum: the initial face does not break invertibility (prereg
crux A). -/
theorem heat_init_adequacy (M : RingMesh) (D : ℝ) {T : Set ℝ}
    (hT : IsOpen T) (g : ℝ → E) {a : Crd (HeatRec E)} :
    ∃ α : Cell (looseConj (heatInitAtoms M D T g) : Loose a a)
        (suppC (heatInitClassicalRecs M D T g)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [heatInitAtoms_iff, meshInitSols_eq_classical M D hT]

/-! ## Feeding the port: the named analytic floor

`PortFeed` is where the enclosure stratum begins.  For general
admissible data (continuous, collar-compatible), the feed is the heat
semigroup on the circle — **cited, not mechanized**
(`bridge:semigroup@enclosure`); the DTMC square names Ionescu–Tulcea
at exactly this seam.  The two constructive feeds below are the honest
extent of semigroup-free feeding: equilibria, and single Fourier
modes (elementary calculus — and note the *exact-ℚ* shadow of the mode
is enclosure-shaped too: `exp` is transcendental at rational times,
so the certificate stratum sandwiches it; the rung-2 exact-ℚ mesh
layer owns that seam). -/

/-- The port feeds for datum `g`: some global periodic solution
attains trace `g`.  An existential the square never owes — one-sided
by type. -/
def PortFeed (M : RingMesh) (D : ℝ) (T : Set ℝ) (g : ℝ → E) : Prop :=
  ∃ u : ℝ → ℝ → E, IsHeatTorusSolInit M D T u g

/-- **Conditional con discharge**: given a feed, the ported conjunction
has a non-vacuous model — the Dirac at the fed solution's canonical
record.  The *unconditional* statement is deliberately absent: for
general data it is the semigroup's existence theorem, named above and
not owed here. -/
theorem heatInitAtoms_consistent_of_feed {M : RingMesh} {D : ℝ}
    {T : Set ℝ} (hT : IsOpen T) {g : ℝ → E}
    (hfeed : PortFeed M D T g) :
    ∃ μ : SubPMF (HeatRec E), looseConj (heatInitAtoms M D T g) μ ∧
      μ ≠ SubPMF.zero (HeatRec E) := by
  obtain ⟨u, hu⟩ := hfeed
  refine ⟨SubPMF.dirac (heatRecOf u), ?_, SubPMF.dirac_ne_zero _⟩
  rw [heatInitAtoms_iff, meshInitSols_eq_classical M D hT]
  exact (suppC_dirac _ _).mpr ⟨u, hu, recMatchesTorus_heatRecOf M T u⟩

/-- Equilibria feed constant data: the port is feedable with zero
analysis. -/
theorem portFeed_const (M : RingMesh) (D : ℝ) (T : Set ℝ) (k : E) :
    PortFeed M D T (fun _ => k) :=
  ⟨fun _ _ => k, isHeatTorusSol_const D M.L T k,
    fun _ _ => tendsto_const_nhds⟩

/-! ### The mode feed: one honest transient, no semigroup -/

/-- The single-mode field `(exp (−D·ω²·t) · cos (ω·x)) • e`. -/
noncomputable def modeField (D ω : ℝ) (e : E) : ℝ → ℝ → E :=
  fun x t => (Real.exp (-(D * ω ^ 2) * t) * Real.cos (ω * x)) • e

/-- The mode's initial datum `cos (ω·x) • e`. -/
noncomputable def modeDatum (ω : ℝ) (e : E) : ℝ → E :=
  fun x => Real.cos (ω * x) • e

theorem modeField_hasDerivAt_x (D ω : ℝ) (e : E) (t y : ℝ) :
    HasDerivAt (fun z => modeField D ω e z t)
      ((Real.exp (-(D * ω ^ 2) * t) * (-Real.sin (ω * y) * ω)) • e) y := by
  have h1 : HasDerivAt (fun z : ℝ => ω * z) ω y := by
    simpa using (hasDerivAt_id y).const_mul ω
  have h2 : HasDerivAt (fun z => Real.cos (ω * z))
      (-Real.sin (ω * y) * ω) y := h1.cos
  have h3 := (h2.const_mul (Real.exp (-(D * ω ^ 2) * t))).smul_const e
  simpa only [modeField] using h3

theorem modeField_deriv_x (D ω : ℝ) (e : E) (t : ℝ) :
    (deriv fun z => modeField D ω e z t)
      = fun y => (Real.exp (-(D * ω ^ 2) * t) * (-Real.sin (ω * y) * ω)) • e :=
  funext fun y => (modeField_hasDerivAt_x D ω e t y).deriv

theorem modeField_hasDerivAt_x2 (D ω : ℝ) (e : E) (t y : ℝ) :
    HasDerivAt (deriv fun z => modeField D ω e z t)
      ((Real.exp (-(D * ω ^ 2) * t) * (-Real.cos (ω * y) * ω ^ 2)) • e) y := by
  rw [modeField_deriv_x]
  have h1 : HasDerivAt (fun z : ℝ => ω * z) ω y := by
    simpa using (hasDerivAt_id y).const_mul ω
  have h2 : HasDerivAt (fun z => Real.sin (ω * z))
      (Real.cos (ω * y) * ω) y := h1.sin
  have h3 : HasDerivAt (fun z => -Real.sin (ω * z) * ω)
      (-Real.cos (ω * y) * ω ^ 2) y := by
    rw [show -Real.cos (ω * y) * ω ^ 2 = -(Real.cos (ω * y) * ω) * ω by ring]
    exact (h2.neg).mul_const ω
  exact (h3.const_mul (Real.exp (-(D * ω ^ 2) * t))).smul_const e

theorem modeField_hasDerivAt_t (D ω : ℝ) (e : E) (x t : ℝ) :
    HasDerivAt (fun s => modeField D ω e x s)
      ((Real.exp (-(D * ω ^ 2) * t) * -(D * ω ^ 2) * Real.cos (ω * x)) • e)
      t := by
  have h1 : HasDerivAt (fun s : ℝ => -(D * ω ^ 2) * s) (-(D * ω ^ 2)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(D * ω ^ 2))
  have h2 := h1.exp
  have h3 := (h2.mul_const (Real.cos (ω * x))).smul_const e
  simpa only [modeField] using h3

/-- The mode satisfies the heat rows at every point, for every `D` —
the sign is never consulted (backward heat feeds the same mode,
growing). -/
theorem heatAt_mode (D ω : ℝ) (e : E) (x t : ℝ) :
    HeatAt D (modeField D ω e) x t := by
  refine ⟨?_, (modeField_hasDerivAt_x D ω e t x).differentiableAt,
    (modeField_hasDerivAt_x2 D ω e t x).differentiableAt, ?_⟩
  · simp only [modeField]
    fun_prop
  · have hd2 : deriv (deriv fun y => modeField D ω e y t) x
        = (Real.exp (-(D * ω ^ 2) * t) * (-Real.cos (ω * x) * ω ^ 2)) • e :=
      (modeField_hasDerivAt_x2 D ω e t x).deriv
    rw [hd2, smul_smul,
      show D * (Real.exp (-(D * ω ^ 2) * t) * (-Real.cos (ω * x) * ω ^ 2))
          = Real.exp (-(D * ω ^ 2) * t) * -(D * ω ^ 2) * Real.cos (ω * x)
        by ring]
    exact modeField_hasDerivAt_t D ω e x t

/-- The mode descends to the circle when the frequency is resonant:
`ω · L = k · 2π`. -/
theorem modeField_periodic (D ω : ℝ) (e : E) {k : ℤ} {L : ℝ}
    (hω : ω * L = k * (2 * Real.pi)) (t : ℝ) :
    Function.Periodic (fun y => modeField D ω e y t) L := by
  intro y
  simp only [modeField]
  rw [show ω * (y + L) = ω * y + (k : ℝ) * (2 * Real.pi) by
      rw [mul_add, hω],
    Real.cos_add_int_mul_two_pi]

/-- The mode attains its datum along any window's boundary filter: at
`t = 0` the exponential is `1`.  No `NeBot` needed — feeds never argue
by uniqueness. -/
theorem modeField_trace (D ω : ℝ) (e : E) (T : Set ℝ) (x : ℝ) :
    InitTraceOn T (modeDatum ω e) (modeField D ω e) x := by
  have hc : ContinuousAt (fun s => modeField D ω e x s) 0 := by
    simp only [modeField]
    fun_prop
  have h0 : modeField D ω e x 0 = modeDatum ω e x := by
    simp [modeField, modeDatum, Real.exp_zero]
  have ht := hc.tendsto
  rw [h0] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- **The mode feeds the port**: for any resonant frequency, the
single Fourier mode is a global periodic solution attaining the
nonconstant datum `cos (ω·x) • e` — elementary calculus, no semigroup,
any `D`, any window. -/
theorem portFeed_mode (M : RingMesh) (D : ℝ) (T : Set ℝ) (e : E)
    {ω : ℝ} (k : ℤ) (hω : ω * M.L = k * (2 * Real.pi)) :
    PortFeed M D T (modeDatum ω e) :=
  ⟨modeField D ω e,
    ⟨fun t => modeField_periodic D ω e hω t,
      fun x _ t _ => heatAt_mode D ω e x t⟩,
    fun x _ => modeField_trace D ω e T x⟩

/-- The mode's datum is genuinely non-equilibrium: it separates two
points whenever the mode is honest (`e ≠ 0`, `ω ≠ 0`) — the feed
theorem is not secretly about constants. -/
theorem modeDatum_ne_const {e : E} (he : e ≠ 0) {ω : ℝ} (hω : ω ≠ 0) :
    modeDatum ω e (ω⁻¹ * (Real.pi / 2)) ≠ modeDatum ω e 0 := by
  have harg : ω * (ω⁻¹ * (Real.pi / 2)) = Real.pi / 2 := by
    rw [← mul_assoc, mul_inv_cancel₀ hω, one_mul]
  simp only [modeDatum, harg, mul_zero, Real.cos_zero, one_smul,
    Real.cos_pi_div_two, zero_smul]
  exact fun h => he h.symm

/-! ## The port is load-bearing -/

/-- A record satisfying every mesh atom refuses a mismatched port
atom: the six-atom family does not pin traces.  Consumes the filter
fee, like every uniqueness argument at the face. -/
theorem not_init1_const {M : RingMesh} {T : Set ℝ} {k : E} (hk : k ≠ 0)
    (hne : (𝓝[T] (0 : ℝ)).NeBot) :
    constRec k ∉ init1C M T (fun _ => (0 : E)) := by
  intro hmem
  haveI := hne
  have h0 : (0 : ℝ) ∈ M.I1 := by
    constructor
    · have := M.hδ
      linarith
    · have := M.ha
      have := M.hδ
      linarith
  have htr : Filter.Tendsto (fun _ : ℝ => k) (𝓝[T] (0 : ℝ)) (𝓝 (0 : E)) :=
    hmem 0 h0
  have hconst : Filter.Tendsto (fun _ : ℝ => k) (𝓝[T] (0 : ℝ)) (𝓝 k) :=
    tendsto_const_nhds
  exact hk (tendsto_nhds_unique hconst htr)

/-- The square-level statement of the same fact: the constant record's
Dirac passes the whole six-atom mesh family and refuses the ported
family for a mismatched datum — the port atoms are load-bearing at
statement level. -/
theorem heatAtoms_not_pin_port (M : RingMesh) (D : ℝ) (T : Set ℝ)
    (hne : (𝓝[T] (0 : ℝ)).NeBot) {k : E} (hk : k ≠ 0) :
    looseConj (heatAtoms M D T) (SubPMF.dirac (constRec k)) ∧
      ¬ looseConj (heatInitAtoms M D T (fun _ => (0 : E)))
        (SubPMF.dirac (constRec k)) := by
  constructor
  · rw [heatAtoms_iff]
    exact (suppC_dirac _ _).mpr (isMeshSol_const k)
  · intro hcon
    rw [heatInitAtoms_iff] at hcon
    have hmem := (suppC_dirac _ _).mp hcon
    exact not_init1_const hk hne hmem.trace1

end Adequacy
end SuFunctor

#print axioms SuFunctor.Adequacy.initFace_wrap_compat
#print axioms SuFunctor.Adequacy.heatInitAtoms_iff
#print axioms SuFunctor.Adequacy.meshInitSols_eq_classical
#print axioms SuFunctor.Adequacy.heat_init_adequacy
#print axioms SuFunctor.Adequacy.heatInitAtoms_consistent_of_feed
#print axioms SuFunctor.Adequacy.portFeed_const
#print axioms SuFunctor.Adequacy.portFeed_mode
#print axioms SuFunctor.Adequacy.modeDatum_ne_const
#print axioms SuFunctor.Adequacy.heatAtoms_not_pin_port
