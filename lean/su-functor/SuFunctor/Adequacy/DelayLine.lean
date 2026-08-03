import SuFunctor.Adequacy.Inclusions
import Mathlib.Analysis.Calculus.MeanValue

/-! # Adequacy: the ideal delay line, and delay differential equations
as a wiring pattern

The first adequacy square with a spatially extended cell.  An *ideal
delay line* is the transport equation `∂ₜu + c ∂ₓu = 0` on a segment of
length `c·τ` — the idealization of the mercury acoustic delay-line
memory of the earliest stored-program computers: samples enter at one
end, travel at speed `c`, and emerge unchanged a time `τ` later.  Wired
to an ordinary differential equation cell through three interface
wires — an initial *load* wire placing the history on the line, an
*inflow* trace wire feeding the cell's state into the upstream end, and
an *outflow* tap reading the downstream end into the cell's vector
field — the composite's trajectories are exactly the solutions of the
delay differential equation `ẏ(t) = f(y(t), y(t−τ))` in the classical
sense (Hale–Verduyn Lunel, *Introduction to Functional Differential
Equations*, Ch. 2).  Delay equations thus enter the semantic universe
as a **wiring pattern** over cells the universe already has, not as a
new formalism; the famous "infinite-dimensional state" of a delay
equation — the history segment `y|[t−τ,t]` — is nothing but the field
on the spatial cell, read along characteristics
(`IsCompositeSol.field_slice_is_history`).

Design notes, load-bearing:

* **Dynamics are constraint rows, never a solution operator.**  The
  transport cell's dynamics (`IsTransportSol`) says only: along each
  characteristic of the cylinder, the field's trace is continuous with
  vanishing derivative *within the trace's own window* — the germ of
  the PDE along its characteristic flow.  The solution operator (the
  time-`s` shift semigroup on histories that the functional-analytic
  DDE literature takes as primitive) appears nowhere in the
  presentation; it is *derived* content of the left edge
  (`IsTransportSol.trace_const`, `isTransportSol_reparam` — the method
  of characteristics, as an equivalence).  This is why the square
  closes with elementary one-variable calculus: characteristics reduce
  the left edge to the mean value theorem, with no Sobolev or
  semigroup machinery anywhere.
* **Wires are directional.**  The upstream end of the line is *pinned*
  (a Dirichlet trace constraint, `InflowClause`); the downstream end is
  *read* (`OutflowClause` constrains the tap signal, not the field).
  This matches the dependence structure of the transport operator:
  characteristics enter at the inflow face and the initial face, and
  those are exactly the faces the wiring constrains.  Pinning both
  ends would generically yield an unsatisfiable composite.
* **No method of steps.**  The correspondence
  (`composite_iff_dde`) is proved uniformly in `t` by one
  characteristics argument; stepwise construction is an *existence*
  technique, and the square does not owe existence.  Satisfiability of
  the compiled constraints is a separate, judgment-level matter
  (`composite_const` witnesses it constructively for equilibria; the
  compiled atoms themselves never exclude the vacuous model,
  `suppC_zero` — the existential commitment lives in the judgment, not
  the constraint stratum).
* **The record-level square is two-sided.**  For general PDE cells the
  per-mesh feeding lemma is one-sided (compiled rows are implied by
  weak-solution-hood, with the equivalence recovered only in the mesh
  limit).  For the delay line the left edge is total *today*, so
  `delayline_adequacy` is an isomorphism of loose arrows at the
  possibilistic stratum: the conjunction of the five compiled atoms
  (two cells, three wires) is equivalent to the support-inclusion of
  the classical solution set.  A deterministic frame never pins mass —
  the constraint class is closed under sub-mass and mixtures, so the
  bottom edge is the demonic inclusion of the solution *set*, with the
  per-solution Dirac face (`diracC_recOf_entails`) recovering the
  pointwise deterministic inclusion.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Set Topology

universe u

/-! ## The transport cell

The spatial cell is the segment `[0, c·τ]`; spacetime is the cylinder
`[0, c·τ] × [0, ∞)`.  The characteristic with *launch coordinate* `ζ`
(the time at which it crosses, or would cross, the upstream face
`x = 0`) traverses `s ↦ (c·(s − ζ), s)`, staying inside the cylinder
for `s ∈ [max ζ 0, ζ + τ]`; every point `(x, t)` of the cylinder lies
on exactly one such characteristic, the one with
`ζ = t − x/c ∈ [−τ, ∞)`. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The trace of a field along the characteristic with launch
coordinate `ζ`: the field's values as seen by an observer riding the
characteristic. -/
def charTrace (c : ℝ) (u : ℝ → ℝ → E) (ζ : ℝ) : ℝ → E :=
  fun s => u (c * (s - ζ)) s

/-- The time window a characteristic with launch coordinate `ζ` spends
inside the cylinder. -/
abbrev charDom (τ ζ : ℝ) : Set ℝ := Icc (max ζ 0) (ζ + τ)

/-- The transport cell's dynamics and record class, as constraints on
the field: along each characteristic of the cylinder, the trace is
continuous and has vanishing derivative within its window.  This is
the constraint-row form of `∂ₜu + c ∂ₓu = 0`: the differential
statement along the characteristic flow, mentioning only the field's
values on the cell. -/
structure IsTransportSol (c τ : ℝ) (u : ℝ → ℝ → E) : Prop where
  /-- Trace continuity: the field's record class along characteristics. -/
  cont : ∀ ζ ∈ Ici (-τ), ContinuousOn (charTrace c u ζ) (charDom τ ζ)
  /-- The transport equation, along characteristics. -/
  deriv : ∀ ζ ∈ Ici (-τ), ∀ s ∈ charDom τ ζ,
    HasDerivWithinAt (charTrace c u ζ) 0 (charDom τ ζ) s

namespace IsTransportSol

/-- The within-window derivative rows lift to the forward-window form
the mean value theorem consumes. -/
theorem deriv_Ici {c τ : ℝ} {u : ℝ → ℝ → E} (h : IsTransportSol c τ u)
    {ζ : ℝ} (hζ : ζ ∈ Ici (-τ)) {s : ℝ}
    (hs : s ∈ Ico (max ζ 0) (ζ + τ)) :
    HasDerivWithinAt (charTrace c u ζ) 0 (Ici s) s := by
  refine (h.deriv ζ hζ s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin ?_
  have h1 : Ici s ∩ Iic (ζ + τ) ∈ 𝓝[Ici s] s :=
    inter_mem_nhdsWithin _ (Iic_mem_nhds hs.2)
  exact Filter.mem_of_superset h1 fun _ hr => ⟨le_trans hs.1 hr.1, hr.2⟩

/-- **Constancy along characteristics** — the left edge's engine.  The
constraint rows pin every characteristic trace to its entry value, by
the one-variable mean value theorem.  No PDE machinery is consumed:
this is the whole content of the method of characteristics for the
ideal delay line. -/
theorem trace_const {c τ : ℝ} {u : ℝ → ℝ → E} (h : IsTransportSol c τ u)
    {ζ : ℝ} (hζ : ζ ∈ Ici (-τ)) {s : ℝ} (hs : s ∈ charDom τ ζ) :
    charTrace c u ζ s = charTrace c u ζ (max ζ 0) :=
  constant_of_has_deriv_right_zero (h.cont ζ hζ)
    (fun _ hr => h.deriv_Ici hζ hr) s hs

end IsTransportSol

/-- Cylinder points have launch coordinates in the window `[−τ, ∞)`. -/
theorem zeta_mem {c τ x t : ℝ} (hc : 0 < c) (hx : x ∈ Icc 0 (c * τ))
    (ht : t ∈ Ici (0 : ℝ)) : t - x / c ∈ Ici (-τ) := by
  have hxc : x / c ≤ τ := by rw [div_le_iff₀ hc, mul_comm]; exact hx.2
  have ht' : (0 : ℝ) ≤ t := ht
  simp only [mem_Ici]
  linarith

/-- A cylinder point's time lies in its own characteristic's window. -/
theorem t_mem_charDom {c τ x t : ℝ} (hc : 0 < c) (hx : x ∈ Icc 0 (c * τ))
    (ht : t ∈ Ici (0 : ℝ)) : t ∈ charDom τ (t - x / c) := by
  have hxc : x / c ≤ τ := by rw [div_le_iff₀ hc, mul_comm]; exact hx.2
  have hxc0 : 0 ≤ x / c := div_nonneg hx.1 hc.le
  have ht' : (0 : ℝ) ≤ t := ht
  exact ⟨max_le (by linarith) ht', by linarith⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reading the characteristic trace at a cylinder point returns the
field there. -/
theorem charTrace_cylinder {c : ℝ} {x t : ℝ} (hc : 0 < c) (u : ℝ → ℝ → E) :
    charTrace c u (t - x / c) t = u x t := by
  have hx' : c * (t - (t - x / c)) = x := by
    have hc' : c ≠ 0 := hc.ne'
    field_simp
    ring
  show u (c * (t - (t - x / c))) t = u x t
  rw [hx']

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A characteristic launched at `ζ ≥ 0` enters through the inflow
face. -/
theorem charTrace_entry_nonneg {c : ℝ} {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (u : ℝ → ℝ → E) : charTrace c u ζ (max ζ 0) = u 0 ζ := by
  rw [max_eq_left hζ0]
  show u (c * (ζ - ζ)) ζ = u 0 ζ
  rw [sub_self, mul_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A characteristic launched at `ζ ≤ 0` enters through the initial
face. -/
theorem charTrace_entry_nonpos {c : ℝ} {ζ : ℝ} (hζ0 : ζ ≤ 0)
    (u : ℝ → ℝ → E) : charTrace c u ζ (max ζ 0) = u (c * (0 - ζ)) 0 := by
  rw [max_eq_right hζ0]
  rfl

/-! ## The ODE cell, the concatenation, and the classical DDE -/

/-- An ODE cell with state `y`, input signal `z`, and initial value
`y₀`: the forward-derivative form of `ẏ = f(y, z)` on `[0, ∞)`. -/
structure IsOdeCell (f : E → E → E) (y₀ : E) (y z : ℝ → E) : Prop where
  init : y 0 = y₀
  cont : ContinuousOn y (Ici 0)
  deriv : ∀ t ∈ Ici 0, HasDerivWithinAt y (f (y t) (z t)) (Ici t) t

/-- The concatenation of a history and a continuation at time `0`. -/
noncomputable def concat (φ y : ℝ → E) : ℝ → E :=
  fun t => if t < 0 then φ t else y t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem concat_of_neg {φ y : ℝ → E} {t : ℝ} (h : t < 0) :
    concat φ y t = φ t := if_pos h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem concat_of_nonneg {φ y : ℝ → E} {t : ℝ} (h : 0 ≤ t) :
    concat φ y t = y t := if_neg (not_lt.mpr h)

omit [NormedSpace ℝ E] in
/-- The pasting: a continuous history and a continuous continuation
agreeing at `0` concatenate to a continuous function on `[−τ, ∞)`. -/
theorem continuousOn_concat {τ : ℝ} (hτ : 0 < τ) {φ y : ℝ → E}
    (hφ : ContinuousOn φ (Icc (-τ) 0)) (hy : ContinuousOn y (Ici 0))
    (h0 : y 0 = φ 0) : ContinuousOn (concat φ y) (Ici (-τ)) := by
  have hneg : -τ ≤ (0 : ℝ) := by linarith
  rw [← Icc_union_Ici_eq_Ici hneg]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Ici
  · refine hφ.congr fun t ht => ?_
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact concat_of_neg h
    · subst h
      rw [concat_of_nonneg le_rfl, h0]
  · exact hy.congr fun t ht => concat_of_nonneg ht

/-- A solution of the delay differential equation
`ẏ(t) = f(y(t), y(t−τ))` with history `φ`, as the classical literature
presents it (Hale–Verduyn Lunel, Ch. 2): a function on `[−τ, ∞)`
agreeing with the history on `[−τ, 0]`, continuous, with forward
derivative `f(Y(t), Y(t−τ))` at every `t ≥ 0`. -/
structure IsDdeSol (f : E → E → E) (τ : ℝ) (φ Y : ℝ → E) : Prop where
  hist : ∀ t ∈ Icc (-τ) 0, Y t = φ t
  cont : ContinuousOn Y (Ici (-τ))
  deriv : ∀ t ∈ Ici 0, HasDerivWithinAt Y (f (Y t) (Y (t - τ))) (Ici t) t

/-! ## The wires and the composite -/

/-- The load wire: the history is placed on the line at time `0`,
oldest samples farthest downstream. -/
def LoadClause (c τ : ℝ) (φ : ℝ → E) (u : ℝ → ℝ → E) : Prop :=
  ∀ x ∈ Icc 0 (c * τ), u x 0 = φ (-(x / c))

/-- The inflow wire: the ODE cell's state is pinned to the upstream
trace — a Dirichlet trace constraint on the *inflow* face, which is
where the transport operator's characteristics enter. -/
def InflowClause (y : ℝ → E) (u : ℝ → ℝ → E) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), u 0 t = y t

/-- The outflow tap: the wire signal reads the downstream trace.  Note
the directionality — this constrains the *tap*, not the field: the
downstream face of a transport cell is read, never pinned. -/
def OutflowClause (c τ : ℝ) (z : ℝ → E) (u : ℝ → ℝ → E) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), z t = u (c * τ) t

/-- The delay-line composite: an ODE cell and a transport cell of
length `c·τ`, joined by the three wires.  The five fields are the five
compiled constraint atoms of the square (`delayAtoms`). -/
structure IsCompositeSol (f : E → E → E) (c τ : ℝ) (φ : ℝ → E)
    (y z : ℝ → E) (u : ℝ → ℝ → E) : Prop where
  transport : IsTransportSol c τ u
  ode : IsOdeCell f (φ 0) y z
  load : LoadClause c τ φ u
  inflow : InflowClause y u
  outflow : OutflowClause c τ z u

namespace IsCompositeSol

variable {f : E → E → E} {c τ : ℝ} {φ y z : ℝ → E} {u : ℝ → ℝ → E}

/-- **The trace identification.**  On the cylinder, the field is the
concatenated history-and-state read along characteristics: every
sample on the line is the boundary datum that launched it. -/
theorem field_eq (hc : 0 < c) (h : IsCompositeSol f c τ φ y z u) :
    ∀ x ∈ Icc 0 (c * τ), ∀ t ∈ Ici (0 : ℝ),
      u x t = concat φ y (t - x / c) := by
  intro x hx t ht
  have hζ : t - x / c ∈ Ici (-τ) := zeta_mem hc hx ht
  have hmem : t ∈ charDom τ (t - x / c) := t_mem_charDom hc hx ht
  have h1 : u x t = charTrace c u (t - x / c) (max (t - x / c) 0) := by
    rw [← charTrace_cylinder hc u]
    exact h.transport.trace_const hζ hmem
  rcases le_or_gt 0 (t - x / c) with hζ0 | hζ0
  · rw [h1, charTrace_entry_nonneg hζ0, h.inflow _ hζ0,
      concat_of_nonneg hζ0]
  · rw [h1, charTrace_entry_nonpos hζ0.le]
    have hζτ : -τ ≤ t - x / c := hζ
    have hx' : c * (0 - (t - x / c)) ∈ Icc 0 (c * τ) := by
      constructor
      · exact mul_nonneg hc.le (by linarith)
      · exact mul_le_mul_of_nonneg_left (by linarith) hc.le
    rw [h.load _ hx']
    have h3 : c * (0 - (t - x / c)) / c = -(t - x / c) := by
      rw [mul_comm, mul_div_assoc, div_self hc.ne', mul_one]
      ring
    rw [h3, neg_neg, concat_of_neg hζ0]

/-- **The transport cell is the delay operator**: the outflow tap
carries the concatenated signal delayed by exactly `τ`. -/
theorem outflow_delay (hc : 0 < c) (hτ : 0 < τ)
    (h : IsCompositeSol f c τ φ y z u) :
    ∀ t ∈ Ici (0 : ℝ), z t = concat φ y (t - τ) := by
  intro t ht
  have hend : (c * τ) ∈ Icc 0 (c * τ) := ⟨mul_nonneg hc.le hτ.le, le_rfl⟩
  rw [h.outflow t ht, h.field_eq hc _ hend t ht]
  congr 1
  rw [mul_comm, mul_div_assoc, div_self hc.ne', mul_one]

/-- **The history segment is the field on the spatial cell.**  At each
time `t`, the spatial slice of the field carries exactly the
trajectory's history segment over `[t−τ, t]`, read through the
characteristic reparameterization `s ↦ c·(t−s)`: the delay equation's
"infinite-dimensional state" is a spatial record, not a new semantic
species. -/
theorem field_slice_is_history (hc : 0 < c)
    (h : IsCompositeSol f c τ φ y z u) {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    ∀ s ∈ Icc (t - τ) t, u (c * (t - s)) t = concat φ y s := by
  intro s hs
  have hx : c * (t - s) ∈ Icc 0 (c * τ) := by
    constructor
    · exact mul_nonneg hc.le (by linarith [hs.2])
    · exact mul_le_mul_of_nonneg_left (by linarith [hs.1]) hc.le
  rw [h.field_eq hc _ hx t ht]
  congr 1
  have h1 : c * (t - s) / c = t - s := by
    rw [mul_comm, mul_div_assoc, div_self hc.ne', mul_one]
  rw [h1]
  ring

/-- Forward direction of the wiring theorem: a composite trajectory's
concatenated path is a classical DDE solution. -/
theorem toDde (hc : 0 < c) (hτ : 0 < τ)
    (hφ : ContinuousOn φ (Icc (-τ) 0))
    (h : IsCompositeSol f c τ φ y z u) :
    IsDdeSol f τ φ (concat φ y) where
  hist := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h0 | h0
    · exact concat_of_neg h0
    · subst h0
      rw [concat_of_nonneg le_rfl, h.ode.init]
  cont := continuousOn_concat hτ hφ h.ode.cont h.ode.init
  deriv := by
    intro t ht
    have hval : f (concat φ y t) (concat φ y (t - τ)) = f (y t) (z t) := by
      rw [concat_of_nonneg ht, ← h.outflow_delay hc hτ t ht]
    rw [hval]
    exact (h.ode.deriv t ht).congr
      (fun s hs => concat_of_nonneg (le_trans ht hs)) (concat_of_nonneg ht)

end IsCompositeSol

/-- The converse half of the left edge: a field that reads a
continuous signal along characteristics satisfies the transport rows
(each trace is constant, so its derivative vanishes). -/
theorem isTransportSol_reparam {c τ : ℝ} (hc : 0 < c) {w : ℝ → E}
    {u : ℝ → ℝ → E}
    (hu : ∀ x ∈ Icc 0 (c * τ), ∀ t ∈ Ici (0 : ℝ), u x t = w (t - x / c)) :
    IsTransportSol c τ u := by
  have key : ∀ ζ ∈ Ici (-τ),
      EqOn (charTrace c u ζ) (fun _ => w ζ) (charDom τ ζ) := by
    intro ζ hζ s hs
    have hζτ : -τ ≤ ζ := hζ
    have hζs : ζ ≤ s := le_trans (le_max_left _ _) hs.1
    have h0s : (0 : ℝ) ≤ s := le_trans (le_max_right _ _) hs.1
    have hsτ : s ≤ ζ + τ := hs.2
    have hx : c * (s - ζ) ∈ Icc 0 (c * τ) := by
      constructor
      · exact mul_nonneg hc.le (by linarith)
      · exact mul_le_mul_of_nonneg_left (by linarith) hc.le
    have h1 : charTrace c u ζ s = w (s - c * (s - ζ) / c) := hu _ hx s h0s
    have h2 : s - c * (s - ζ) / c = ζ := by
      rw [mul_comm, mul_div_assoc, div_self hc.ne', mul_one]
      ring
    show charTrace c u ζ s = w ζ
    rw [h1, h2]
  exact
    { cont := fun ζ hζ => continuousOn_const.congr (key ζ hζ)
      deriv := fun ζ hζ s hs =>
        (hasDerivWithinAt_const s _ (w ζ)).congr_of_mem
          (fun r hr => key ζ hζ hr) hs }

/-- The record-matching relation: a triple of total functions presents
a classical solution `Y` when it agrees with `Y`'s canonical reads on
the composite's domains.  (Records live over domains; the off-domain
coordinates of a total-function chart are not observables, so the
classical inclusion includes up to off-domain modification.) -/
structure RecMatches (c τ : ℝ) (Y : ℝ → E) (y z : ℝ → E)
    (u : ℝ → ℝ → E) : Prop where
  path : ∀ t ∈ Ici (0 : ℝ), y t = Y t
  tap : ∀ t ∈ Ici (0 : ℝ), z t = Y (t - τ)
  field : ∀ x ∈ Icc 0 (c * τ), ∀ t ∈ Ici (0 : ℝ), u x t = Y (t - x / c)

/-- Backward direction of the wiring theorem: any record matching a
classical DDE solution satisfies the composite's five constraints. -/
theorem composite_of_dde {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) {Y : ℝ → E} (hY : IsDdeSol f τ φ Y)
    {y z : ℝ → E} {u : ℝ → ℝ → E} (hm : RecMatches c τ Y y z u) :
    IsCompositeSol f c τ φ y z u where
  transport := isTransportSol_reparam hc hm.field
  ode :=
    { init := by
        have h0 : y 0 = Y 0 := hm.path 0 self_mem_Ici
        have h1 : Y 0 = φ 0 := hY.hist 0 ⟨by linarith, le_rfl⟩
        rw [h0, h1]
      cont := by
        refine (hY.cont.mono fun t ht => ?_).congr fun t ht => hm.path t ht
        have ht' : (0 : ℝ) ≤ t := ht
        show -τ ≤ t
        linarith
      deriv := by
        intro t ht
        have hval : f (y t) (z t) = f (Y t) (Y (t - τ)) := by
          rw [hm.path t ht, hm.tap t ht]
        rw [hval]
        refine (hY.deriv t ht).congr
          (fun s hs => hm.path s ?_) (hm.path t ht)
        have hts : t ≤ s := hs
        have ht0 : (0 : ℝ) ≤ t := ht
        exact mem_Ici.mpr (le_trans ht0 hts) }
  load := by
    intro x hx
    have hxc : x / c ≤ τ := by rw [div_le_iff₀ hc, mul_comm]; exact hx.2
    have hxc0 : 0 ≤ x / c := div_nonneg hx.1 hc.le
    have h1 : u x 0 = Y (0 - x / c) := hm.field x hx 0 self_mem_Ici
    have h2 : Y (-(x / c)) = φ (-(x / c)) :=
      hY.hist _ ⟨by linarith, by linarith⟩
    rw [h1, zero_sub, h2]
  inflow := by
    intro t ht
    have h1 : u 0 t = Y (t - 0 / c) :=
      hm.field 0 ⟨le_rfl, mul_nonneg hc.le hτ.le⟩ t ht
    rw [h1, zero_div, sub_zero, hm.path t ht]
  outflow := by
    intro t ht
    have h1 : u (c * τ) t = Y (t - c * τ / c) :=
      hm.field (c * τ) ⟨mul_nonneg hc.le hτ.le, le_rfl⟩ t ht
    have h2 : t - c * τ / c = t - τ := by
      rw [mul_comm, mul_div_assoc, div_self hc.ne', mul_one]
    rw [hm.tap t ht, h1, h2]

/-- **The wiring-pattern theorem.**  The delay-line composite's
trajectories are exactly the records of classical DDE solutions: an
ODE cell wired through a transport cell *is* the delay differential
equation `ẏ(t) = f(y(t), y(t−τ))`, with the correspondence uniform in
`t` (no method of steps) and two-sided (the left edge is total). -/
theorem composite_iff_dde {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) (hφ : ContinuousOn φ (Icc (-τ) 0))
    {y z : ℝ → E} {u : ℝ → ℝ → E} :
    IsCompositeSol f c τ φ y z u ↔
      ∃ Y, IsDdeSol f τ φ Y ∧ RecMatches c τ Y y z u := by
  constructor
  · intro h
    refine ⟨concat φ y, h.toDde hc hτ hφ, ?_, ?_, ?_⟩
    · exact fun t ht => (concat_of_nonneg ht).symm
    · exact fun t ht => h.outflow_delay hc hτ t ht
    · exact fun x hx t ht => h.field_eq hc x hx t ht
  · rintro ⟨Y, hY, hm⟩
    exact composite_of_dde hc hτ hY hm

/-- The ODE-record projection: existentially over the line and the
tap, the composite's path records are exactly the classical solutions
(restricted to the cell's window). -/
theorem composite_path_proj {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) (hφ : ContinuousOn φ (Icc (-τ) 0))
    {y : ℝ → E} :
    (∃ z u, IsCompositeSol f c τ φ y z u) ↔
      ∃ Y, IsDdeSol f τ φ Y ∧ ∀ t ∈ Ici (0 : ℝ), y t = Y t := by
  constructor
  · rintro ⟨z, u, h⟩
    obtain ⟨Y, hY, hm⟩ := (composite_iff_dde hc hτ hφ).mp h
    exact ⟨Y, hY, hm.path⟩
  · rintro ⟨Y, hY, hy⟩
    refine ⟨fun t => Y (t - τ), fun x t => Y (t - x / c), ?_⟩
    exact (composite_iff_dde hc hτ hφ).mpr
      ⟨Y, hY, hy, fun t _ => rfl, fun x _ t _ => rfl⟩

/-! ## The square

The compiled presentation is five constraint atoms on the composite's
record space — two cells and three wires, mirroring the wiring diagram
clause for clause — each read at the possibilistic stratum: a model
satisfies an atom when every record it deems possible satisfies the
clause.  The classical semantics is the DDE solution set, included as
the support constraint of its record presentations.  The square is an
isomorphism of loose arrows, two-sided because the delay line's left
edge (characteristics) is total. -/

/-- The possibilistic (support) constraint: every outcome the model
deems possible lies in `P`.  This is the constraint-stratum reading of
a deterministic-but-possibly-nonunique system: the denotation of a
solution *set*, closed under sub-mass and mixtures.  Note it never
excludes the vacuous model (`suppC_zero`): existential commitment is
judgment-level content, not constraint-level content. -/
def suppC {V : Type u} (P : Set V) : SubPMF V → Prop :=
  fun μ => ∀ v, μ.wt v ≠ 0 → v ∈ P

theorem suppC_zero {V : Type u} (P : Set V) : suppC P (SubPMF.zero V) :=
  fun _ hv => absurd (by simp [SubPMF.zero]) hv

/-- On a point mass, the support constraint is membership: the
per-solution face of the set-valued inclusion. -/
theorem suppC_dirac {V : Type u} (P : Set V) (v : V) :
    suppC P (SubPMF.dirac v) ↔ v ∈ P := by
  classical
  constructor
  · intro h
    refine h v ?_
    show (Finsupp.single v (1 : ℚ)) v ≠ 0
    simp
  · intro hv w hw
    by_cases hwv : w = v
    · rwa [hwv]
    · exfalso
      apply hw
      show (Finsupp.single v (1 : ℚ)) w = 0
      exact Finsupp.single_eq_of_ne hwv

/-- The composite's record space: the ODE cell's path, the outflow
wire's signal, the transport cell's field. -/
structure DelayRec (E : Type) where
  path : ℝ → E
  tap : ℝ → E
  field : ℝ → ℝ → E

/-- The transport cell's constraint set. -/
def transportC (c τ : ℝ) : Set (DelayRec E) :=
  {p | IsTransportSol c τ p.field}

/-- The ODE cell's constraint set (dynamics, record class, initial
row). -/
def odeCellC (f : E → E → E) (φ : ℝ → E) : Set (DelayRec E) :=
  {p | IsOdeCell f (φ 0) p.path p.tap}

/-- The load wire's constraint set. -/
def loadC (c τ : ℝ) (φ : ℝ → E) : Set (DelayRec E) :=
  {p | LoadClause c τ φ p.field}

/-- The inflow wire's constraint set. -/
def inflowC : Set (DelayRec E) :=
  {p | InflowClause p.path p.field}

/-- The outflow tap's constraint set. -/
def outflowC (c τ : ℝ) : Set (DelayRec E) :=
  {p | OutflowClause c τ p.tap p.field}

/-- The compiled constraint atoms of the delay-line composite: two
cells and three wires, one support atom each.  The list *is* the
wiring diagram, read as a loose-arrow diagram of `Crd (DelayRec E)`. -/
def delayAtoms (f : E → E → E) (c τ : ℝ) (φ : ℝ → E) :
    List (SubPMF (DelayRec E) → Prop) :=
  [suppC (transportC c τ), suppC (odeCellC f φ), suppC (loadC c τ φ),
    suppC inflowC, suppC (outflowC c τ)]

/-- The composite's solution set, as a set of records. -/
def compositeSols (f : E → E → E) (c τ : ℝ) (φ : ℝ → E) :
    Set (DelayRec E) :=
  {p | IsCompositeSol f c τ φ p.path p.tap p.field}

/-- The classical object's record presentations: records matching some
classical DDE solution on the composite's domains. -/
def classicalRecs (f : E → E → E) (c τ : ℝ) (φ : ℝ → E) :
    Set (DelayRec E) :=
  {p | ∃ Y, IsDdeSol f τ φ Y ∧ RecMatches c τ Y p.path p.tap p.field}

/-- Bundling: the conjunction of the five atoms is the support
constraint of the composite solution set — the wiring diagram's
conjunction, taken once, at the mesh-joint. -/
theorem delayAtoms_iff (f : E → E → E) (c τ : ℝ) (φ : ℝ → E)
    (μ : SubPMF (DelayRec E)) :
    looseConj (delayAtoms f c τ φ) μ ↔
      suppC (compositeSols f c τ φ) μ := by
  simp only [delayAtoms, looseConj, suppC]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, -⟩ p hp
    exact ⟨h1 p hp, h2 p hp, h3 p hp, h4 p hp, h5 p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).transport, fun p hp => (h p hp).ode,
      fun p hp => (h p hp).load, fun p hp => (h p hp).inflow,
      fun p hp => (h p hp).outflow, trivial⟩

/-- The wiring theorem in set form: composite solutions are exactly
the classical records. -/
theorem compositeSols_eq_classical {f : E → E → E} {c τ : ℝ}
    {φ : ℝ → E} (hc : 0 < c) (hτ : 0 < τ)
    (hφ : ContinuousOn φ (Icc (-τ) 0)) :
    compositeSols f c τ φ = classicalRecs f c τ φ :=
  Set.ext fun _ => composite_iff_dde hc hτ hφ

/-- **The delay-line adequacy square.**  Compiling the wiring diagram
to its five constraint atoms and denoting agrees with interpreting the
delay equation classically and including its solution set at the
possibilistic stratum: an invertible globular cell of
`Crd (DelayRec E)`.  Two-sided — the delay line is the transport
instance whose left edge (the method of characteristics) is total
today. -/
theorem delayline_adequacy (f : E → E → E) {c τ : ℝ} (hc : 0 < c)
    (hτ : 0 < τ) {φ : ℝ → E} (hφ : ContinuousOn φ (Icc (-τ) 0))
    {a : Crd (DelayRec E)} :
    ∃ α : Cell (looseConj (delayAtoms f c τ φ) : Loose a a)
        (suppC (classicalRecs f c τ φ)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [delayAtoms_iff, compositeSols_eq_classical hc hτ hφ]

/-! ## The per-solution (Dirac) face and the properness witnesses -/

/-- The canonical record of a classical solution: the solution itself,
its delayed read, and its characteristic extension onto the line. -/
noncomputable def recOf (c τ : ℝ) (Y : ℝ → E) : DelayRec E :=
  ⟨Y, fun t => Y (t - τ), fun x t => Y (t - x / c)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem recMatches_recOf (c τ : ℝ) (Y : ℝ → E) :
    RecMatches c τ Y (recOf c τ Y).path (recOf c τ Y).tap
      (recOf c τ Y).field :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem recOf_mem_compositeSols {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) (hφ : ContinuousOn φ (Icc (-τ) 0))
    {Y : ℝ → E} (hY : IsDdeSol f τ φ Y) :
    recOf c τ Y ∈ compositeSols f c τ φ :=
  (composite_iff_dde hc hτ hφ).mpr ⟨Y, hY, recMatches_recOf c τ Y⟩

/-- The per-solution Dirac face: each classical solution's point mass
satisfies the compiled atoms. -/
theorem delayAtoms_dirac_of_dde {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) (hφ : ContinuousOn φ (Icc (-τ) 0))
    {Y : ℝ → E} (hY : IsDdeSol f τ φ Y) :
    looseConj (delayAtoms f c τ φ) (SubPMF.dirac (recOf c τ Y)) :=
  (delayAtoms_iff f c τ φ _).mpr
    ((suppC_dirac _ _).mpr (recOf_mem_compositeSols hc hτ hφ hY))

/-- The deterministic inclusion entails the compiled constraints, per
solution: the `diracC` bottom edge at the per-solution grain. -/
theorem diracC_recOf_entails {f : E → E → E} {c τ : ℝ} {φ : ℝ → E}
    (hc : 0 < c) (hτ : 0 < τ) (hφ : ContinuousOn φ (Icc (-τ) 0))
    {Y : ℝ → E} (hY : IsDdeSol f τ φ Y) :
    ∀ μ : SubPMF (DelayRec E), diracC (recOf c τ Y) μ →
      looseConj (delayAtoms f c τ φ) μ := by
  intro μ hμ
  have hμ' : μ = SubPMF.dirac (recOf c τ Y) := hμ
  rw [hμ']
  exact delayAtoms_dirac_of_dde hc hτ hφ hY

/-- Equilibria are transport solutions (the constant field). -/
theorem isTransportSol_const (c τ : ℝ) (k : E) :
    IsTransportSol c τ (fun _ _ => k) where
  cont := fun _ _ => continuousOn_const
  deriv := fun _ _ s _ => hasDerivWithinAt_const s _ k

/-- Equilibria solve the DDE: the constant function at a fixed point
of the closed loop. -/
theorem isDdeSol_const {f : E → E → E} {τ : ℝ} (k : E)
    (hk : f k k = 0) : IsDdeSol f τ (fun _ => k) (fun _ => k) where
  hist := fun _ _ => rfl
  cont := continuousOn_const
  deriv := fun t _ => by
    show HasDerivWithinAt (fun _ => k) (f k k) (Ici t) t
    rw [hk]
    exact hasDerivWithinAt_const t _ k

/-- The constructive properness witness: at an equilibrium of the
closed loop, the constant record solves the composite — the compiled
constraint class is inhabited by more than the vacuous model, so the
judgment-level existential commitment is dischargeable. -/
theorem composite_const {f : E → E → E} {c τ : ℝ} (k : E)
    (hk : f k k = 0) :
    IsCompositeSol f c τ (fun _ => k) (fun _ => k) (fun _ => k)
      (fun _ _ => k) where
  transport := isTransportSol_const c τ k
  ode :=
    { init := rfl
      cont := continuousOn_const
      deriv := fun t _ => by
        show HasDerivWithinAt (fun _ => k) (f k k) (Ici t) t
        rw [hk]
        exact hasDerivWithinAt_const t _ k }
  load := fun _ _ => rfl
  inflow := fun _ _ => rfl
  outflow := fun _ _ => rfl

end Adequacy
end SuFunctor
