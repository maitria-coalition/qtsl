import SuFunctor.Adequacy.DelayLine
import SuFunctor.Adequacy.SemanticUniverseWiring
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Adequacy: ordinary differential equations

The adequacy square for the autonomous initial-value problem
`ẏ = f(y)`, `y 0 = x₀`, on the forward window `[0, ∞)` — the
drift-only corner of the manifest family, and the seam that the delay
line's ODE cell, the random-parameter frame, and every closed-loop
continuous plant specialize.  Records are paths (`ℝ → E` directly:
one cell, no wires, and both constraint families read only `t ≥ 0`,
so the classical inclusion is insensitive to off-domain modification
with no matching apparatus needed).

Design notes, load-bearing:

* **Dynamics are constraint rows, never a solution operator.**  The
  compiled grain is three row families on the path: the initial row,
  the record-class row (continuity on the window), and the drift rows
  in *forward* form — `HasDerivWithinAt y (f (y t)) (Ici t) t` at each
  `t ≥ 0`.  The flow map of the classical theory appears nowhere in
  the presentation; determinism is *derived* content
  (`odeSols_eqOn_of_lipschitzOnWith`), and the mechanized uniqueness
  engine it consumes takes the forward rows as hypotheses verbatim —
  the community's own Grönwall interface already speaks constraint
  rows.
* **The record-class row is load-bearing.**  Forward rows give
  right-continuity for free but not left-continuity: the step record
  `k·𝟙_{[t₀,∞)}` satisfies every forward row for `ẏ = 0`, `y 0 = 0`,
  and is not a solution.  The continuity row excludes it; dropping the
  row is a genuine weakening, not a redundancy.
* **The left edge anchors to the community's mechanized object**:
  `IsIntegralCurveOn` — the integral-curve API, whose within-window
  derivative form is two-sided at interior points — plus the Picard
  integral form (`isOdeSol_iff_integral`).  The connector between the
  forward rows and the within-window form is the square's one genuine
  piece of analysis: the fundamental theorem of calculus in both
  directions (rows ⟹ the integral identity, by FTC-2 for right
  derivatives; the identity ⟹ the two-sided derivative at interior
  points, by FTC-1).  It rides a `[CompleteSpace E]` hypothesis (the
  Bochner integral); the bundling, the pinning theorems, and the
  semantic-universe wiring do not.
* **Existence is not owed.**  As for the delay line: the compiled
  atoms never exclude the vacuous model (`suppC_zero`), the
  existential commitment is judgment-level, and blow-up in finite
  time (`ẏ = y²`) means the solution set over `[0, ∞)` can be
  genuinely empty for polynomial drift on an unbounded carrier.  The
  constructive properness witness is the equilibrium
  (`isOdeSol_const`); local Picard–Lindelöf solutions live on compact
  windows and their gluing into maximal solutions is a separate,
  named stratum, not consumed here.
* **The bottom edge is possibilistic and set-valued** (the delay-line
  convention): the square presupposes no uniqueness theory — solution
  sets play the role credal sets play for the stochastic frames — and
  the per-solution Dirac face recovers the pointwise deterministic
  inclusion.  Determinism enters as a theorem under the frame's own
  hypotheses: Lipschitz drift on the declared domain, solutions
  confined to it (`odeSols_eqOn_of_lipschitzOnWith`); openness at the
  initial face enters demonically as a box, whose denotation is the
  union of the per-point solution sets (`ode_box_adequacy`).
* **Time-dependence is the seam, autonomy is the frame.**  The row
  structure `IsOdeRows` takes a time-dependent field, so the delay
  line's ODE-cell clause is literally this square's row form at the
  composed field (`isOdeCell_iff_rows`), and the random-parameter
  frame specializes per draw (`f := f θ`, autonomous per draw).  The
  formation rule itself is autonomous; the square proper
  (`ode_adequacy`) is stated there.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Set Topology MeasureTheory
open scoped NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The compiled rows, time-dependent seam -/

/-- The compiled row form of an initial-value problem against a
time-dependent field `v`: the initial row, the record-class row
(continuity on the window), and the drift rows in forward form.  The
time-dependent statement is the seam: the delay line's ODE cell and
the random-parameter frame both specialize it. -/
structure IsOdeRows (v : ℝ → E → E) (x₀ : E) (y : ℝ → E) : Prop where
  init : y 0 = x₀
  cont : ContinuousOn y (Ici 0)
  deriv : ∀ t ∈ Ici 0, HasDerivWithinAt y (v t (y t)) (Ici t) t

/-- The delay-line square's ODE-cell clause **is** this square's row
form, at the field composed with the input signal: the tie between
the delay-line instance and the ODE seam, definitional in both
directions. -/
theorem isOdeCell_iff_rows {f : E → E → E} {y₀ : E} {y z : ℝ → E} :
    IsOdeCell f y₀ y z ↔ IsOdeRows (fun t x => f x (z t)) y₀ y :=
  ⟨fun h => ⟨h.init, h.cont, h.deriv⟩, fun h => ⟨h.init, h.cont, h.deriv⟩⟩

/-- The autonomous frame: `ẏ = f(y)`, `y 0 = x₀`, as compiled rows. -/
abbrev IsOdeSol (f : E → E) (x₀ : E) (y : ℝ → E) : Prop :=
  IsOdeRows (fun _ => f) x₀ y

/-! ## The connector: forward rows ⟺ the community's forms

The forward rows are what compilation produces; the community's
mechanized solution concept (`IsIntegralCurveOn` on the window) reads
the derivative within the *whole* window — two-sided at interior
points.  The two meet through the integral identity, by the
fundamental theorem of calculus in both directions.  This is the
square's one genuine piece of analysis, and it carries the module's
only completeness hypothesis. -/

section Connector

variable [CompleteSpace E]

/-- **FTC-2 for the forward rows**: a row-form trajectory satisfies
the Picard integral identity on the window. -/
theorem IsOdeRows.integral_eq {v : ℝ → E → E} {x₀ : E} {y : ℝ → E}
    (h : IsOdeRows v x₀ y)
    (hv : ContinuousOn (fun t => v t (y t)) (Ici 0)) :
    ∀ t ∈ Ici (0 : ℝ), y t = x₀ + ∫ s in (0 : ℝ)..t, v s (y s) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have hint : IntervalIntegrable (fun s => v s (y s)) volume 0 t :=
    (hv.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht'
  have key : (∫ s in (0 : ℝ)..t, v s (y s)) = y t - y 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht'
      (h.cont.mono Icc_subset_Ici_self)
      (fun s hs => (h.deriv s hs.1.le).mono Ioi_subset_Ici_self) hint
  rw [key, h.init]
  abel

/-- **FTC-1 at interior points**: a row-form trajectory has the
two-sided derivative at every `t > 0` — the forward-only reading of
the compiled rows costs nothing away from the corner. -/
theorem IsOdeRows.hasDerivAt {v : ℝ → E → E} {x₀ : E} {y : ℝ → E}
    (h : IsOdeRows v x₀ y)
    (hv : ContinuousOn (fun t => v t (y t)) (Ici 0))
    {t : ℝ} (ht : 0 < t) : HasDerivAt y (v t (y t)) t := by
  have hI : HasDerivAt (fun u => x₀ + ∫ s in (0 : ℝ)..u, v s (y s))
      (v t (y t)) t := by
    refine HasDerivAt.const_add x₀
      (intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_)
    · exact (hv.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht.le
    · exact ⟨Ici 0, Ici_mem_nhds ht,
        hv.aestronglyMeasurable measurableSet_Ici⟩
    · exact hv.continuousAt (Ici_mem_nhds ht)
  refine hI.congr_of_eventuallyEq ?_
  filter_upwards [Ici_mem_nhds ht] with u hu
  exact h.integral_eq hv u hu

/-- The connector at the time-dependent seam: the compiled rows are
the community's integral-curve concept on the window, given
continuity of the field along the trajectory.  The community side
carries no separate record-class clause — continuity is derivable
from the within-window derivative form. -/
theorem isOdeRows_iff_integralCurve {v : ℝ → E → E} {x₀ : E} {y : ℝ → E}
    (hv : ContinuousOn (fun t => v t (y t)) (Ici 0)) :
    IsOdeRows v x₀ y ↔ y 0 = x₀ ∧ IsIntegralCurveOn y v (Ici 0) := by
  constructor
  · intro h
    refine ⟨h.init, fun t ht => ?_⟩
    rcases eq_or_lt_of_le (mem_Ici.mp ht) with h0 | h0
    · subst h0
      exact h.deriv 0 left_mem_Ici
    · exact (h.hasDerivAt hv h0).hasDerivWithinAt
  · rintro ⟨h0, hIC⟩
    exact ⟨h0, hIC.continuousOn,
      fun t ht => (hIC t ht).mono (Ici_subset_Ici.mpr (mem_Ici.mp ht))⟩

/-- The Picard fixed-point form: continuous trajectories satisfying
the integral identity are exactly the row-form solutions — the
community's other canonical presentation, and the form the
contraction-mapping existence proof constructs. -/
theorem isOdeSol_iff_integral {f : E → E} {x₀ : E} {y : ℝ → E}
    (hf : Continuous f) :
    IsOdeSol f x₀ y ↔ ContinuousOn y (Ici 0) ∧
      ∀ t ∈ Ici (0 : ℝ), y t = x₀ + ∫ s in (0 : ℝ)..t, f (y s) := by
  constructor
  · intro h
    exact ⟨h.cont, h.integral_eq (hf.comp_continuousOn h.cont)⟩
  · rintro ⟨hy, hint⟩
    have hv : ContinuousOn (fun t => f (y t)) (Ici 0) :=
      hf.comp_continuousOn hy
    refine ⟨?_, hy, ?_⟩
    · simpa using hint 0 left_mem_Ici
    · intro t ht
      have ht' : (0 : ℝ) ≤ t := ht
      have hsub : Ioi t ⊆ Ici (0 : ℝ) := fun u hu => le_trans ht' hu.le
      have hd : HasDerivWithinAt (fun u => x₀ + ∫ s in (0 : ℝ)..u, f (y s))
          (f (y t)) (Ici t) t := by
        refine HasDerivWithinAt.const_add x₀
          (intervalIntegral.integral_hasDerivWithinAt_right ?_ ?_ ?_)
        · exact (hv.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht'
        · exact ⟨Ici 0,
            Filter.mem_of_superset self_mem_nhdsWithin hsub,
            hv.aestronglyMeasurable measurableSet_Ici⟩
        · exact (hv t ht).mono hsub
      exact hd.congr (fun u hu => hint u (le_trans ht' hu)) (hint t ht)

/-- The connector at the autonomous frame, hypothesis-free on the
trajectory: for continuous drift, the compiled rows are exactly the
community's integral curves through `x₀` on the window. -/
theorem isOdeSol_iff_integralCurve {f : E → E} {x₀ : E} {y : ℝ → E}
    (hf : Continuous f) :
    IsOdeSol f x₀ y ↔
      y 0 = x₀ ∧ IsIntegralCurveOn y (fun _ => f) (Ici 0) := by
  constructor
  · intro h
    exact (isOdeRows_iff_integralCurve (hf.comp_continuousOn h.cont)).mp h
  · intro h
    exact (isOdeRows_iff_integralCurve
      (hf.comp_continuousOn h.2.continuousOn)).mpr h

end Connector

/-! ## The pinning theorems: determinism as derived content

No completeness needed: the mechanized Grönwall interface consumes
the forward rows verbatim.  Uniqueness is a *declared-domain*
theorem — Lipschitz drift on the domain, solutions confined to it —
never a constraint-stratum fact; the compiled atoms denote the
solution set. -/

/-- **The rows pin the trajectory** on the declared domain: two
row-form solutions with Lipschitz drift on `s`, both confined to `s`,
agree on the whole window.  The confinement hypotheses are the
frame's declared-domain discipline, consumed rather than decorative. -/
theorem odeSols_eqOn_of_lipschitzOnWith {f : E → E} {K : ℝ≥0} {s : Set E}
    (hL : LipschitzOnWith K f s) {x₀ : E} {y₁ y₂ : ℝ → E}
    (h₁ : IsOdeSol f x₀ y₁) (h₂ : IsOdeSol f x₀ y₂)
    (hs₁ : ∀ t ∈ Ici (0 : ℝ), y₁ t ∈ s)
    (hs₂ : ∀ t ∈ Ici (0 : ℝ), y₂ t ∈ s) :
    EqOn y₁ y₂ (Ici 0) := by
  intro T hT
  have hT' : (0 : ℝ) ≤ T := hT
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ x => f x) (s := fun _ => s)
    (fun t _ => hL)
    (h₁.cont.mono Icc_subset_Ici_self)
    (fun t ht => h₁.deriv t ht.1)
    (fun t ht => hs₁ t ht.1)
    (h₂.cont.mono Icc_subset_Ici_self)
    (fun t ht => h₂.deriv t ht.1)
    (fun t ht => hs₂ t ht.1)
    (h₁.init.trans h₂.init.symm)
    (right_mem_Icc.mpr hT')

/-- The globally-Lipschitz corollary: no confinement needed when the
declared domain is the whole carrier. -/
theorem odeSols_eqOn_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hL : LipschitzWith K f) {x₀ : E} {y₁ y₂ : ℝ → E}
    (h₁ : IsOdeSol f x₀ y₁) (h₂ : IsOdeSol f x₀ y₂) :
    EqOn y₁ y₂ (Ici 0) :=
  odeSols_eqOn_of_lipschitzOnWith hL.lipschitzOnWith h₁ h₂
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)

/-! ## The square

The compiled presentation is two constraint atoms on the record
space — the cell (record class + drift rows) and the initial row —
each read at the possibilistic stratum, exactly the delay-line
convention.  The classical semantics is the solution set in the
community's vocabulary, included as a support constraint. -/

/-- The cell's constraint set: record class and drift rows.  (The
name avoids the delay-line module's `odeCellC`, which lives on the
composite record space.) -/
def odeDynC (f : E → E) : Set (ℝ → E) :=
  {y | ContinuousOn y (Ici 0) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (f (y t)) (Ici t) t}

/-- The initial row's constraint set. -/
def odeInitC (x₀ : E) : Set (ℝ → E) := {y | y 0 = x₀}

/-- The compiled constraint atoms: the cell and the initial row, one
support atom each. -/
def odeAtoms (f : E → E) (x₀ : E) : List (SubPMF (ℝ → E) → Prop) :=
  [suppC (odeDynC f), suppC (odeInitC x₀)]

/-- The compiled solution set: row-form solutions. -/
def odeSols (f : E → E) (x₀ : E) : Set (ℝ → E) := {y | IsOdeSol f x₀ y}

/-- The classical object, in the community's mechanized vocabulary:
integral curves of the drift through `x₀`, on the window. -/
def integralCurves (f : E → E) (x₀ : E) : Set (ℝ → E) :=
  {y | y 0 = x₀ ∧ IsIntegralCurveOn y (fun _ => f) (Ici 0)}

/-- Bundling: the conjunction of the two atoms is the support
constraint of the compiled solution set. -/
theorem odeAtoms_iff (f : E → E) (x₀ : E) (μ : SubPMF (ℝ → E)) :
    looseConj (odeAtoms f x₀) μ ↔ suppC (odeSols f x₀) μ := by
  simp only [odeAtoms, looseConj, suppC]
  constructor
  · rintro ⟨h1, h2, -⟩ y hy
    exact ⟨h2 y hy, (h1 y hy).1, (h1 y hy).2⟩
  · intro h
    exact ⟨fun y hy => ⟨(h y hy).cont, (h y hy).deriv⟩,
      fun y hy => (h y hy).init, trivial⟩

/-- The left edge in set form: for continuous drift, the compiled
solution set is the community's. -/
theorem odeSols_eq_integralCurves [CompleteSpace E] {f : E → E}
    (hf : Continuous f) (x₀ : E) :
    odeSols f x₀ = integralCurves f x₀ :=
  Set.ext fun _ => isOdeSol_iff_integralCurve hf

/-- **The ODE adequacy square.**  Compiling the initial-value problem
to its constraint atoms and denoting agrees with interpreting the
equation classically and including its solution set at the
possibilistic stratum: an invertible globular cell of `Crd (ℝ → E)`.
Two-sided — the left edge is the fundamental theorem of calculus,
total for continuous drift on a complete carrier. -/
theorem ode_adequacy [CompleteSpace E] {f : E → E} (hf : Continuous f)
    (x₀ : E) {a : Crd (ℝ → E)} :
    ∃ α : Cell (looseConj (odeAtoms f x₀) : Loose a a)
        (suppC (integralCurves f x₀)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [odeAtoms_iff, ← odeSols_eq_integralCurves hf x₀]

/-! ## The per-solution (Dirac) face and the properness witnesses -/

/-- The per-solution Dirac face: each classical solution's point mass
satisfies the compiled atoms. -/
theorem odeAtoms_dirac_of_mem [CompleteSpace E] {f : E → E}
    (hf : Continuous f) {x₀ : E} {y : ℝ → E}
    (hy : y ∈ integralCurves f x₀) :
    looseConj (odeAtoms f x₀) (SubPMF.dirac y) := by
  rw [odeAtoms_iff]
  refine (suppC_dirac _ _).mpr ?_
  rw [odeSols_eq_integralCurves hf x₀]
  exact hy

/-- The deterministic inclusion entails the compiled constraints, per
solution: the `diracC` bottom edge at the per-solution grain. -/
theorem diracC_sol_entails [CompleteSpace E] {f : E → E}
    (hf : Continuous f) {x₀ : E} {y : ℝ → E}
    (hy : y ∈ integralCurves f x₀) :
    ∀ μ : SubPMF (ℝ → E), diracC y μ → looseConj (odeAtoms f x₀) μ := by
  intro μ hμ
  have hμ' : μ = SubPMF.dirac y := hμ
  rw [hμ']
  exact odeAtoms_dirac_of_mem hf hy

/-- Equilibria solve: the constant trajectory at a zero of the drift. -/
theorem isOdeSol_const {f : E → E} {k : E} (hk : f k = 0) :
    IsOdeSol f k (fun _ => k) where
  init := rfl
  cont := continuousOn_const
  deriv := fun t _ => by
    show HasDerivWithinAt (fun _ : ℝ => k) (f k) (Ici t) t
    rw [hk]
    exact hasDerivWithinAt_const t _ k

/-- The constructive properness witness: at an equilibrium the
compiled constraint class is inhabited by more than the vacuous
model, so the judgment-level existential commitment is dischargeable
— no completeness, no existence theory consumed. -/
theorem odeAtoms_dirac_const {f : E → E} {k : E} (hk : f k = 0) :
    looseConj (odeAtoms f k) (SubPMF.dirac (fun _ => k)) := by
  rw [odeAtoms_iff]
  exact (suppC_dirac _ _).mpr (isOdeSol_const hk)

/-! ## The demonic initial face

Openness at the initial face enters demonically as a box: the frame's
`init_box` convention.  At the possibilistic stratum its denotation
is the union of the per-point solution sets — the deterministic
frame's shadow of the credal-union machinery of the stochastic
squares. -/

/-- The demonic initial row: the initial value lies in the box. -/
def odeInitBoxC (B : Set E) : Set (ℝ → E) := {y | y 0 ∈ B}

/-- The compiled atoms with a demonic initial box. -/
def odeBoxAtoms (f : E → E) (B : Set E) : List (SubPMF (ℝ → E) → Prop) :=
  [suppC (odeDynC f), suppC (odeInitBoxC B)]

/-- The demonic initial face denotes the union of the per-point
solution sets. -/
theorem odeBoxSols_eq (f : E → E) (B : Set E) :
    odeDynC f ∩ odeInitBoxC B = ⋃ x₀ ∈ B, odeSols f x₀ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_iUnion, odeDynC, odeInitBoxC,
    odeSols, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hc, hd⟩, hB⟩
    exact ⟨y 0, hB, rfl, hc, hd⟩
  · rintro ⟨x₀, hB, h⟩
    refine ⟨⟨h.cont, h.deriv⟩, ?_⟩
    rw [h.init]
    exact hB

/-- Bundling at the demonic initial face. -/
theorem odeBoxAtoms_iff (f : E → E) (B : Set E) (μ : SubPMF (ℝ → E)) :
    looseConj (odeBoxAtoms f B) μ ↔
      suppC (⋃ x₀ ∈ B, odeSols f x₀) μ := by
  simp only [odeBoxAtoms, looseConj, suppC, ← odeBoxSols_eq]
  constructor
  · rintro ⟨h1, h2, -⟩ y hy
    exact ⟨h1 y hy, h2 y hy⟩
  · intro h
    exact ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2, trivial⟩

/-- The adequacy square at the demonic initial face: the compiled
atoms with a box initial row denote the union of the classical
solution sets over the box. -/
theorem ode_box_adequacy [CompleteSpace E] {f : E → E} (hf : Continuous f)
    (B : Set E) {a : Crd (ℝ → E)} :
    ∃ α : Cell (looseConj (odeBoxAtoms f B) : Loose a a)
        (suppC (⋃ x₀ ∈ B, integralCurves f x₀)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [odeBoxAtoms_iff]
  have hU : (⋃ x₀ ∈ B, odeSols f x₀) = ⋃ x₀ ∈ B, integralCurves f x₀ :=
    Set.iUnion₂_congr fun x₀ _ => odeSols_eq_integralCurves hf x₀
  rw [hU]

/-! ## The square, wired to the semantic universe

The wiring rides the generic transport layer wholesale — the
presented diagram, the ideal-point bridge — with one deliberate
contrast against the stochastic squares: the possibilistic model
class is closed downward (sub-mass never violates a support
constraint), so the *zero* law's ideal point models every compiled
presentation.  Existential commitment stays judgment-level, exactly
as `suppC_zero` says one stratum down. -/

/-- The compiled initial-value problem's presentation in the semantic
universe's fibre over the record space. -/
noncomputable def odeDnf (f : E → E) (x₀ : E) :
    SpecDnf (Plain.Joint (ℝ → E)) :=
  diagramDnf (odeAtoms f x₀)

/-- The rows-grain wiring: an ideal point models the compiled
presentation exactly when its law is supported on the compiled
solution set. -/
theorem su_ode_wiring (f : E → E) (x₀ : E) (μ : SubPMF (ℝ → E)) :
    idealPoint μ ∈ (odeDnf f x₀).modelClass ↔
      suppC (odeSols f x₀) μ :=
  (idealPoint_mem_diagramDnf_iff (odeAtoms f x₀) μ).trans
    (odeAtoms_iff f x₀ μ)

/-- **The ODE square, wired to the semantic universe**: an ideal
point models the compiled presentation exactly when its law is
supported on the classical solution set. -/
theorem su_ode_adequacy [CompleteSpace E] {f : E → E} (hf : Continuous f)
    (x₀ : E) (μ : SubPMF (ℝ → E)) :
    idealPoint μ ∈ (odeDnf f x₀).modelClass ↔
      suppC (integralCurves f x₀) μ := by
  rw [su_ode_wiring, odeSols_eq_integralCurves hf x₀]

/-- The positive face: each classical solution's point mass enters
the universe and models the compiled presentation. -/
theorem su_ode_dirac_mem [CompleteSpace E] {f : E → E}
    (hf : Continuous f) {x₀ : E} {y : ℝ → E}
    (hy : y ∈ integralCurves f x₀) :
    idealPoint (SubPMF.dirac y) ∈ (odeDnf f x₀).modelClass :=
  (su_ode_adequacy hf x₀ _).mpr ((suppC_dirac _ _).mpr hy)

/-- The possibilistic contrast, stated deliberately: the zero law's
ideal point models the compiled presentation — support constraints
never force realization, and the demand that the system realize
anything is judgment-level content. -/
theorem su_ode_vacuous_mem (f : E → E) (x₀ : E) :
    idealPoint (SubPMF.zero (ℝ → E)) ∈ (odeDnf f x₀).modelClass :=
  (su_ode_wiring f x₀ _).mpr (suppC_zero _)

/-- Ex falso at the corner: the inconsistent system does not model
the compiled presentation. -/
theorem su_ode_bottom (f : E → E) (x₀ : E) :
    (⊤ : Plain.Pen (ℝ → E)) ∉ (odeDnf f x₀).modelClass :=
  top_notMem_diagramDnf _

end Adequacy
end SuFunctor
