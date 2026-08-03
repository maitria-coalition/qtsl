import QtslAux.QStreett

/-!
# Class-stratum alias fixture: `QStreettDegenerate`

The crown fixture of the alias family — `QStreettDegenerate` in the
alias-derivation fixture pattern (`AliasSmallGain` is the exemplar;
`AliasStructural` / `AliasPathSugar` are the class-stratum siblings),
at the same lemma-level transposition: the elaboration lands on the
base rule's **in-repo soundness lemma**
(`Qtsl.QStreett.sound_StreettDegenerate`, the degenerate form of the
bundled Streett certificate at `Rq := fun _ => Set.univ`) with
computed arguments; the derivation-calculus cell plumbing arrives with
the class-stratum presentation.

What makes this the showcase: the base lemma takes **21 explicit
hypotheses** — measurability (six), the probability budget, the
confinement inclusion, mass conservation and step-closure, the safety
battery's integrability/drift/floor/nonnegativity, per-pair positivity
and rank nonnegativity/boundedness/integrability, the strict
`ε`-decrease drift, the start state, and the threshold — and the
generic gate discharges **all 21 from the structure's fields**
(21 → 0), concluding a genuinely nontrivial almost-sure bound: with
probability at least `p`, *every* response set `G i` is visited
infinitely often.  The proof machinery behind that conclusion
(localized supermartingales, the excursion bound, the fail-closed
safety battery) never appears at the fixture site; the concrete
instance below exhibits all 21 discharges as term-level fields on one
screen, with zero martingale theory at the demo site.

Conservativity caution (carried on every alias in this family, per
its standing discipline): the degenerate collapse — requests taken to
be `univ`,
hence "always pending", so the Streett conditional strengthens to
unconditional recurrence — consumes $\mathrm{Fin}(S) = \emptyset$,
hard-coded here by the total path type `ℕ → S`.  Exact on total-path
charts only: on killed-process classes with the cemetery outside the
region vocabulary, "the request is always pending" fails after death,
and the chart hypothesis must ride explicitly wherever the alias is
cited over a completed space.

Decode note: at the S1 fragment depth a `decodeQtslPresentationOps`
hypothesis would be decorative rather than load-bearing; the decode
marriage rides the per-row fragment widening planned for this
family.
-/

namespace SuFunctor

namespace QtslSem

open MeasureTheory ProbabilityTheory Filter
open Qtsl.Battery Qtsl.QStreett

/-!
## QStreettDegenerate — unconditional recurrence of every response set

Catalogue: tier **alias** — the degenerate Streett bundle (every
request set `⊤`).  Base lemma: `Qtsl.QStreett.sound_StreettDegenerate`
(21 explicit hypotheses; the roster's "20" undercounted by one —
count them).
-/

/-- A degenerate-Streett step: the chain data (confinement region `D`
inside `Dbar`, unsafe set `U`, safety battery `V₀` with budget
`p + thr ≤ 1`, start state `x`) and, per pair `i`, the response set
`G i` with its rank certificate `(W i, ε i, C i)`.  The 21 proof
fields mirror the base lemma's explicit hypothesis list verbatim —
the whole content of the alias rides here, so the gate below takes no
hypotheses at all.

The structure deliberately carries no instance assumptions beyond
`[MeasurableSpace S]`: `[Countable ι]` and `[IsMarkovKernel K]` are
consumed by the gate only. -/
structure StreettDegenerateStep (S : Type*) [MeasurableSpace S]
    (ι : Type*) (K : Kernel S S) where
  D : Set S
  Dbar : Set S
  U : Set S
  V₀ : S → ℝ
  p : ℝ
  thr : ℝ
  x : S
  G : ι → Set S
  W : ι → S → ℝ
  ε : ι → ℝ
  C : ι → ℝ
  -- measurability (6)
  measD : MeasurableSet D
  measDbar : MeasurableSet Dbar
  measU : MeasurableSet U
  measV₀ : Measurable V₀
  measG : ∀ i, MeasurableSet (G i)
  measW : ∀ i, Measurable (W i)
  -- budget and confinement (4)
  budget : p + thr ≤ 1
  confSub : D ⊆ Dbar
  mass : ∀ y ∈ D, y ∉ U → K y Dbar = 1
  stepClosed : ∀ y ∈ D, y ∉ U → K y (D ∪ U) = 1
  -- the safety battery (4)
  battInt : ∀ y ∈ D, y ∉ U → Integrable V₀ (K y)
  battDrift : ∀ y ∈ D, y ∉ U → ∫ z, V₀ z ∂K y ≤ V₀ y
  battFloor : ∀ y ∈ U, y ∈ Dbar → 1 ≤ V₀ y
  battNonneg : ∀ y ∈ Dbar, 0 ≤ V₀ y
  -- the per-pair rank certificates (5)
  epsPos : ∀ i, 0 < ε i
  rankNonneg : ∀ i, ∀ y ∈ Dbar, 0 ≤ W i y
  rankBound : ∀ i, ∀ y ∈ Dbar, W i y ≤ C i
  rankInt : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i → Integrable (W i) (K y)
  rankDriftR : ∀ i, ∀ y ∈ D, y ∉ U → y ∉ G i →
    ∫ z, W i z ∂K y ≤ W i y - ε i
  -- start (2)
  start : x ∈ D
  threshold : V₀ x ≤ thr

/-- The elaboration: the alias's concluded event — unconditional
recurrence of **every** response set. -/
def StreettDegenerateStep.recurrenceEvent {S : Type*} [MeasurableSpace S]
    {ι : Type*} {K : Kernel S S} (st : StreettDegenerateStep S ι K) :
    Set (ℕ → S) :=
  {ω | ∀ i, ∃ᶠ n in atTop, ω n ∈ st.G i}

/-- **The generic gate**: the probability bound on the recurrence
event, discharged entirely from the structure's fields — a single
application of `sound_StreettDegenerate` to the 21 proof fields
(the base lemma takes 21 explicit hypotheses; the step form takes
none: 21 → 0). -/
theorem streettDegenerate_gate {S : Type*} [MeasurableSpace S]
    {ι : Type*} [Countable ι] {K : Kernel S S} [IsMarkovKernel K]
    (st : StreettDegenerateStep S ι K) :
    ENNReal.ofReal st.p ≤ pathMeasure K st.x st.recurrenceEvent :=
  sound_StreettDegenerate st.measD st.measDbar st.measU st.measV₀
    st.measG st.measW st.budget st.confSub st.mass st.stepClosed
    st.battInt st.battDrift st.battFloor st.battNonneg st.epsPos
    st.rankNonneg st.rankBound st.rankInt st.rankDriftR
    st.start st.threshold

namespace DegenerateDemo

/-- The two-state deterministic cycle: `false ↦ true ↦ false`. -/
noncomputable def cycleK : Kernel Bool Bool :=
  Kernel.deterministic (fun s => !s) (Measurable.of_discrete)

instance : IsMarkovKernel cycleK := by
  unfold cycleK; infer_instance

/-- The cycle kernel at a state is the Dirac measure at the flipped
state. -/
theorem cycleK_apply (y : Bool) : cycleK y = Measure.dirac (!y) :=
  Kernel.deterministic_apply _ y

/-- The concrete step — the 21 hypotheses of the base lemma, each
discharged as a term-level field: two Streett pairs (`ι = Bool`,
`G i = {i}` — the bundle genuinely quantifies), the whole space as
confinement region (`D = Dbar = univ`, `U = ∅`), the zero battery at
full budget (`V₀ = 0`, `p = 1`, `thr = 0`), and per pair the rank
indicator `W i = (if · = i then 0 else 1)` with decrease `ε = 1` and
ceiling `C = 1`: one step off the response set lands exactly on it,
so the expected rank drops from `1` to `0`. -/
noncomputable def step : StreettDegenerateStep Bool Bool cycleK where
  D := Set.univ
  Dbar := Set.univ
  U := ∅
  V₀ := fun _ => 0
  p := 1
  thr := 0
  x := false
  G i := {i}
  W i y := if y = i then 0 else 1
  ε _ := 1
  C _ := 1
  measD := MeasurableSet.univ
  measDbar := MeasurableSet.univ
  measU := MeasurableSet.empty
  measV₀ := measurable_const
  measG _ := MeasurableSet.of_discrete
  measW _ := Measurable.of_discrete
  budget := by norm_num
  confSub := subset_rfl
  mass _ _ _ := measure_univ
  stepClosed _ _ _ := by rw [Set.union_empty]; exact measure_univ
  battInt _ _ _ := integrable_const 0
  battDrift _ _ _ := by simp
  battFloor y hy _ := absurd hy (Set.notMem_empty y)
  battNonneg _ _ := le_refl 0
  epsPos _ := one_pos
  rankNonneg i y _ := by split <;> norm_num
  rankBound i y _ := by split <;> norm_num
  rankInt _ _ _ _ _ := Integrable.of_finite
  rankDriftR i y _ _ hyG := by
    have hy : y = !i := by
      rcases y <;> rcases i <;> simp_all
    subst hy
    rw [cycleK_apply, integral_dirac]
    rcases i <;> norm_num
  start := Set.mem_univ false
  threshold := le_refl 0

/-- The concrete face, from the bare gate: full mass on the event that
**every** state of the two-state cycle is visited infinitely often —
the almost-sure recurrence of both states, concluded from 21
term-level certificate checks with zero martingale theory at this
site. -/
theorem face :
    ENNReal.ofReal 1 ≤ pathMeasure cycleK false
      {ω | ∀ i : Bool, ∃ᶠ n in atTop, ω n ∈ ({i} : Set Bool)} :=
  streettDegenerate_gate step

/-- The face at mass one (the display form). -/
theorem face_full_mass :
    1 ≤ pathMeasure cycleK false
      {ω | ∀ i : Bool, ∃ᶠ n in atTop, ω n ∈ ({i} : Set Bool)} :=
  ENNReal.ofReal_one ▸ face

/-- The extracted single-pair corollary: almost surely, the cycle
visits `true` infinitely often. -/
theorem face_true :
    1 ≤ pathMeasure cycleK false {ω | ∃ᶠ n in atTop, ω n = true} := by
  refine le_trans face_full_mass (measure_mono fun ω hω => ?_)
  exact (hω true).mono fun n hn => hn

end DegenerateDemo

end QtslSem

end SuFunctor
