import QtslAux.JumpDiffusion
import QtslAux.SdeMartingaleProblem

/-! # The martingale problem at the multi-leg generator, and its verdicts

The martingale-problem verdict machinery of
`QtslAux.SdeMartingaleProblem` consumes its generator **opaquely**: the
compensator argument — martingale plus nonincreasing compensation is a
supermartingale — never inspects the drift, diffusion, killing, or jump
structure of the operator whose row is certified. This module is that
opacity made explicit: the solution concept, the derived continuous-time
Dynkin supermartingale, the sampled Dynkin class, and the verdict stock
transplant verbatim from the single-Dirac-leg generator
(`Qtsl.SdeGenerator.generator`) to the multi-leg integro-differential
generator (`Qtsl.JumpDiffusion.generator`) — killing, finitely many jump
legs, sub-stochastic mixture resets.

The payoff is at the compiled face: the multi-leg splice
(`Qtsl.JumpDiffusion.genPoly_eval_eq_generator`) has **no hypotheses**,
so the transplanted headlines (`mp_avoid_row_of_genPoly`,
`mp_avoid_init_of_genPoly`) hold for *every* polynomial presentation —
the conservativity and single-leg fences of the landed SDE headlines are
gone, and the checker's own compiled row certifies avoid verdicts for
the full presentation class.

The landed single-leg route then **factors** through this module:
`SdeProfile.toJd` embeds the single-Dirac profile, `generator_toJd` is
the identity of operators at the semantic face, and
`SdeMartingaleProblem.MpSolution.toJd` transports solutions along it —
so a martingale-problem solution in the landed sense is one in this
module's sense, verdicts included.

The C² test class and the polynomial statics (`IsC2Fn`, `isC2Fn_poly`)
are generator-free and are consumed from the SDE module unchanged; the
`OptionalSamplingRC` compensator engine likewise. What moves is exactly
the generator-touching skin.

The positive control (`idResetPoly`, `mp_control`) is strictly richer
than the SDE module's zero presentation: its two jump legs carry *live*
rates and a genuine two-map mixture — the dynamics are nonetheless zero
because every reset is the identity at total mass one, which is the
honest scope of a constant-process control (a nonzero-dynamics solution
constructor waits on upstream stochastic integration, exactly as in the
SDE module's fences).

Fences (named, honest): verdicts are on the sampled grid; martingale-
problem well-posedness is not claimed; the strong-solution face is
absent upstream at the pin; per-leg rate validity and mixture-mass
validity are checker-facing rows (`lam_nonneg_of_rate_rows`), never
assumed silently.

No `sorry`; axiom receipts ride the package's `AxiomReceipts` target.
-/

open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal

namespace Qtsl

namespace JumpDiffusion

open SdeGenerator (State SdeProfile)
open SdeGeneratorPoly
open SdeMartingaleProblem (IsC2Fn isC2Fn_poly)

variable {n m : ℕ}

/-! ## 1. The Dynkin class at the multi-leg generator -/

variable {Ω : Type*} [MeasureSpace Ω]

/-- **The Dynkin class at the multi-leg generator** (avoid form): a
sampled stopped state process for the profile `P`, confined to the
closed working domain `D`, carrying the ONE analytic field
`dynkin_of_gen_nonpos` in conditional form: whenever the
integro-differential generator row is certified nonpositive on `D`, the
certificate observable rides the chain as a supermartingale.
Deliberately a field, never a theorem of this module; discharged for
martingale-problem presentations by `MpSolution.toJdDynkinVille` below —
the verbatim transplant of `Qtsl.SdeGenerator.SdeDynkinVille`, which is
this structure at the single-Dirac-leg face. -/
structure JdDynkinVille (P : JdProfile n m) (D : Set (State n))
    (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ)
    (Ω : Type*) [MeasureSpace Ω] where
  /-- the sampled stopped state process -/
  X : ℕ → Ω → State n
  /-- the filtration of the sampled process -/
  𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)
  /-- escape-face accounting, structural: the stopped chain stays in the
  closed working domain -/
  confined : ∀ k ω, X k ω ∈ D
  /-- the one analytic field: certified `𝒜V ≤ 0` on `D` ⟹ `V(X_k)` is a
  supermartingale — the Dynkin formula for C² observables up to bounded
  stopping, plus optional sampling and Fatou. -/
  dynkin_of_gen_nonpos :
    (∀ z ∈ D, generator P V gradV hessV z ≤ 0) →
    Supermartingale (fun k ω => V (X k ω)) 𝒢 volume

namespace JdDynkinVille

variable {P : JdProfile n m} {D : Set (State n)} {V : State n → ℝ}
  {gradV : State n → State n} {hessV : State n → Fin n → Fin n → ℝ}

/-- **The avoid row** (multiplicative form): the three row families
gen (`𝒜V ≤ 0` on `D`), floor (`V ≥ a` on `Bad`), nonneg (`V ≥ 0` on `D`)
give `a · P(∃k, X_k ∈ Bad) ≤ 𝔼[V(X₀)]`, through
`Qtsl.Ville.reach_avoid`. -/
theorem avoid_row [IsProbabilityMeasure (volume : Measure Ω)]
    (S : JdDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)} {a : ℝ}
    (hgen : ∀ z ∈ D, generator P V gradV hessV z ≤ 0)
    (hnonneg : ∀ z ∈ D, 0 ≤ V z)
    (hfloor : ∀ z ∈ Bad, a ≤ V z) :
    ENNReal.ofReal a * volume {ω | ∃ k, S.X k ω ∈ Bad}
      ≤ ENNReal.ofReal (∫ ω, V (S.X 0 ω)) :=
  Ville.reach_avoid (X := S.X) (B := Bad) (S.dynkin_of_gen_nonpos hgen)
    (fun k ω => hnonneg _ (S.confined k ω))
    (fun _ _ hk => hfloor _ hk)

/-- **The avoid row** (division form): with `a > 0`,
`P(∃k, X_k ∈ Bad) ≤ 𝔼[V(X₀)] / a`. -/
theorem avoid_row_div [IsProbabilityMeasure (volume : Measure Ω)]
    (S : JdDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)} {a : ℝ}
    (hgen : ∀ z ∈ D, generator P V gradV hessV z ≤ 0)
    (hnonneg : ∀ z ∈ D, 0 ≤ V z)
    (ha : 0 < a) (hfloor : ∀ z ∈ Bad, a ≤ V z) :
    volume {ω | ∃ k, S.X k ω ∈ Bad}
      ≤ ENNReal.ofReal (∫ ω, V (S.X 0 ω)) / ENNReal.ofReal a :=
  Ville.reach_avoid_div (X := S.X) (B := Bad)
    (S.dynkin_of_gen_nonpos hgen)
    (fun k ω => hnonneg _ (S.confined k ω)) ha
    (fun _ _ hk => hfloor _ hk)

/-- **The avoid row at a deterministic start** (floor at `1`):
`P(∃k, X_k ∈ Bad) ≤ V(z₀)`. -/
theorem avoid_row_init [IsProbabilityMeasure (volume : Measure Ω)]
    (S : JdDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)}
    {z0 : State n}
    (hgen : ∀ z ∈ D, generator P V gradV hessV z ≤ 0)
    (hnonneg : ∀ z ∈ D, 0 ≤ V z)
    (hfloor : ∀ z ∈ Bad, 1 ≤ V z)
    (hstart : ∀ ω, S.X 0 ω = z0) :
    volume {ω | ∃ k, S.X k ω ∈ Bad} ≤ ENNReal.ofReal (V z0) := by
  have h := S.avoid_row (a := 1) hgen hnonneg hfloor
  have hconst : (∫ ω, V (S.X 0 ω)) = V z0 := by
    simp only [hstart]
    simp only [integral_const, probReal_univ, one_smul]
  rw [ENNReal.ofReal_one, one_mul, hconst] at h
  exact h

/-- **The discounted-deadline row**: the discounted certificate row
`𝒜V + θV ≤ 0` off the target has, at contraction `β = e^{−θΔ}` on the
sampling grid, the geometric-drift face
`E[V(X_{k+1}) | 𝒢_k] ≤ β·V(X_k)` off the target — supplied here as a
hypothesis per model, exactly like the Dynkin field — and then
`a · P(no visit to Target by time k) ≤ βᵏ · 𝔼[V(X₀)]`, through
`Qtsl.Deadline.deadline_tail`. -/
theorem discounted_deadline_row [IsProbabilityMeasure (volume : Measure Ω)]
    (S : JdDynkinVille P D V gradV hessV Ω) {Target : Set (State n)}
    {β a : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ k, Integrable (fun ω => V (S.X k ω))
      (volume : Measure Ω))
    (hnonneg : ∀ z ∈ D, 0 ≤ V z)
    (hmB : ∀ k, MeasurableSet[S.𝒢 k] {ω | S.X k ω ∈ Target})
    (hdrift : ∀ k, ∀ᵐ ω ∂(volume : Measure Ω), S.X k ω ∉ Target →
      ((volume : Measure Ω)[fun ω' => V (S.X (k + 1) ω') | S.𝒢 k]) ω
        ≤ β * V (S.X k ω))
    (hbarrier : ∀ z ∈ D \ Target, a ≤ V z) (k : ℕ) :
    ENNReal.ofReal a * volume {ω | ∀ j ≤ k, S.X j ω ∉ Target}
      ≤ ENNReal.ofReal (β ^ k * ∫ ω, V (S.X 0 ω)) :=
  Deadline.deadline_tail (V := fun j ω => V (S.X j ω)) (X := S.X)
    (B := Target) hβ hint
    (fun j ω => hnonneg _ (S.confined j ω)) hmB hdrift
    (fun j ω hj => hbarrier _ ⟨S.confined j ω, hj⟩) k

end JdDynkinVille

/-! ## 2. The left edge: the (stopped) martingale problem at the
multi-leg generator -/

/-- **The stopped/confined martingale problem for a multi-leg
jump-diffusion profile** — the community's solution semantics
(Stroock–Varadhan; Ethier–Kurtz ch. 4, generator-as-pairs form; Davis
for the jump-kernel/killing convention), stated over the multi-leg
integro-differential generator: an adapted, jointly-path-measurable
process confined to the closed working domain `D` such that for every
C²-presented test observable satisfying the textbook integrability
provisos, the compensated process `V(X_t) − ∫₀ᵗ (𝒜V)(X_s) ds` is a
martingale. The test class (`IsC2Fn`) is the SDE module's,
generator-free and consumed unchanged. -/
structure MpSolution (P : JdProfile n m) (D : Set (State n))
    (Ω : Type*) [MeasureSpace Ω] where
  /-- the state process -/
  X : ℝ≥0 → Ω → State n
  /-- the filtration -/
  ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)
  /-- the process is adapted -/
  hadapted : ∀ t, StronglyMeasurable[ℱ t] (X t)
  /-- paths are measurable (the honest shadow of progressive
  measurability; every textbook solution is at least this) -/
  hpath : ∀ ω, Measurable fun t : ℝ≥0 => X t ω
  /-- confinement to the closed working domain (the stopped problem;
  escape-face accounting structural, as in `JdDynkinVille`) -/
  hconf : ∀ t ω, X t ω ∈ D
  /-- **the martingale problem**: for every C²-presented test datum with
  the textbook integrability provisos, the compensated certificate
  process is a martingale -/
  mart : ∀ (V : State n → ℝ) (gradV : State n → State n)
      (hessV : State n → Fin n → Fin n → ℝ),
    IsC2Fn V gradV hessV →
    (∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P V gradV hessV (X (Real.toNNReal s) ω))
      volume 0 t) →
    (∀ t : ℝ≥0, Integrable (fun ω => V (X t ω)) (volume : Measure Ω)) →
    Martingale (fun (t : ℝ≥0) (ω : Ω) => V (X t ω)
      - ∫ s in (0:ℝ)..(t:ℝ),
          generator P V gradV hessV (X (Real.toNNReal s) ω))
      ℱ (volume : Measure Ω)

namespace MpSolution

variable {Ω : Type*} [MeasureSpace Ω] {P : JdProfile n m}
  {D : Set (State n)} {V : State n → ℝ} {gradV : State n → State n}
  {hessV : State n → Fin n → Fin n → ℝ}

/-- **Continuous-time Dynkin, derived, at the multi-leg generator**: a
certified nonpositive generator row on the working domain makes the
certificate observable a continuous-time supermartingale along any
martingale-problem solution. The analytic content is exactly the
compensator argument of the optional-sampling package — which never
inspects the generator, which is why this proof is the SDE module's
verbatim; adaptedness of the compensator is derived
(certificate-along-process minus martingale), never assumed. -/
theorem supermartingale_of_gen_nonpos
    [IsProbabilityMeasure (volume : Measure Ω)]
    (mp : MpSolution P D Ω) (hC2 : IsC2Fn V gradV hessV)
    (hgint : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P V gradV hessV (mp.X (Real.toNNReal s) ω))
      volume 0 t)
    (hVint : ∀ t : ℝ≥0, Integrable (fun ω => V (mp.X t ω))
      (volume : Measure Ω))
    (hrow : ∀ z ∈ D, generator P V gradV hessV z ≤ 0) :
    Supermartingale (fun (t : ℝ≥0) (ω : Ω) => V (mp.X t ω)) mp.ℱ
      (volume : Measure Ω) := by
  have hmart := mp.mart V gradV hessV hC2 hgint hVint
  refine OptionalSamplingRC.supermartingale_of_compensator_nonpos (ℱ := mp.ℱ)
    (fun t ω => V (mp.X t ω))
    (fun s ω => generator P V gradV hessV (mp.X (Real.toNNReal s) ω))
    hmart ?_ hVint hgint
    (fun ω s _ => hrow _ (mp.hconf _ _))
  intro t
  have h1 : StronglyMeasurable[mp.ℱ t] fun ω => V (mp.X t ω) :=
    hC2.continuous_V.comp_stronglyMeasurable (mp.hadapted t)
  have h2 : StronglyMeasurable[mp.ℱ t] fun ω => V (mp.X t ω)
      - ∫ s in (0:ℝ)..(t:ℝ),
          generator P V gradV hessV (mp.X (Real.toNNReal s) ω) :=
    hmart.stronglyAdapted t
  have heq : (fun ω => ∫ s in (0:ℝ)..(t:ℝ),
      generator P V gradV hessV (mp.X (Real.toNNReal s) ω))
      = fun ω => V (mp.X t ω)
        - (V (mp.X t ω) - ∫ s in (0:ℝ)..(t:ℝ),
            generator P V gradV hessV (mp.X (Real.toNNReal s) ω)) := by
    funext ω; ring
  have hmeas : Measurable[mp.ℱ t] fun ω => ∫ s in (0:ℝ)..(t:ℝ),
      generator P V gradV hessV (mp.X (Real.toNNReal s) ω) := by
    rw [heq]
    exact (h1.sub h2).measurable
  exact hmeas

/-- The filtration sampled along a monotone grid. -/
def sampledFiltration (mp : MpSolution P D Ω) (τ : ℕ → ℝ≥0)
    (hτ : Monotone τ) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq k := mp.ℱ (τ k)
  mono' _ _ hkj := mp.ℱ.mono' (hτ hkj)
  le' k := mp.ℱ.le' (τ k)

/-- **The class field, discharged at the multi-leg generator**: a
martingale-problem solution, sampled along any monotone grid, is a
`JdDynkinVille` instance whose analytic field `dynkin_of_gen_nonpos` is
a THEOREM — the Dynkin content is derived, and the per-model residue is
being a martingale-problem solution (the community's own object) plus
the per-datum integrability provisos. The avoid and deadline verdict
classes then apply with zero re-proof. -/
noncomputable def toJdDynkinVille
    [IsProbabilityMeasure (volume : Measure Ω)]
    (mp : MpSolution P D Ω) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hC2 : IsC2Fn V gradV hessV)
    (hgint : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P V gradV hessV (mp.X (Real.toNNReal s) ω))
      volume 0 t)
    (hVint : ∀ t : ℝ≥0, Integrable (fun ω => V (mp.X t ω))
      (volume : Measure Ω)) :
    JdDynkinVille P D V gradV hessV Ω where
  X k ω := mp.X (τ k) ω
  𝒢 := mp.sampledFiltration τ hτ
  confined k ω := mp.hconf (τ k) ω
  dynkin_of_gen_nonpos hgen := by
    have hsup := mp.supermartingale_of_gen_nonpos hC2 hgint hVint hgen
    exact ⟨fun k => hsup.1 (τ k),
      fun k j hkj => hsup.2.1 (τ k) (τ j) (hτ hkj),
      fun k => hsup.2.2 (τ k)⟩

end MpSolution

/-! ## 3. The headlines, with the fences gone

The landed SDE headlines carry `hkill : P₀.kill = 0` and a single-
Dirac-leg `hlegs` hypothesis, because the single-leg splice needs them.
The multi-leg splice needs nothing, so the headlines below hold for
EVERY polynomial presentation — killing, finitely many jump legs,
sub-stochastic mixture resets. -/

section Headline

/-- **Community semantics to certified verdict** (avoid row, compiled
form, no fences): a martingale-problem solution of the presentation's
evaluated multi-leg profile, together with the checker's own compiled
row — `aeval z (genPoly P₀ V₀) ≤ 0` on `D`, the exact-rational object a
certificate row bounds — and the nonneg/floor validity rows, yields the
probability verdict `a · P(∃k, X_{τ_k} ∈ Bad) ≤ 𝔼[V(X_{τ_0})]`, for
EVERY presentation `P₀`. The compilation side is the hypothesis-free
splice (`JumpDiffusion.genPoly_eval_eq_generator`); the derivative gap
is closed by `isC2Fn_poly`, unchanged; the verdict side is
`JdDynkinVille.avoid_row` through `Qtsl.Ville.reach_avoid`. -/
theorem mp_avoid_row_of_genPoly
    [IsProbabilityMeasure (volume : Measure Ω)]
    {P₀ : PolyProfile n m} {D : Set (State n)}
    (V₀ : MvPolynomial (Fin n) ℚ)
    (mp : MpSolution P₀.toJd D Ω)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hgint : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
      volume 0 t)
    (hVint : ∀ t : ℝ≥0, Integrable
      (fun ω => (aeval (mp.X t ω) V₀ : ℝ)) (volume : Measure Ω))
    (hrow : ∀ z ∈ D, (aeval z (genPoly P₀ V₀) : ℝ) ≤ 0)
    (hnonneg : ∀ z ∈ D, 0 ≤ (aeval z V₀ : ℝ))
    {Bad : Set (State n)} {a : ℝ}
    (hfloor : ∀ z ∈ Bad, a ≤ (aeval z V₀ : ℝ)) :
    ENNReal.ofReal a * volume {ω | ∃ k, mp.X (τ k) ω ∈ Bad}
      ≤ ENNReal.ofReal (∫ ω, (aeval (mp.X (τ 0) ω) V₀ : ℝ)) := by
  have hsplice : ∀ z : State n,
      (aeval z (genPoly P₀ V₀) : ℝ)
        = generator P₀.toJd (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ)) z :=
    fun z => genPoly_eval_eq_generator P₀ V₀ z
  have hgint' : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P₀.toJd (fun w => (aeval w V₀ : ℝ))
        (fun w i => (aeval w (pderiv i V₀) : ℝ))
        (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
        (mp.X (Real.toNNReal s) ω)) volume 0 t := by
    intro ω t
    have heq : (fun s : ℝ =>
        (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
        = fun s : ℝ => generator P₀.toJd
            (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
            (mp.X (Real.toNNReal s) ω) :=
      funext fun s => hsplice _
    rw [← heq]
    exact hgint ω t
  exact (mp.toJdDynkinVille τ hτ (isC2Fn_poly V₀) hgint' hVint).avoid_row
    (fun z hz => hsplice z ▸ hrow z hz) hnonneg hfloor

/-- The verdict at a deterministic start (floor at `1`), no fences:
`P(∃k, X_{τ_k} ∈ Bad) ≤ V(z₀)` for every presentation. -/
theorem mp_avoid_init_of_genPoly
    [IsProbabilityMeasure (volume : Measure Ω)]
    {P₀ : PolyProfile n m} {D : Set (State n)}
    (V₀ : MvPolynomial (Fin n) ℚ)
    (mp : MpSolution P₀.toJd D Ω)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hgint : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
      volume 0 t)
    (hVint : ∀ t : ℝ≥0, Integrable
      (fun ω => (aeval (mp.X t ω) V₀ : ℝ)) (volume : Measure Ω))
    (hrow : ∀ z ∈ D, (aeval z (genPoly P₀ V₀) : ℝ) ≤ 0)
    (hnonneg : ∀ z ∈ D, 0 ≤ (aeval z V₀ : ℝ))
    {Bad : Set (State n)} {z0 : State n}
    (hstart : ∀ ω : Ω, mp.X (τ 0) ω = z0)
    (hfloor : ∀ z ∈ Bad, 1 ≤ (aeval z V₀ : ℝ)) :
    volume {ω | ∃ k, mp.X (τ k) ω ∈ Bad}
      ≤ ENNReal.ofReal (aeval z0 V₀ : ℝ) := by
  have hsplice : ∀ z : State n,
      (aeval z (genPoly P₀ V₀) : ℝ)
        = generator P₀.toJd (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ)) z :=
    fun z => genPoly_eval_eq_generator P₀ V₀ z
  have hgint' : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P₀.toJd (fun w => (aeval w V₀ : ℝ))
        (fun w i => (aeval w (pderiv i V₀) : ℝ))
        (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
        (mp.X (Real.toNNReal s) ω)) volume 0 t := by
    intro ω t
    have heq : (fun s : ℝ =>
        (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
        = fun s : ℝ => generator P₀.toJd
            (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
            (mp.X (Real.toNNReal s) ω) :=
      funext fun s => hsplice _
    rw [← heq]
    exact hgint ω t
  exact (mp.toJdDynkinVille τ hτ (isC2Fn_poly V₀) hgint' hVint).avoid_row_init
    (fun z hz => hsplice z ▸ hrow z hz) hnonneg hfloor hstart

end Headline

/-! ## 4. The landed route factors: solutions transport along the
identity of operators -/

/-- The canonical single-Dirac embedding at the semantic stratum: an
SDE profile is a multi-leg profile with zero killing and one Dirac leg
at full mass. -/
noncomputable def _root_.Qtsl.SdeGenerator.SdeProfile.toJd
    (P : SdeProfile n m) : JdProfile n m where
  f := P.f
  σ := P.σ
  kill _ := 0
  legs := [(P.lam, [((1 : ℝ), P.g)])]

/-- **Identity of operators at the semantic face**: the multi-leg
generator of the embedded profile is the landed single-Dirac generator
on the nose. -/
theorem generator_toJd (P : SdeProfile n m) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) :
    generator P.toJd V gradV hessV z
      = SdeGenerator.generator P V gradV hessV z := by
  have h := generator_one_dirac (P := P.toJd) (lam := P.lam) (g := P.g)
    (fun _ => rfl) rfl V gradV hessV z
  rw [h]
  rfl

/-- **Solutions transport along the identity of operators**: a
martingale-problem solution in the landed single-leg sense is one in
the multi-leg sense at the embedded profile — so the landed verdict
route factors through this module's, verdicts included. -/
noncomputable def _root_.Qtsl.SdeMartingaleProblem.MpSolution.toJd
    {P : SdeProfile n m} {D : Set (State n)} {Ω : Type*} [MeasureSpace Ω]
    (mp : SdeMartingaleProblem.MpSolution P D Ω) :
    MpSolution P.toJd D Ω where
  X := mp.X
  ℱ := mp.ℱ
  hadapted := mp.hadapted
  hpath := mp.hpath
  hconf := mp.hconf
  mart V gradV hessV hC2 hgint hVint := by
    have hg : ∀ z, generator P.toJd V gradV hessV z
        = SdeGenerator.generator P V gradV hessV z :=
      generator_toJd P V gradV hessV
    have hgint' : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
        (fun s => SdeGenerator.generator P V gradV hessV
          (mp.X (Real.toNNReal s) ω)) volume 0 t := by
      intro ω t
      simpa only [hg] using hgint ω t
    have h := mp.mart V gradV hessV hC2 hgint' hVint
    simpa only [hg] using h

/-! ## 5. Positive control: live rates, genuine mixture, zero dynamics -/

section Control

/-- The control presentation: zero drift, zero diffusion, zero killing,
and TWO jump legs with LIVE rates — a Dirac identity reset at rate `x²`,
and a genuine two-map mixture (identity at weight `1/2` twice, total
mass one) at rate `1`. The dynamics are zero because every reset is the
identity at full mass — the honest scope of a constant-process control
— but the rates, the leg plurality, and the mixture plurality are all
live, which the landed single-leg control could not exhibit. -/
noncomputable def idResetPoly : PolyProfile 1 1 where
  f _ := 0
  σp _ _ := 0
  kill := 0
  legs :=
    [(X 0 ^ 2, [((1 : ℚ), fun i => X i)]),
     (C 1, [((1/2 : ℚ), fun i => X i), ((1/2 : ℚ), fun i => X i)])]

/-- The computed generator of the control presentation vanishes for
every certificate body: each identity-reset leg's transfer is the
observable itself at total mass one. -/
theorem genPoly_idResetPoly (V : MvPolynomial (Fin 1) ℚ) :
    genPoly idResetPoly V = 0 := by
  simp [genPoly, idResetPoly, PolyProfile.gram, transferMix, bind₁_X_left]
  rw [← add_mul, ← C_add]
  norm_num

/-- The evaluated (semantic) generator of the control presentation
vanishes at EVERY test datum — no linkage needed: the drift, diffusion,
and killing families are zero, and each leg's semantic transfer is the
observable at total mass one. -/
theorem generator_toJd_idResetPoly (V : State 1 → ℝ)
    (gradV : State 1 → State 1) (hessV : State 1 → Fin 1 → Fin 1 → ℝ)
    (z : State 1) :
    generator idResetPoly.toJd V gradV hessV z = 0 := by
  simp [generator, PolyProfile.toJd, idResetPoly, evalMixture,
    JdProfile.gram, JdProfile.driftDiff, SdeGenerator.SdeProfile.gram,
    transferSum]
  ring

variable {Ω : Type*} [MeasureSpace Ω]

/-- The constant process solves the control presentation's martingale
problem on the universal domain: the compensated process is constant,
hence a martingale. Non-vacuity witness for the multi-leg `MpSolution`
(the shape check that every field is constructible); the zero dynamics
are the honest scope — see the module fences. -/
noncomputable def mpConstJd [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) :
    MpSolution idResetPoly.toJd Set.univ Ω where
  X _ _ := x₀
  ℱ := ⟨fun _ => ⊥, monotone_const, fun _ => bot_le⟩
  hadapted _ := stronglyMeasurable_const
  hpath _ := measurable_const
  hconf _ _ := Set.mem_univ _
  mart V gradV hessV _ _ _ := by
    have hshape : (fun (t : ℝ≥0) (ω : Ω) => V x₀
        - ∫ s in (0:ℝ)..(t:ℝ),
            generator idResetPoly.toJd V gradV hessV x₀)
        = fun _ _ => V x₀ := by
      funext t ω
      simp [generator_toJd_idResetPoly]
    show Martingale (fun (t : ℝ≥0) (ω : Ω) => V x₀
      - ∫ s in (0:ℝ)..(t:ℝ),
          generator idResetPoly.toJd V gradV hessV x₀) _ _
    rw [hshape]
    exact martingale_const _ _ _

@[simp] theorem mpConstJd_X [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) (t : ℝ≥0) (ω : Ω) : (mpConstJd x₀).X t ω = x₀ := rfl

/-- **End-to-end positive control**: the fenceless headline verdict
derived for the constant solution of the control presentation at the
certificate `V = X·X` — statics, hypothesis-free splice, transplanted
engine, sampling, and the Ville verdict all exercised; nothing assumed,
and no fence arguments exist to pass at the call site. -/
theorem mp_control [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) {Bad : Set (State 1)}
    (hfloor : ∀ z ∈ Bad,
      1 ≤ (aeval z (X 0 * X 0 : MvPolynomial (Fin 1) ℚ) : ℝ)) :
    volume {_ω : Ω | ∃ _k : ℕ, x₀ ∈ Bad}
      ≤ ENNReal.ofReal (aeval x₀ (X 0 * X 0 : MvPolynomial (Fin 1) ℚ) : ℝ) := by
  have h := mp_avoid_init_of_genPoly (Ω := Ω)
    (P₀ := idResetPoly) (X 0 * X 0) (mpConstJd x₀)
    (fun k => (k : ℝ≥0)) Nat.mono_cast
    (fun ω t => by
      simp only [genPoly_idResetPoly, map_zero]
      exact intervalIntegrable_const)
    (fun t => by
      simp only [mpConstJd_X]
      exact integrable_const _)
    (fun z _ => by simp [genPoly_idResetPoly])
    (fun z _ => by
      rw [map_mul, aeval_X]
      exact mul_self_nonneg _)
    (z0 := x₀) (fun ω => rfl) hfloor
  simpa only [mpConstJd_X] using h

end Control

end JumpDiffusion

end Qtsl
