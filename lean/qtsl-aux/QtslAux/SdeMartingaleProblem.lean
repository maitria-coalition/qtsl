import QtslAux.SdeGeneratorPoly
import OptionalSamplingRC.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The martingale problem for SDE profiles, and the Dynkin discharge

This module ties the community's own solution semantics for stochastic
differential equations to the certificate machinery of
`QtslAux.SdeGenerator`, and closes the loop end-to-end for the compiled
polynomial class.

## Why the martingale problem

The standard characterisation of a jump-diffusion by its generator is
the **martingale problem** (Stroock–Varadhan, *Multidimensional
Diffusion Processes*; Ethier–Kurtz, *Markov Processes: Characterization
and Convergence*, Ch. 4, in the generator-as-pairs formulation): `X`
solves the martingale problem for `𝒜` iff for every admissible test
observable `V`,

  `V(X_t) − ∫₀ᵗ (𝒜V)(X_s) ds`  is a martingale.

Weak SDE solutions and martingale-problem solutions coincide — that
equivalence is the community's own theorem (Kurtz; Stroock–Varadhan),
CITED here as the license that the martingale problem is Itô-solution
semantics, and deliberately not mechanized: the mathlib pin this
package builds against carries no stochastic integral, no Itô formula,
no quadratic variation, so a strong-solution left edge is out of reach
upstream, while `Martingale`/`Supermartingale` are index-generic and
make the martingale problem statable today. For the polynomial fragment
this module proves end-to-end, the martingale problem is not even a
workaround: **polynomial diffusions are defined by the martingale
problem with polynomial test functions in the literature itself**
(Filipović–Larsson). The jump term rides the integro-differential
generator (Ethier–Kurtz; Davis for the pure-jump face).

The pairs of the generator-as-pairs formulation are
`(V, generator P V gradV hessV)` with the derivative data honestly
linked by `IsC2Fn` — the C² test class, presented the way the generator
consumes it. The integrability provisos on the `mart` field are the
textbook's own standing assumptions for unbounded test functions. The
confinement field makes this the **stopped/confined** martingale
problem (Ethier–Kurtz's stopped problem): the working domain `D` is
where the certified row holds, exactly as in `SdeDynkinVille`.

## What is derived (the class field, discharged)

`SdeGenerator.SdeDynkinVille` carries one deliberately-hypothesised
analytic field: certified `𝒜V ≤ 0` on `D` implies the sampled `V(X_k)`
is a supermartingale. **For martingale-problem solutions that field is
a THEOREM** (`MpSolution.toSdeDynkinVille`): the analytic content
reduces to the compensator argument — martingale plus nonincreasing
compensation is a supermartingale
(`OptionalSamplingRC.supermartingale_of_compensator_nonpos`, from the
sibling package) — and what remains per model is *being a solution*
(the community's own object) plus the per-datum integrability provisos.
A companion development at the segment stratum
(`QtslAux.LayerD.MPDischarge`) runs the same doctrine for hybrid-system
segments; here the generator is the SDE profile's actual textbook
operator and the consumer is the profile-level verdict class.

The headline (`mp_avoid_row_of_genPoly`, `mp_avoid_init_of_genPoly`)
closes the square for the compiled polynomial class: a
martingale-problem solution of the presentation's evaluated profile,
plus the **checker's own row** (`aeval z (genPoly P₀ V₀) ≤ 0` on `D`,
exact-rational) and the validity rows, yields the probability verdicts
`a · P(∃k, X_{τ_k} ∈ Bad) ≤ 𝔼[V(X_{τ_0})]` — community semantics to
certified verdict through the splice (`genPoly_eval_eq_generator`),
with the statics closing the derivative gap: `isC2Fn_poly` is the
order-1 AND order-2 formal-vs-analytic identification (the Fréchet
derivative of `aeval · (pderiv j V)` is the formal
`pderiv i (pderiv j V)` row).

## Fences (named, honest)

* Verdicts are on the sampled grid `τ`; the continuum-time supremum
  needs a.s. path regularity, constructor-side (as in
  `SdeDynkinVille`).
* Martingale-problem well-posedness (existence/uniqueness for a given
  profile) is not claimed; the left edge is the solution *concept*.
* The strong-solution (Itô-integral) face is absent upstream at the
  pin; revisit when mathlib lands stochastic integration.
* The positive control (`mpConst`/`mp_control`) is a zero-dynamics
  non-vacuity and shape witness exercising every hypothesis of the
  compose path; a nonzero-drift deterministic instance needs a
  continuous-partials⟹Fréchet composition lemma (or per-instance FTC)
  and is deliberately out of scope here.

The polynomial Fréchet-gradient statics below are self-contained in
this package (the checker-side package downstream carries the same
statics for its deterministic profiles; the dependency between the
packages points the other way, so this package vendors its own copy).

No `sorry`; axiom receipts ride the package's `AxiomReceipts` target.
-/

open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal

namespace Qtsl

namespace SdeMartingaleProblem

open SdeGenerator SdeGeneratorPoly

/-! ## 1. The polynomial Fréchet-gradient statics

The Fréchet derivative of polynomial evaluation IS the formal `pderiv`
gradient — the mathlib pin has analyticity of polynomial evaluation but
no derivative formula. -/

section PolyStatics

variable {n : ℕ}

/-- The formal-gradient continuous linear map of a polynomial at a point:
`∑ i, (∂ᵢV)(x) • projᵢ`. Applying it to a velocity `v` gives
`∑ i, (∂ᵢV)(x) * vᵢ` — the generator's row shape. -/
noncomputable def polyGradCLM (V : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i V) • ContinuousLinearMap.proj i

@[simp] theorem polyGradCLM_apply (V : MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    polyGradCLM V x v = ∑ i, eval x (pderiv i V) * v i := by
  simp [polyGradCLM, smul_eq_mul]

theorem polyGradCLM_C (a : ℝ) (x : Fin n → ℝ) :
    polyGradCLM (MvPolynomial.C a) x = 0 := by
  ext v
  simp [polyGradCLM_apply]

theorem polyGradCLM_add (p q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    polyGradCLM (p + q) x = polyGradCLM p x + polyGradCLM q x := by
  ext v
  simp [polyGradCLM_apply, add_mul, Finset.sum_add_distrib]

theorem polyGradCLM_mul_X (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (x : Fin n → ℝ) :
    polyGradCLM (p * X j) x
      = eval x p • ContinuousLinearMap.proj j + x j • polyGradCLM p x := by
  ext v
  simp only [polyGradCLM_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hterm : ∀ i : Fin n,
      eval x (pderiv i (p * X j)) * v i
        = eval x (pderiv i p) * v i * x j
          + (if j = i then eval x p * v i else 0) := by
    intro i
    by_cases h : j = i
    · simp only [h, pderiv_mul, pderiv_X_self, eval_add, eval_mul, eval_X,
        mul_one, if_pos]
      ring
    · simp only [pderiv_mul, pderiv_X_of_ne h, eval_mul, eval_X,
        mul_zero, add_zero, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq, ← Finset.sum_mul]
  simp only [Finset.mem_univ, if_true]
  ring

/-- THE identification: the Fréchet derivative of polynomial evaluation
is the formal `pderiv` gradient. -/
theorem hasFDerivAt_eval_poly (V : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y V) (polyGradCLM V x) x := by
  induction V using MvPolynomial.induction_on with
  | C a =>
      rw [polyGradCLM_C]
      have h := hasFDerivAt_const (𝕜 := ℝ) (E := Fin n → ℝ) a x
      have heq : (fun _ : Fin n → ℝ => a)
          = fun y : Fin n → ℝ => eval y (MvPolynomial.C a) :=
        funext fun y => (eval_C (σ := Fin n) a).symm
      rw [heq] at h
      exact h
  | add p q hp hq =>
      rw [polyGradCLM_add]
      have h := hp.add hq
      have heq : ((fun y : Fin n → ℝ => eval y p) + fun y : Fin n → ℝ => eval y q)
          = fun y : Fin n → ℝ => eval y (p + q) :=
        funext fun y => by simp [Pi.add_apply, eval_add]
      rw [heq] at h
      exact h
  | mul_X p j hp =>
      rw [polyGradCLM_mul_X]
      have hproj : HasFDerivAt (fun y : Fin n → ℝ => y j)
          (ContinuousLinearMap.proj j) x :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
          j).hasFDerivAt
      have h := hp.mul hproj
      have heq : ((fun y : Fin n → ℝ => eval y p) * fun y : Fin n → ℝ => y j)
          = fun y : Fin n → ℝ => eval y (p * X j) :=
        funext fun y => by simp [Pi.mul_apply, eval_mul, eval_X]
      rw [heq] at h
      exact h

/-- Evaluation of a rational-coefficient certificate polynomial over ℝⁿ
is evaluation of its coefficient-mapped image. -/
theorem aeval_eq_eval_map_rat (V : MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) :
    aeval x V = eval x (map (algebraMap ℚ ℝ) V) := by
  rw [aeval_def, eval₂_eq_eval_map]

/-- The identification, rational-certificate form: the derivative of
`aeval · V` is the formal gradient computed in exact rational
arithmetic, coefficient-mapped. -/
theorem hasFDerivAt_aeval_poly (V : MvPolynomial (Fin n) ℚ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => aeval y V)
      (polyGradCLM (map (algebraMap ℚ ℝ) V) x) x := by
  have h := hasFDerivAt_eval_poly (map (algebraMap ℚ ℝ) V) x
  simpa only [aeval_eq_eval_map_rat] using h

end PolyStatics

/-! ## 2. The C² test class, presented as the generator consumes it -/

section C2

variable {n : ℕ}

/-- The row continuous linear map of a coefficient row `r`:
`v ↦ ∑ i, r i * v i` — the shape in which the generator's drift term
pairs a gradient with a velocity. -/
noncomputable def rowCLM (r : State n) : (State n) →L[ℝ] ℝ :=
  ∑ i, r i • ContinuousLinearMap.proj i

@[simp] theorem rowCLM_apply (r v : State n) :
    rowCLM r v = ∑ i, r i * v i := by
  simp [rowCLM, smul_eq_mul]

/-- The bridge from the certificate skin to the statics: the row CLM of
the evaluated formal gradient IS `polyGradCLM` of the coefficient-mapped
polynomial (`pderiv_map` commutes the formal gradient past the
coefficient embedding). -/
theorem rowCLM_pderiv_eq_polyGradCLM (V : MvPolynomial (Fin n) ℚ)
    (z : State n) :
    rowCLM (fun i => (aeval z (pderiv i V) : ℝ))
      = polyGradCLM (map (algebraMap ℚ ℝ) V) z := by
  ext v
  simp only [rowCLM_apply, polyGradCLM_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_map, ← aeval_eq_eval_map_rat]

/-- **The C² test datum linkage** — what it means for the triple
`(V, gradV, hessV)` the generator consumes to be an honest
twice-differentiable observable with its genuine derivative data:
`gradV` is the Fréchet derivative of `V` (as a row), `hessV · j` is the
Fréchet derivative of the `j`-th gradient component (so
`hessV z i j = ∂ᵢ∂ⱼV(z)`), and the second partials are continuous (the
textbook C² clause). This is the test class of the martingale problem
below; the community's C² test functions are exactly the functions
presentable this way. -/
structure IsC2Fn (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ) : Prop where
  /-- `gradV` is the genuine Fréchet derivative of `V` -/
  hasFDerivAt_V : ∀ z, HasFDerivAt V (rowCLM (gradV z)) z
  /-- `hessV z · j` is the genuine Fréchet derivative of `gradV · j` -/
  hasFDerivAt_grad : ∀ z j,
    HasFDerivAt (fun w => gradV w j) (rowCLM fun i => hessV z i j) z
  /-- second partials are continuous (C² proper) -/
  continuous_hess : ∀ i j, Continuous fun z => hessV z i j

namespace IsC2Fn

variable {V : State n → ℝ} {gradV : State n → State n}
  {hessV : State n → Fin n → Fin n → ℝ}

theorem continuous_V (h : IsC2Fn V gradV hessV) : Continuous V :=
  continuous_iff_continuousAt.mpr fun z => (h.hasFDerivAt_V z).continuousAt

theorem continuous_grad (h : IsC2Fn V gradV hessV) (j : Fin n) :
    Continuous fun z => gradV z j :=
  continuous_iff_continuousAt.mpr fun z => (h.hasFDerivAt_grad z j).continuousAt

end IsC2Fn

/-- **The polynomial statics, orders 1 and 2**: every certificate
polynomial, with its formal `pderiv` gradient and formal
`pderiv ∘ pderiv` Hessian evaluated over ℝⁿ, is an honest C² test datum.
Order 1 is the identification above; order 2 is the same identification
instantiated at `pderiv j V`. This is what lets the checker's own row
data enter the martingale problem as a community-lawful test
function. -/
theorem isC2Fn_poly (V : MvPolynomial (Fin n) ℚ) :
    IsC2Fn (fun z : State n => (aeval z V : ℝ))
      (fun z i => (aeval z (pderiv i V) : ℝ))
      (fun z i j => (aeval z (pderiv i (pderiv j V)) : ℝ)) where
  hasFDerivAt_V z := by
    rw [rowCLM_pderiv_eq_polyGradCLM]
    exact hasFDerivAt_aeval_poly V z
  hasFDerivAt_grad z j := by
    rw [rowCLM_pderiv_eq_polyGradCLM]
    exact hasFDerivAt_aeval_poly (pderiv j V) z
  continuous_hess i j := SdeGeneratorPoly.continuous_aeval_real _

end C2

/-! ## 3. The left edge: the (stopped) martingale problem for the profile -/

section MartingaleProblem

variable {n m : ℕ}

/-- **The stopped/confined martingale problem for an SDE profile** — the
community's solution semantics (Stroock–Varadhan; Ethier–Kurtz ch. 4,
generator-as-pairs form), stated over the profile's generator: an
adapted, jointly-path-measurable process confined to the closed working
domain `D` such that for every C²-presented test observable satisfying
the textbook integrability provisos, the compensated process
`V(X_t) − ∫₀ᵗ (𝒜V)(X_s) ds` is a martingale. Constructors are the
community's own weak solutions, via the Itô formula (cited, not
mechanized — no stochastic integral exists upstream at the pin); for
polynomial-coefficient profiles the polynomial-test-function
instantiation is itself the literature's definition of polynomial
diffusions (Filipović–Larsson). -/
structure MpSolution (P : SdeProfile n m) (D : Set (State n))
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
  escape-face accounting structural, as in `SdeDynkinVille`) -/
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

variable {Ω : Type*} [MeasureSpace Ω] {P : SdeProfile n m}
  {D : Set (State n)} {V : State n → ℝ} {gradV : State n → State n}
  {hessV : State n → Fin n → Fin n → ℝ}

/-- **Continuous-time Dynkin, derived**: a certified nonpositive
generator row on the working domain makes the certificate observable a
continuous-time supermartingale along any martingale-problem solution.
The analytic content is exactly the compensator argument of the sibling
optional-sampling package; adaptedness of the compensator is derived
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

/-- **The class field, discharged**: a martingale-problem solution,
sampled along any monotone grid, is an `SdeDynkinVille` instance whose
analytic field `dynkin_of_gen_nonpos` is a THEOREM — the Dynkin content
is derived, and the per-model residue is being a martingale-problem
solution (the community's own object) plus the per-datum integrability
provisos. The avoid and deadline verdict classes then apply with zero
re-proof. -/
noncomputable def toSdeDynkinVille
    [IsProbabilityMeasure (volume : Measure Ω)]
    (mp : MpSolution P D Ω) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hC2 : IsC2Fn V gradV hessV)
    (hgint : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator P V gradV hessV (mp.X (Real.toNNReal s) ω))
      volume 0 t)
    (hVint : ∀ t : ℝ≥0, Integrable (fun ω => V (mp.X t ω))
      (volume : Measure Ω)) :
    SdeDynkinVille P D V gradV hessV Ω where
  X k ω := mp.X (τ k) ω
  𝒢 := mp.sampledFiltration τ hτ
  confined k ω := mp.hconf (τ k) ω
  dynkin_of_gen_nonpos hgen := by
    have hsup := mp.supermartingale_of_gen_nonpos hC2 hgint hVint hgen
    exact ⟨fun k => hsup.1 (τ k),
      fun k j hkj => hsup.2.1 (τ k) (τ j) (hτ hkj),
      fun k => hsup.2.2 (τ k)⟩

end MpSolution

end MartingaleProblem

/-! ## 4. The square, closed for the compiled polynomial class -/

section Headline

variable {n m : ℕ} {Ω : Type*} [MeasureSpace Ω]

/-- **Community semantics to certified verdict** (avoid row, compiled
form): a martingale-problem solution of the presentation's evaluated
profile, together with the checker's own compiled row —
`aeval z (genPoly P₀ V₀) ≤ 0` on `D`, the exact-rational object a
certificate row bounds — and the nonneg/floor validity rows, yields the
probability verdict `a · P(∃k, X_{τ_k} ∈ Bad) ≤ 𝔼[V(X_{τ_0})]`. The
compilation side is the splice (`genPoly_eval_eq_generator`); the
derivative gap is closed by `isC2Fn_poly`; the verdict side is
`SdeDynkinVille.avoid_row` through `Qtsl.Ville.reach_avoid`. -/
theorem mp_avoid_row_of_genPoly
    [IsProbabilityMeasure (volume : Measure Ω)]
    {P₀ : PolyProfile n m} {lam : MvPolynomial (Fin n) ℚ}
    {g : Fin n → MvPolynomial (Fin n) ℚ} {D : Set (State n)}
    (hkill : P₀.kill = 0) (hlegs : P₀.legs = [(lam, [((1 : ℚ), g)])])
    (V₀ : MvPolynomial (Fin n) ℚ)
    (mp : MpSolution (P₀.toSde lam g) D Ω)
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
        = generator (P₀.toSde lam g) (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ)) z :=
    fun z => genPoly_eval_eq_generator P₀ lam g V₀ hkill hlegs z
  have hgint' : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator (P₀.toSde lam g) (fun w => (aeval w V₀ : ℝ))
        (fun w i => (aeval w (pderiv i V₀) : ℝ))
        (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
        (mp.X (Real.toNNReal s) ω)) volume 0 t := by
    intro ω t
    have heq : (fun s : ℝ =>
        (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
        = fun s : ℝ => generator (P₀.toSde lam g)
            (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
            (mp.X (Real.toNNReal s) ω) :=
      funext fun s => hsplice _
    rw [← heq]
    exact hgint ω t
  exact (mp.toSdeDynkinVille τ hτ (isC2Fn_poly V₀) hgint' hVint).avoid_row
    (fun z hz => hsplice z ▸ hrow z hz) hnonneg hfloor

/-- The verdict at a deterministic start (floor at `1`):
`P(∃k, X_{τ_k} ∈ Bad) ≤ V(z₀)`. -/
theorem mp_avoid_init_of_genPoly
    [IsProbabilityMeasure (volume : Measure Ω)]
    {P₀ : PolyProfile n m} {lam : MvPolynomial (Fin n) ℚ}
    {g : Fin n → MvPolynomial (Fin n) ℚ} {D : Set (State n)}
    (hkill : P₀.kill = 0) (hlegs : P₀.legs = [(lam, [((1 : ℚ), g)])])
    (V₀ : MvPolynomial (Fin n) ℚ)
    (mp : MpSolution (P₀.toSde lam g) D Ω)
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
        = generator (P₀.toSde lam g) (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ)) z :=
    fun z => genPoly_eval_eq_generator P₀ lam g V₀ hkill hlegs z
  have hgint' : ∀ (ω : Ω) (t : ℝ), IntervalIntegrable
      (fun s => generator (P₀.toSde lam g) (fun w => (aeval w V₀ : ℝ))
        (fun w i => (aeval w (pderiv i V₀) : ℝ))
        (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
        (mp.X (Real.toNNReal s) ω)) volume 0 t := by
    intro ω t
    have heq : (fun s : ℝ =>
        (aeval (mp.X (Real.toNNReal s) ω) (genPoly P₀ V₀) : ℝ))
        = fun s : ℝ => generator (P₀.toSde lam g)
            (fun w => (aeval w V₀ : ℝ))
            (fun w i => (aeval w (pderiv i V₀) : ℝ))
            (fun w i j => (aeval w (pderiv i (pderiv j V₀)) : ℝ))
            (mp.X (Real.toNNReal s) ω) :=
      funext fun s => hsplice _
    rw [← heq]
    exact hgint ω t
  exact (mp.toSdeDynkinVille τ hτ (isC2Fn_poly V₀) hgint' hVint).avoid_row_init
    (fun z hz => hsplice z ▸ hrow z hz) hnonneg hfloor hstart

end Headline

/-! ## 5. Positive control: the compose path, exercised end-to-end -/

section Control

/-- The zero presentation: zero drift, one zero diffusion column, no
killing, one Dirac jump leg at rate `0` with the identity reset — the
single-Dirac-leg shape the splice demands, with all dynamics off. -/
noncomputable def zeroPoly : PolyProfile 1 1 where
  f _ := 0
  σp _ _ := 0
  kill := 0
  legs := [(0, [((1 : ℚ), fun i => X i)])]

/-- The computed generator of the zero presentation vanishes for every
certificate body. -/
theorem genPoly_zeroPoly (V : MvPolynomial (Fin 1) ℚ) :
    genPoly zeroPoly V = 0 := by
  simp [genPoly, zeroPoly, PolyProfile.gram]

/-- The evaluated (semantic) generator of the zero presentation vanishes
at EVERY test datum — no linkage needed: all three generator families
carry zero coefficients. -/
theorem generator_toSde_zeroPoly (V : State 1 → ℝ)
    (gradV : State 1 → State 1) (hessV : State 1 → Fin 1 → Fin 1 → ℝ)
    (z : State 1) :
    generator (zeroPoly.toSde 0 fun i => X i) V gradV hessV z = 0 := by
  simp [SdeGenerator.generator, PolyProfile.toSde,
    SdeGenerator.SdeProfile.gram, zeroPoly]

variable {Ω : Type*} [MeasureSpace Ω]

/-- The constant process solves the zero presentation's martingale
problem on the universal domain: the compensated process is constant,
hence a martingale. Non-vacuity witness for `MpSolution` (the shape
check that every field is constructible); the zero dynamics are the
honest scope — see the module fences. -/
noncomputable def mpConst [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) :
    MpSolution (zeroPoly.toSde 0 fun i => X i) Set.univ Ω where
  X _ _ := x₀
  ℱ := ⟨fun _ => ⊥, monotone_const, fun _ => bot_le⟩
  hadapted _ := stronglyMeasurable_const
  hpath _ := measurable_const
  hconf _ _ := Set.mem_univ _
  mart V gradV hessV _ _ _ := by
    have hshape : (fun (t : ℝ≥0) (ω : Ω) => V x₀
        - ∫ s in (0:ℝ)..(t:ℝ),
            generator (zeroPoly.toSde 0 fun i => X i) V gradV hessV x₀)
        = fun _ _ => V x₀ := by
      funext t ω
      simp [generator_toSde_zeroPoly]
    show Martingale (fun (t : ℝ≥0) (ω : Ω) => V x₀
      - ∫ s in (0:ℝ)..(t:ℝ),
          generator (zeroPoly.toSde 0 fun i => X i) V gradV hessV x₀) _ _
    rw [hshape]
    exact martingale_const _ _ _

@[simp] theorem mpConst_X [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) (t : ℝ≥0) (ω : Ω) : (mpConst x₀).X t ω = x₀ := rfl

/-- **End-to-end positive control**: the headline verdict derived for
the constant solution of the zero presentation at the certificate
`V = X·X` — statics, splice, engine, sampling, and the Ville verdict all
exercised; nothing assumed. -/
theorem mp_control [IsProbabilityMeasure (volume : Measure Ω)]
    (x₀ : State 1) {Bad : Set (State 1)}
    (hfloor : ∀ z ∈ Bad,
      1 ≤ (aeval z (X 0 * X 0 : MvPolynomial (Fin 1) ℚ) : ℝ)) :
    volume {_ω : Ω | ∃ _k : ℕ, x₀ ∈ Bad}
      ≤ ENNReal.ofReal (aeval x₀ (X 0 * X 0 : MvPolynomial (Fin 1) ℚ) : ℝ) := by
  have h := mp_avoid_init_of_genPoly (Ω := Ω)
    (P₀ := zeroPoly) (lam := 0) (g := fun i => X i)
    rfl rfl (X 0 * X 0) (mpConst x₀)
    (fun k => (k : ℝ≥0)) Nat.mono_cast
    (fun ω t => by
      simp only [genPoly_zeroPoly, map_zero]
      exact intervalIntegrable_const)
    (fun t => by
      simp only [mpConst_X]
      exact integrable_const _)
    (fun z _ => by simp [genPoly_zeroPoly])
    (fun z _ => by
      rw [map_mul, aeval_X]
      exact mul_self_nonneg _)
    (z0 := x₀) (fun ω => rfl) hfloor
  simpa only [mpConst_X] using h

end Control

end SdeMartingaleProblem

end Qtsl
