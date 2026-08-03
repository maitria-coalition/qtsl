import QtslAux.Ville
import QtslAux.Deadline

/-! # The SDE profile: extended generator, the Dynkin class, verdict transfers

This module carries the certificate-facing semantics of stochastic
differential equation profiles: the profile data (drift, per-driver
diffusion columns, jump rate and reset), the derived covariance and its
soundness pair, the extended generator

  `𝒜V = ∇V·f + ½ Σᵢⱼ aᵢⱼ ∂ᵢⱼV + λ·(V∘g − V)`,

and the class `SdeDynkinVille` through which certified generator
inequalities become probability bounds via the Ville and deadline stock
of this package.

## The profile

`SdeProfile n m` records drift `f`, diffusion COLUMNS `σ k` — one column
per independent Brownian driver, state-dependent entries welcome — and
the jump pair `lam`/`g` (`lam = 0` is the pure-diffusion face). The
covariance is DERIVED, never stored: `SdeProfile.gram` is
`a = Σ_k σ^k (σ^k)ᵀ`, and the pair `gram_symm` /
`gram_quadForm_nonneg` (`a(z) ⪰ 0`, by the sum-of-squares identity) is
the soundness content of that representation choice. `gradV`/`hessV`
enter the generator as derivative *data*; the identification of formal
with analytic derivatives for the polynomial certificate class lives in
the companion module `QtslAux.SdeMartingaleProblem` (`isC2Fn_poly`).
The degeneracy theorems check the expected collapses: no drivers gives
the jump-process (PDMP) generator, no drivers and no jumps the
deterministic `f·∇V`, no jumps the diffusion generator.
`lam_nonneg_of_rate_row` is the semantic face of the rate-validity row
`−λ(z) ≤ 0`: a sign-flipped rate only ever makes the generator
inequality easier while destroying the model, which is why the rate row
is a refusal instrument and not decoration.

## The one analytic field, deliberately a hypothesis

`SdeDynkinVille` is a sampled stopped state process confined to a
closed working domain, carrying ONE stochastic-analysis field —
`dynkin_of_gen_nonpos`, in conditional form: whenever the generator row
is certified nonpositive on the domain, the certificate observable
rides the sampled chain as a supermartingale. This is the Dynkin
formula for C² observables up to bounded stopping, plus optional
sampling and Fatou (Dynkin, *Markov Processes*, Ch. V; Ethier–Kurtz,
*Markov Processes: Characterization and Convergence*, Ch. 4; Davis,
*Markov Models and Optimization*, Ch. 2, for the pure-jump face) —
textbook-standard for polynomial coefficients on compacts, and
deliberately a field of the class rather than a theorem of this module:
no statement below mentions a stochastic integral, an Itô formula, or a
Brownian motion. The companion module `QtslAux.SdeMartingaleProblem`
DISCHARGES the field for solutions presented by their martingale
problem (`MpSolution.toSdeDynkinVille`): there the analytic content
reduces to a compensator argument, and what remains per model is the
presentation itself plus per-datum integrability provisos.

Escape-face accounting is rendered structurally: the `confined` field
demands the stopped chain stay in the closed working domain. The
verdicts are on the sampled grid; the continuum-time supremum needs
almost-sure path regularity and stays constructor-side.

## Verdict transfers (honest Lean over the package's Ville/deadline stock)

* `SdeDynkinVille.avoid_row` / `avoid_row_div` / `avoid_row_init` —
  the avoidance certificate class: gen (`𝒜V ≤ 0` on `D`), floor
  (`V ≥ a` on `Bad`), nonneg (`V ≥ 0` on `D`) rows give
  `a · P(∃k, X_k ∈ Bad) ≤ 𝔼[V(X₀)]`, through `Qtsl.Ville.reach_avoid`.
* `SdeDynkinVille.discounted_deadline_row` — the discounted-deadline
  certificate class (`𝒜V + θV ≤ 0` off the target, floor off the
  target): `a · P(no visit by time k) ≤ βᵏ · 𝔼[V(X₀)]` at contraction
  `β`, through `Qtsl.Deadline.deadline_tail`.

The compensated (`𝒜V ≤ β`) drift-bound face is deliberately not here:
its transfer engine is a nonnegative-compensator Ville inequality this
package does not yet carry.

No `sorry`; axiom receipts ride the package's `AxiomReceipts` target.
-/

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Qtsl

namespace SdeGenerator

/-- The state space of the SDE profile at dimension `n` — plain coordinate
tuples. No topology or measure structure is demanded: the transfers below
never need measurability of the state process (the Ville/deadline stock is
measurability-free on the state side). -/
abbrev State (n : ℕ) := Fin n → ℝ

/-- **The SDE profile's field families**, as data: drift `f`, per-driver
diffusion columns `σ` (`m` independent Brownian drivers, one column each,
state-dependent entries welcome), jump rate `lam` and reset `g`
(`lam = 0` is the pure-diffusion face). The covariance `a` is derived
(`SdeProfile.gram`), never stored; validity `λ ≥ 0` is the rate row's job
(`lam_nonneg_of_rate_row`), never assumed silently. -/
structure SdeProfile (n m : ℕ) where
  /-- drift field -/
  f : State n → State n
  /-- diffusion columns, one per independent Brownian driver -/
  σ : Fin m → State n → State n
  /-- jump rate (`0` for pure diffusion) -/
  lam : State n → ℝ
  /-- jump reset map -/
  g : State n → State n

namespace SdeProfile

variable {n m : ℕ}

/-- The derived covariance `a(z) = Σ_k σ^k(z) (σ^k(z))ᵀ`, evaluated
definitionally. -/
noncomputable def gram (P : SdeProfile n m) (z : State n) (i j : Fin n) : ℝ :=
  ∑ k, P.σ k z i * P.σ k z j

/-- The derived covariance is symmetric. -/
theorem gram_symm (P : SdeProfile n m) (z : State n) (i j : Fin n) :
    P.gram z i j = P.gram z j i :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **The derived covariance is positive semidefinite** — the
sum-of-squares identity `vᵀ a(z) v = Σ_k (σ^k(z)·v)²`, which is the whole
soundness content of the "σ-columns, covariance derived never stored"
representation. -/
theorem gram_quadForm_nonneg (P : SdeProfile n m) (z : State n)
    (v : State n) :
    0 ≤ ∑ i, ∑ j, P.gram z i j * (v i * v j) := by
  have key : ∑ i, ∑ j, P.gram z i j * (v i * v j)
      = ∑ k, (∑ i, P.σ k z i * v i) ^ 2 := by
    calc ∑ i, ∑ j, P.gram z i j * (v i * v j)
        = ∑ i, ∑ j, ∑ k, (P.σ k z i * v i) * (P.σ k z j * v j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl
            fun j _ => ?_
          rw [gram, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ i, ∑ k, ∑ j, (P.σ k z i * v i) * (P.σ k z j * v j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (P.σ k z i * v i) * (P.σ k z j * v j) :=
          Finset.sum_comm
      _ = ∑ k, (∑ i, P.σ k z i * v i) * (∑ j, P.σ k z j * v j) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_mul_sum]
      _ = ∑ k, (∑ i, P.σ k z i * v i) ^ 2 :=
          Finset.sum_congr rfl fun k _ => (sq _).symm
  rw [key]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

end SdeProfile

variable {n m : ℕ}

/-- **The extended generator at the profile**:
`𝒜V(z) = Σᵢ ∂ᵢV·fᵢ + ½ Σᵢⱼ aᵢⱼ(z)·∂ᵢⱼV + λ(z)·(V(g z) − V z)`.
`gradV`/`hessV` are derivative *data*; the identification with genuine
Fréchet derivatives for the polynomial certificate class is
`QtslAux.SdeMartingaleProblem.isC2Fn_poly`. -/
noncomputable def generator (P : SdeProfile n m) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) : ℝ :=
  (∑ i, gradV z i * P.f z i)
    + (1 / 2) * (∑ i, ∑ j, P.gram z i j * hessV z i j)
    + P.lam z * (V (P.g z) - V z)

/-- Degeneracy: **no drivers ⟹ the jump-process (PDMP) generator**
`∇V·f + λ(V∘g − V)`. -/
theorem generator_no_drivers (P : SdeProfile n 0) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) :
    generator P V gradV hessV z
      = (∑ i, gradV z i * P.f z i) + P.lam z * (V (P.g z) - V z) := by
  simp [generator, SdeProfile.gram]

/-- Degeneracy: **no drivers, no jumps ⟹ the deterministic generator**
`f·∇V` — the SDE profile degenerates onto the deterministic
directional-derivative row. -/
theorem generator_pure_drift (P : SdeProfile n 0) (hlam : ∀ z, P.lam z = 0)
    (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ) (z : State n) :
    generator P V gradV hessV z = ∑ i, gradV z i * P.f z i := by
  simp [generator, SdeProfile.gram, hlam]

/-- Degeneracy: **no jumps ⟹ the pure-diffusion generator**. -/
theorem generator_no_jump (P : SdeProfile n m) (hlam : ∀ z, P.lam z = 0)
    (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ) (z : State n) :
    generator P V gradV hessV z
      = (∑ i, gradV z i * P.f z i)
        + (1 / 2) * (∑ i, ∑ j, P.gram z i j * hessV z i j) := by
  simp [generator, hlam]

/-- **The rate-validity row's semantic face**: the certificate-facing rate
row `−λ(z) ≤ 0` on the working region is exactly the model-validity
condition `λ ≥ 0` that the jump term's Dynkin reading requires — without
it, a sign-flipped rate makes the generator inequality EASIER while
destroying the model (a negative-rate jump process is not a process),
which is why the rate row is a refusal instrument and not decoration. -/
theorem lam_nonneg_of_rate_row (P : SdeProfile n m) {D : Set (State n)}
    (hrow : ∀ z ∈ D, -P.lam z ≤ 0) : ∀ z ∈ D, 0 ≤ P.lam z :=
  fun z hz => neg_nonpos.1 (hrow z hz)

variable {Ω : Type*} [MeasureSpace Ω]

/-- **The Dynkin class** (avoid form): a sampled stopped state process
for the profile `P`, confined to the closed working domain `D`
(escape-face accounting, rendered structurally), carrying the ONE
analytic field `dynkin_of_gen_nonpos` in conditional form: whenever the
generator row is certified nonpositive on `D`, the certificate
observable rides the chain as a supermartingale. Deliberately a field,
never a theorem of this module (module docstring); discharged for
martingale-problem presentations by
`QtslAux.SdeMartingaleProblem.MpSolution.toSdeDynkinVille`. The
ℕ-sampled grid is the Ville stock's face; the continuum sup is
constructor-side path regularity. -/
structure SdeDynkinVille (P : SdeProfile n m) (D : Set (State n))
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
  /-- the one analytic field (see the class docstring): certified
  `𝒜V ≤ 0` on `D` ⟹ `V(X_k)` is a supermartingale — the Dynkin formula
  for C² observables up to bounded stopping, plus optional sampling and
  Fatou. -/
  dynkin_of_gen_nonpos :
    (∀ z ∈ D, generator P V gradV hessV z ≤ 0) →
    Supermartingale (fun k ω => V (X k ω)) 𝒢 volume

namespace SdeDynkinVille

variable {P : SdeProfile n m} {D : Set (State n)} {V : State n → ℝ}
  {gradV : State n → State n} {hessV : State n → Fin n → Fin n → ℝ}

/-- **The avoid row** (multiplicative form): the three row families
gen (`𝒜V ≤ 0` on `D`), floor (`V ≥ a` on `Bad`), nonneg (`V ≥ 0` on `D`)
give `a · P(∃k, X_k ∈ Bad) ≤ 𝔼[V(X₀)]`, through
`Qtsl.Ville.reach_avoid`. -/
theorem avoid_row [IsProbabilityMeasure (volume : Measure Ω)]
    (S : SdeDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)} {a : ℝ}
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
    (S : SdeDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)} {a : ℝ}
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
    (S : SdeDynkinVille P D V gradV hessV Ω) {Bad : Set (State n)}
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
    (S : SdeDynkinVille P D V gradV hessV Ω) {Target : Set (State n)}
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

end SdeDynkinVille

end SdeGenerator

end Qtsl
