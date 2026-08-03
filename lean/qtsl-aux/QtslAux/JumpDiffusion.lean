import QtslAux.SdeGeneratorPoly

/-! # The multi-leg jump-diffusion generator, and the splice without fences

The certificate compiler (`QtslAux.SdeGeneratorPoly.genPoly`) has
always been total over its presentation: killing, finitely many jump
legs, each a rate with a finite sub-stochastic mixture of polynomial
reset maps. Its landed splice
(`Qtsl.SdeGeneratorPoly.genPoly_eval_eq_generator`) is narrower — one
jump leg, Dirac reset, no killing — because its semantic target
(`Qtsl.SdeGenerator.SdeProfile`) carries exactly one jump pair.

This module supplies the semantic object at the compiler's own
generality and removes the fence:

* `JdProfile` — the multi-leg jump-diffusion profile: drift,
  per-driver diffusion columns, a killing rate, and finitely many jump
  legs, each a rate paired with a finite real mixture of reset maps.
  The covariance is derived by REUSE of the landed `SdeProfile.gram`
  soundness pair (`driftDiff`), never re-proved.
* `generator` — the integro-differential extended generator
  (Ethier–Kurtz, *Markov Processes: Characterization and Convergence*,
  Ch. 4; Davis, *Markov Models and Optimization*, for the
  jump-kernel/killing convention):

    `𝒜V = −kill·V + ∇V·f + ½ Σᵢⱼ aᵢⱼ ∂ᵢⱼV + Σₗ λₗ·(T_{μₗ}V − V)`,

  where `T_μ V = Σᵢ wᵢ·(V ∘ gᵢ)` is the transfer (Koopman/pullback)
  action of the finite mixture kernel. A sub-stochastic mixture is not
  new semantics: `transferSum_sub_self` decomposes a mixture-leg
  increment as Dirac-leg increments minus the deficit spent as killing
  (Davis's convention for kernels of total mass below one).
* **`genPoly_eval_eq_generator`** — the splice with NO hypotheses: for
  every polynomial presentation, evaluating the symbolically computed
  generator equals the semantic generator at the formal-derivative
  data. The presentation-to-profile map `PolyProfile.toJd` takes no
  arguments, unlike the landed `PolyProfile.toSde`, whose extra
  arguments were the fence.
* `generator_one_dirac` / `toJd_generator_one_dirac` — the degeneracy
  ties: one Dirac leg and zero killing collapse the multi-leg
  generator onto the landed `SdeGenerator.generator`, so the landed
  single-leg splice factors as this module's splice followed by the
  tie. `generator_no_legs` is the pure-diffusion face.
* `two_leg_control` — a non-vacuity pin with every field family live
  (drift, diffusion, killing, a Dirac leg, and a genuinely
  sub-stochastic two-map mixture leg), evaluated in closed form. Its
  proof is deliberately direct — independent of the splice — so the
  pin is a second witness rather than a consumer of the theorem it
  guards.

The martingale-problem stock (`QtslAux.SdeMartingaleProblem`) consumes
its generator opaquely — the compensator argument never inspects the
jump structure — so the multi-leg solution concept and its verdict
route are the verbatim transplant of `MpSolution` at this module's
generator, carried out in `QtslAux.JumpDiffusionMartingaleProblem`:
the fenceless headlines hold for every presentation, and the
single-Dirac-leg route factors through them by solution transport.
Per-leg rate validity is the checker-facing row family, leg by leg
(`lam_nonneg_of_rate_rows`), never assumed silently.

No `sorry`; axiom receipts ride the package's `AxiomReceipts` target.
-/

open MvPolynomial

namespace Qtsl

namespace JumpDiffusion

open SdeGenerator (State SdeProfile)
open SdeGeneratorPoly

variable {n m : ℕ}

/-- A finite mixture of reset maps at the semantic (real) stratum, as a
weighted list `(wᵢ, gᵢ)` — the evaluation shadow of
`Qtsl.SdeGeneratorPoly.Mixture`. Sub-stochastic weights are admitted;
the deficit is killing (`transferSum_sub_self`). -/
abbrev MixtureR (n : ℕ) := List (ℝ × (State n → State n))

/-- **The semantic transfer (Koopman/pullback) action** of a finite
mixture kernel on an observable: `T_μ V (z) = Σᵢ wᵢ · V (gᵢ z)` —
integration of the observable against the finite kernel, exact. -/
noncomputable def transferSum (μ : MixtureR n) (V : State n → ℝ)
    (z : State n) : ℝ :=
  (μ.map fun wg => wg.1 * V (wg.2 z)).sum

@[simp] theorem transferSum_nil (V : State n → ℝ) (z : State n) :
    transferSum ([] : MixtureR n) V z = 0 := rfl

@[simp] theorem transferSum_cons (wg : ℝ × (State n → State n))
    (μ : MixtureR n) (V : State n → ℝ) (z : State n) :
    transferSum (wg :: μ) V z = wg.1 * V (wg.2 z) + transferSum μ V z := by
  simp [transferSum]

/-- **A mixture leg is Dirac legs plus killing**: the transfer
increment of a finite mixture decomposes as the weighted sum of
Dirac-jump increments minus the sub-stochastic deficit spent on the
observable — Davis's convention for jump kernels of total mass below
one. This is why the mixture generator below is not new semantics. -/
theorem transferSum_sub_self (μ : MixtureR n) (V : State n → ℝ)
    (z : State n) :
    transferSum μ V z - V z
      = (μ.map fun wg => wg.1 * (V (wg.2 z) - V z)).sum
        - (1 - (μ.map fun wg => wg.1).sum) * V z := by
  induction μ with
  | nil => simp
  | cons wg rest ih =>
      simp only [transferSum_cons, List.map_cons, List.sum_cons]
      rw [show wg.1 * V (wg.2 z) + transferSum rest V z - V z
            = wg.1 * V (wg.2 z) + (transferSum rest V z - V z) from by ring,
        ih]
      ring

/-- **The multi-leg jump-diffusion profile's field families**, as data:
drift `f`, per-driver diffusion columns `σ`, killing rate `kill`
(`0` = conservative dynamics), and finitely many jump legs, each a
rate with a finite reset mixture. One Dirac leg and zero killing is
the landed `SdeProfile` semantics (`generator_one_dirac`); no legs is
the pure-diffusion face (`generator_no_legs`). -/
structure JdProfile (n m : ℕ) where
  /-- drift field -/
  f : State n → State n
  /-- diffusion columns, one per independent Brownian driver -/
  σ : Fin m → State n → State n
  /-- killing rate (`0` = conservative dynamics) -/
  kill : State n → ℝ
  /-- jump legs: (rate, reset mixture) per leg -/
  legs : List ((State n → ℝ) × MixtureR n)

namespace JdProfile

/-- The drift–diffusion part of the profile as a landed `SdeProfile`
(rate 0, identity reset): the vehicle for covariance REUSE. -/
noncomputable def driftDiff (P : JdProfile n m) : SdeProfile n m :=
  ⟨P.f, P.σ, fun _ => 0, id⟩

/-- The derived covariance `a(z) = Σ_k σ^k(z) (σ^k(z))ᵀ` — by reuse of
the landed `SdeProfile.gram`; derived, never stored. -/
noncomputable def gram (P : JdProfile n m) :
    State n → Fin n → Fin n → ℝ :=
  P.driftDiff.gram

/-- The derived covariance is symmetric (inherited). -/
theorem gram_symm (P : JdProfile n m) (z : State n) (i j : Fin n) :
    P.gram z i j = P.gram z j i :=
  P.driftDiff.gram_symm z i j

/-- **The derived covariance is positive semidefinite** (inherited —
the landed sum-of-squares identity, consumed whole). -/
theorem gram_quadForm_nonneg (P : JdProfile n m) (z : State n)
    (v : State n) :
    0 ≤ ∑ i, ∑ j, P.gram z i j * (v i * v j) :=
  P.driftDiff.gram_quadForm_nonneg z v

end JdProfile

/-- **The integro-differential extended generator at the multi-leg
profile**:
`𝒜V(z) = −kill(z)·V(z) + Σᵢ ∂ᵢV·fᵢ + ½ Σᵢⱼ aᵢⱼ(z)·∂ᵢⱼV
+ Σₗ λₗ(z)·(T_{μₗ}V(z) − V(z))`.
`gradV`/`hessV` are derivative *data*, exactly as in the landed
single-leg generator; the identification with genuine Fréchet
derivatives for the polynomial certificate class is
`QtslAux.SdeMartingaleProblem.isC2Fn_poly`, unchanged. -/
noncomputable def generator (P : JdProfile n m) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) : ℝ :=
  -(P.kill z * V z)
    + (∑ i, gradV z i * P.f z i)
    + (1 / 2) * (∑ i, ∑ j, P.gram z i j * hessV z i j)
    + (P.legs.map fun lm => lm.1 z * (transferSum lm.2 V z - V z)).sum

/-- Degeneracy tie: **one Dirac leg, zero killing ⟹ the landed SDE
generator**. The multi-leg profile at this face IS the landed
`SdeProfile` semantics — and through the landed degeneracy trio,
transitively the jump-process and deterministic faces. -/
theorem generator_one_dirac (P : JdProfile n m) (lam : State n → ℝ)
    (g : State n → State n) (hkill : ∀ z, P.kill z = 0)
    (hlegs : P.legs = [(lam, [((1 : ℝ), g)])])
    (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ) (z : State n) :
    generator P V gradV hessV z
      = SdeGenerator.generator ⟨P.f, P.σ, lam, g⟩ V gradV hessV z := by
  simp only [generator, SdeGenerator.generator, hkill, hlegs,
    JdProfile.gram, JdProfile.driftDiff, SdeGenerator.SdeProfile.gram,
    transferSum_cons, transferSum_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_mul, add_zero, zero_mul, neg_zero,
    zero_add]

/-- Degeneracy: **no legs, zero killing ⟹ the pure-diffusion
generator** (the landed `generator_no_jump`'s right-hand side). -/
theorem generator_no_legs (P : JdProfile n m) (hkill : ∀ z, P.kill z = 0)
    (hlegs : P.legs = []) (V : State n → ℝ)
    (gradV : State n → State n) (hessV : State n → Fin n → Fin n → ℝ)
    (z : State n) :
    generator P V gradV hessV z
      = (∑ i, gradV z i * P.f z i)
        + (1 / 2) * (∑ i, ∑ j, P.gram z i j * hessV z i j) := by
  simp [generator, hkill, hlegs]

/-- **The per-leg rate-validity rows' semantic face**: the
checker-facing rate rows `−λₗ(z) ≤ 0` on the working region — one row
per leg — are exactly the model validity `λₗ ≥ 0` that each leg's
Dynkin reading requires; a sign-flipped rate on any leg makes the
generator inequality easier while destroying the model, which is why
each leg carries its own refusal instrument. -/
theorem lam_nonneg_of_rate_rows (P : JdProfile n m) {D : Set (State n)}
    (hrow : ∀ lm ∈ P.legs, ∀ z ∈ D, -(lm.1 z) ≤ 0) :
    ∀ lm ∈ P.legs, ∀ z ∈ D, 0 ≤ lm.1 z :=
  fun lm hlm z hz => neg_nonpos.1 (hrow lm hlm z hz)

/-! ## The compiled face: evaluation and the splice -/

/-- Evaluation of a compiled (exact-rational) mixture into the
semantic mixture. -/
noncomputable def evalMixture (μ : Mixture n ℚ) : MixtureR n :=
  μ.map fun wg => ((wg.1 : ℝ), fun z i => aeval z (wg.2 i))

/-- The transfer actions correspond under evaluation: evaluating the
formal transfer (`bind₁` substitution against the compiled mixture)
is the semantic transfer of the evaluated mixture. -/
theorem aeval_transferMix (μ : Mixture n ℚ) (V : MvPolynomial (Fin n) ℚ)
    (z : State n) :
    (aeval z (transferMix μ V) : ℝ)
      = transferSum (evalMixture μ) (fun w => (aeval w V : ℝ)) z := by
  induction μ with
  | nil => simp [evalMixture]
  | cons wg rest ih =>
      have hC : (aeval z) (C wg.1) = ((wg.1 : ℝ)) := by simp
      simp [evalMixture, transferMix_cons, map_add, map_mul, hC,
        aeval_bind₁, ih]

/-- The leg-list face of the correspondence: evaluating the compiled
jump sum is the semantic jump sum of the evaluated legs. -/
theorem aeval_jump_sum
    (legs : List (MvPolynomial (Fin n) ℚ × Mixture n ℚ))
    (V : MvPolynomial (Fin n) ℚ) (z : State n) :
    (aeval z ((legs.map fun lm => lm.1 * (transferMix lm.2 V - V)).sum) : ℝ)
      = (legs.map fun lm =>
          (aeval z lm.1 : ℝ)
            * (transferSum (evalMixture lm.2) (fun w => (aeval w V : ℝ)) z
              - (aeval z V : ℝ))).sum := by
  induction legs with
  | nil => simp
  | cons lm rest ih =>
      simp [map_add, map_mul, map_sub, aeval_transferMix, ih]

/-- Evaluation of the FULL polynomial presentation into the semantic
multi-leg profile — every field family, no arguments (contrast the
landed `PolyProfile.toSde`, whose extra `lam`/`g` arguments were the
single-leg fence). -/
noncomputable def _root_.Qtsl.SdeGeneratorPoly.PolyProfile.toJd
    (P : PolyProfile n m) : JdProfile n m where
  f z i := aeval z (P.f i)
  σ k z i := aeval z (P.σp k i)
  kill z := aeval z P.kill
  legs := P.legs.map fun lm =>
    ((fun z => (aeval z lm.1 : ℝ)), evalMixture lm.2)

/-- **THE SPLICE, without fences**: for EVERY polynomial presentation —
killing, finitely many jump legs, sub-stochastic mixture resets —
evaluating the computed generator equals the semantic
integro-differential generator with the certificate observable and its
`gradV`/`hessV` instantiated at the formal derivatives. No
conservativity hypothesis, no leg-shape hypothesis: the landed
single-leg splice is this statement composed with
`toJd_generator_one_dirac`. -/
theorem genPoly_eval_eq_generator (P : PolyProfile n m)
    (V : MvPolynomial (Fin n) ℚ) (z : State n) :
    (aeval z (genPoly P V) : ℝ)
      = generator P.toJd
          (fun w => (aeval w V : ℝ))
          (fun w i => (aeval w (pderiv i V) : ℝ))
          (fun w i j => (aeval w (pderiv i (pderiv j V)) : ℝ)) z := by
  have hhalf : (aeval z) (C (1/2 : ℚ)) = (1/2 : ℝ) := by
    rw [aeval_C]
    norm_num
  simp only [genPoly, generator, PolyProfile.toJd, JdProfile.gram,
    JdProfile.driftDiff, SdeGenerator.SdeProfile.gram, PolyProfile.gram,
    map_add, map_mul, map_neg, map_sum, hhalf, List.map_map,
    aeval_jump_sum, Function.comp_def]
  have hdrift : (∑ i, (aeval z) (P.f i) * (aeval z) (pderiv i V))
      = ∑ i, (aeval z) (pderiv i V) * (aeval z) (P.f i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hdrift]

/-- The compiled face of the degeneracy tie: under the landed splice's
own fence (`kill = 0`, one Dirac leg), the evaluated multi-leg profile
generates exactly as the landed single-leg evaluation `toSde` — so the
landed `Qtsl.SdeGeneratorPoly.genPoly_eval_eq_generator` factors as
this module's splice followed by this tie. -/
theorem toJd_generator_one_dirac (P : PolyProfile n m)
    (lam : MvPolynomial (Fin n) ℚ) (g : Fin n → MvPolynomial (Fin n) ℚ)
    (hkill : P.kill = 0) (hlegs : P.legs = [(lam, [((1 : ℚ), g)])])
    (V : State n → ℝ) (gradV : State n → State n)
    (hessV : State n → Fin n → Fin n → ℝ) (z : State n) :
    generator P.toJd V gradV hessV z
      = SdeGenerator.generator (P.toSde lam g) V gradV hessV z := by
  have h := generator_one_dirac (P := P.toJd)
    (lam := fun w => (aeval w lam : ℝ))
    (g := fun w i => (aeval w (g i) : ℝ))
    (hkill := fun w => by simp [PolyProfile.toJd, hkill])
    (hlegs := by simp [PolyProfile.toJd, hlegs, evalMixture])
    V gradV hessV z
  rw [h]
  rfl

/-! ## Positive control: every field family live, in closed form -/

/-- The control presentation: drift `x`, unit diffusion column, unit
killing, and two jump legs — a Dirac contraction at rate `1`, and a
genuinely sub-stochastic two-map mixture (reset-to-origin at weight
`1/2`, identity at weight `1/4`, deficit `1/4`) at rate `x²`. -/
noncomputable def twoLeg : PolyProfile 1 1 where
  f _ := X 0
  σp _ _ := C 1
  kill := C 1
  legs :=
    [(C 1, [((1 : ℚ), fun _ => C (1/2) * X 0)]),
     (X 0 ^ 2, [((1/2 : ℚ), fun _ => 0), ((1/4 : ℚ), fun _ => X 0)])]

/-- **The control pin**, in closed form at the plain test datum
`V = x²`: with every field family live,
`𝒜V(z) = −z² + 2z² + 1 − (3/4)z² − (3/4)z⁴ = 1 + z²/4 − (3/4)z⁴`.
The proof is deliberately direct — independent of the splice — so this
pin witnesses the profile evaluation and the multi-leg generator
separately from the theorem that ties them. -/
theorem two_leg_control (z : State 1) :
    4 * generator twoLeg.toJd (fun w => (w 0) ^ 2)
        (fun w _ => 2 * w 0) (fun _ _ _ => 2) z
      = 4 + (z 0) ^ 2 - 3 * (z 0) ^ 4 := by
  simp [generator, PolyProfile.toJd, twoLeg, evalMixture,
    JdProfile.gram, JdProfile.driftDiff, SdeGenerator.SdeProfile.gram]
  ring
