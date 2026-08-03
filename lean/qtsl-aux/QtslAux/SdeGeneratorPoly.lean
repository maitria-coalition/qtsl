import QtslAux.SdeGenerator
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial presentations of SDE profiles, and the computed generator

The certificate checker works with exact-rational polynomial data. This
module carries the polynomial presentation of an SDE profile — drift,
diffusion columns, killing rate, and finitely many jump legs, each a
rate paired with a finite mixture of polynomial reset maps — the
**computed generator** `genPoly` (killing multiplies, drift pairs the
formal gradient, diffusion traces the formal Hessian against the derived
gram, jumps ride the transfer/pullback action), and **the splice**
(`genPoly_eval_eq_generator`): for a conservative single-Dirac-leg
presentation, evaluating the computed generator over `ℝⁿ` equals the
semantic generator of `QtslAux.SdeGenerator` with the observable and its
derivative data instantiated at the formal derivatives. Every family is
a symbolic-exact operation; the summations are definitional, and only a
checker needs coefficient values.

The transfer action `transferMix` is the Koopman/pullback action of a
finite mixture kernel on an observable: `T_μ V = ∑ᵢ wᵢ · (V ∘ gᵢ)` —
integration against the kernel, performed exactly at the polynomial
stratum. Sub-stochastic weights are admitted (the deficit is killing);
the validity rows (`w ≥ 0`, `∑ w ≤ 1`) are checker-facing instruments,
not carried here.

`continuous_aeval_real` (evaluation of a rational-coefficient
polynomial over `ℝⁿ` is continuous) is the topology-facing static the
martingale-problem module consumes for its C² test class.
-/

open MvPolynomial

namespace Qtsl

namespace SdeGeneratorPoly

open SdeGenerator

variable {n : ℕ}

/-- A finite mixture of polynomial reset maps, as a weighted list
`(wᵢ, gᵢ)`. Sub-stochastic weights are admitted (the deficit is
killing); validity rows (`w ≥ 0`, `∑ w ≤ 1`) are checker-facing
instruments, not carried here. -/
abbrev Mixture (n : ℕ) (R : Type*) [CommSemiring R] :=
  List (R × (Fin n → MvPolynomial (Fin n) R))

section Transfer

variable {R : Type*} [CommSemiring R]

/-- **The transfer (Koopman/pullback) action** of a mixture kernel on an
observable: `T_μ V = ∑ᵢ wᵢ · (V ∘ gᵢ)` — the integral dual at the
mixture stratum, exact by construction. -/
noncomputable def transferMix (μ : Mixture n R) (V : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  (μ.map fun wg => C wg.1 * bind₁ wg.2 V).sum

@[simp] theorem transferMix_nil (V : MvPolynomial (Fin n) R) :
    transferMix ([] : Mixture n R) V = 0 := rfl

@[simp] theorem transferMix_cons (wg : R × (Fin n → MvPolynomial (Fin n) R))
    (μ : Mixture n R) (V : MvPolynomial (Fin n) R) :
    transferMix (wg :: μ) V = C wg.1 * bind₁ wg.2 V + transferMix μ V := by
  simp [transferMix]

/-- The transfer action is additive in the observable (linearity of
integration, at the formal stratum). -/
theorem transferMix_add (μ : Mixture n R) (V W : MvPolynomial (Fin n) R) :
    transferMix μ (V + W) = transferMix μ V + transferMix μ W := by
  induction μ with
  | nil => simp
  | cons wg rest ih => simp [ih, mul_add]; ring

end Transfer

variable {m : ℕ}

/-- **A polynomial presentation of the SDE-profile field families**:
drift `f`, per-driver diffusion columns `σp`, killing rate `kill`
(order-0 family; `0` = conservative dynamics), and finitely many jump
legs, each a rate with a finite reset mixture. The semantic
`SdeProfile` is this presentation's shadow under evaluation
(`toSde`). -/
structure PolyProfile (n m : ℕ) where
  /-- drift field, componentwise -/
  f : Fin n → MvPolynomial (Fin n) ℚ
  /-- diffusion columns, one per independent driver -/
  σp : Fin m → Fin n → MvPolynomial (Fin n) ℚ
  /-- killing rate (order-0 family; `0` = conservative dynamics) -/
  kill : MvPolynomial (Fin n) ℚ
  /-- jump legs: (rate, reset mixture) per leg -/
  legs : List (MvPolynomial (Fin n) ℚ × Mixture n ℚ)

namespace PolyProfile

/-- The derived covariance `a = Σ_k σ^k (σ^k)ᵀ` at the formal stratum —
`SdeProfile.gram`'s twin: derived, never stored. -/
noncomputable def gram (P : PolyProfile n m) (i j : Fin n) :
    MvPolynomial (Fin n) ℚ :=
  ∑ k, P.σp k i * P.σp k j

/-- Formal gram symmetry (the twin of `SdeProfile.gram_symm`). -/
theorem gram_symm (P : PolyProfile n m) (i j : Fin n) :
    P.gram i j = P.gram j i :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

end PolyProfile

/-- **The computed generator**: given the presentation `P` and the
certificate body `V`, the polynomial

`𝒜V = −kill·V + Σᵢ fᵢ·∂ᵢV + ½ Σᵢⱼ aᵢⱼ·∂ᵢ∂ⱼV + Σₗ λₗ·(T_{μₗ}V − V)`,

every family a symbolic-exact operation: killing multiplies, drift
pairs the formal gradient, diffusion traces the formal Hessian against
the derived gram, jumps ride the transfer. -/
noncomputable def genPoly (P : PolyProfile n m) (V : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ :=
  -(P.kill * V)
    + ∑ i, P.f i * pderiv i V
    + C (1/2 : ℚ) * ∑ i, ∑ j, P.gram i j * pderiv i (pderiv j V)
    + (P.legs.map fun lm => lm.1 * (transferMix lm.2 V - V)).sum

/-- Evaluation of a polynomial presentation into the semantic
(real-valued) `SdeProfile`, for a single-Dirac-leg profile: the
splice's target. -/
noncomputable def PolyProfile.toSde (P : PolyProfile n m)
    (lam : MvPolynomial (Fin n) ℚ) (g : Fin n → MvPolynomial (Fin n) ℚ) :
    SdeGenerator.SdeProfile n m where
  f := fun z i => aeval z (P.f i)
  σ := fun k z i => aeval z (P.σp k i)
  lam := fun z => aeval z lam
  g := fun z i => aeval z (g i)

/-- **THE SPLICE**: for a conservative (`kill = 0`), single-Dirac-leg
presentation, evaluating the computed generator equals the semantic
`SdeGenerator.generator` with the certificate observable and its
`gradV`/`hessV` instantiated at the formal derivatives. The
supermartingale-certificate stock (`SdeDynkinVille` and its consumers)
thereby applies to the computed row with zero re-proof; the
formal-vs-analytic derivative identification lives in the
martingale-problem module's statics (`isC2Fn_poly`). -/
theorem genPoly_eval_eq_generator (P : PolyProfile n m)
    (lam : MvPolynomial (Fin n) ℚ) (g : Fin n → MvPolynomial (Fin n) ℚ)
    (V : MvPolynomial (Fin n) ℚ)
    (hkill : P.kill = 0) (hlegs : P.legs = [(lam, [((1 : ℚ), g)])])
    (z : Fin n → ℝ) :
    aeval z (genPoly P V)
      = SdeGenerator.generator (P.toSde lam g)
          (fun w => aeval w V)
          (fun w i => aeval w (pderiv i V))
          (fun w i j => aeval w (pderiv i (pderiv j V))) z := by
  have hhalf : (aeval z) (C (1/2 : ℚ)) = (1/2 : ℝ) := by
    rw [aeval_C]
    norm_num
  simp only [genPoly, hkill, hlegs, SdeGenerator.generator,
    PolyProfile.toSde, SdeGenerator.SdeProfile.gram, PolyProfile.gram,
    transferMix_cons, transferMix_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, map_add, map_mul, map_sub,
    map_sum, map_one, aeval_bind₁, hhalf, one_mul,
    add_zero, zero_mul, neg_zero, zero_add]
  have hdrift : (∑ i, (aeval z) (P.f i) * (aeval z) (pderiv i V))
      = ∑ i, (aeval z) (pderiv i V) * (aeval z) (P.f i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hdrift]

/-- Polynomial evaluation `z ↦ (aeval z p : ℝ)` is continuous — the ℚ→ℝ
face of `MvPolynomial.continuous_eval`. -/
theorem continuous_aeval_real (p : MvPolynomial (Fin n) ℚ) :
    Continuous fun z : State n => (aeval z p : ℝ) := by
  have h : (fun z : State n => (aeval z p : ℝ))
      = fun z : State n => eval z (p.map (algebraMap ℚ ℝ)) := by
    funext z
    rw [aeval_def, eval₂_eq_eval_map]
  rw [h]
  exact MvPolynomial.continuous_eval _

end SdeGeneratorPoly

end Qtsl
