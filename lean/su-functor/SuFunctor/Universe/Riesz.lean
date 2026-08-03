import SuFunctor.Universe.ProbCarrier
import Mathlib.LinearAlgebra.StdBasis

/-! # The Riesz presentation: distributions as expectation functionals

The flat carrier has two canonical presentations, and this module pins
their equivalence — the finite-outcome instance of the
Riesz–Markov–Kakutani representation:

* **mass coordinates** — `ProbState V`, weight functions on outcomes
  (the presentation the exact-rational certificate stratum computes
  with: vertices, boxes, walls);
* **expectation functionals** — positive normalized linear functionals
  on **gambles** `V → ℝ` (the presentation that survives past the
  finite stratum, where states *are* Radon functionals and mass
  coordinates do not exist; also the imprecise-probability
  vocabulary — compare the exact-rational `QtslAux` stock, whose
  `FinPMF.exp` is this pairing's rational shadow).

`rieszEquiv` is the equivalence: `pairing` sends a distribution to its
expectation functional, `ofFunctional` reads coordinates back as the
masses of point gambles, and point masses go to point evaluations
(`pairing_dirac`).  Downstream statements about the flat carrier can
therefore be read in either presentation; the judgment stratum's row
pairings (`affRow`) are the `[0,∞]`-valued face of the same pairing.
-/

namespace SuFunctor.Universe

variable {V : Type*} [Fintype V]

/-- The expectation pairing: a distribution, read as a linear
functional on gambles. -/
noncomputable def pairing (μ : ProbState V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ v, (μ : V → ℝ) v * f v
  map_add' f g := by
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

theorem pairing_apply (μ : ProbState V) (f : V → ℝ) :
    pairing μ f = ∑ v, (μ : V → ℝ) v * f v := rfl

/-- Expectation functionals are positive. -/
theorem pairing_pos (μ : ProbState V) {f : V → ℝ} (hf : 0 ≤ f) :
    0 ≤ pairing μ f :=
  Finset.sum_nonneg fun v _ => mul_nonneg (μ.nonneg v) (hf v)

/-- Expectation functionals are normalized. -/
theorem pairing_one (μ : ProbState V) : pairing μ 1 = 1 := by
  rw [pairing_apply]
  simp only [Pi.one_apply, mul_one]
  exact μ.sum_eq_one

/-- Point masses pair as point evaluations — the Dirac face of the
representation. -/
theorem pairing_dirac [DecidableEq V] (v : V) (f : V → ℝ) :
    pairing (ProbState.dirac v) f = f v := by
  rw [pairing_apply, Finset.sum_eq_single v]
  · rw [ProbState.dirac_apply_same, one_mul]
  · intro w _ hw
    rw [ProbState.dirac_apply_of_ne hw, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- The point gamble at an outcome is a nonnegative gamble. -/
theorem single_one_nonneg [DecidableEq V] (v : V) :
    (0 : V → ℝ) ≤ Pi.single v 1 := by
  intro w
  rcases eq_or_ne w v with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/-- Reading a positive normalized functional back as a distribution:
its coordinates are the masses of the point gambles. -/
noncomputable def ofFunctional [DecidableEq V] (Λ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f : V → ℝ, 0 ≤ f → 0 ≤ Λ f) (hnorm : Λ 1 = 1) :
    ProbState V :=
  ⟨fun v => Λ (Pi.single v 1),
    ⟨fun v => hpos _ (single_one_nonneg v), by
      rw [← map_sum]
      have hsum : (∑ v, Pi.single v (1 : ℝ)) = (1 : V → ℝ) := by
        have h := Finset.univ_sum_single (1 : V → ℝ)
        simpa using h
      rw [hsum, hnorm]⟩⟩

@[simp] theorem ofFunctional_apply [DecidableEq V] (Λ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f : V → ℝ, 0 ≤ f → 0 ≤ Λ f) (hnorm : Λ 1 = 1) (v : V) :
    ((ofFunctional Λ hpos hnorm : ProbState V) : V → ℝ) v
      = Λ (Pi.single v 1) := rfl

/-- The pairing evaluates point gambles to masses. -/
theorem pairing_single [DecidableEq V] (μ : ProbState V) (v : V) :
    pairing μ (Pi.single v 1) = (μ : V → ℝ) v := by
  rw [pairing_apply, Finset.sum_eq_single v]
  · rw [Pi.single_eq_same, mul_one]
  · intro w _ hw
    rw [Pi.single_eq_of_ne hw, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- Every gamble is the mass-weighted sum of point gambles. -/
theorem gamble_eq_sum_single [DecidableEq V] (f : V → ℝ) :
    f = ∑ v, f v • Pi.single v (1 : ℝ) := by
  have hterm : ∀ v ∈ Finset.univ,
      f v • Pi.single v (1 : ℝ) = Pi.single v (f v) := by
    intro v _
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.univ_sum_single]

/-- **The Riesz–Markov–Kakutani equivalence at finite outcomes**:
probability distributions are exactly the positive normalized linear
functionals on gambles. -/
noncomputable def rieszEquiv [DecidableEq V] :
    ProbState V
      ≃ {Λ : (V → ℝ) →ₗ[ℝ] ℝ //
          (∀ f : V → ℝ, 0 ≤ f → 0 ≤ Λ f) ∧ Λ 1 = 1} where
  toFun μ := ⟨pairing μ, fun _ hf => pairing_pos μ hf, pairing_one μ⟩
  invFun Λ := ofFunctional Λ.1 Λ.2.1 Λ.2.2
  left_inv μ := by
    apply Subtype.ext
    funext v
    rw [ofFunctional_apply, pairing_single]
  right_inv Λ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    conv_rhs => rw [gamble_eq_sum_single f]
    rw [map_sum]
    exact Finset.sum_congr rfl fun v _ => by
      rw [map_smul, smul_eq_mul, ofFunctional_apply]
      exact mul_comm _ _

/-- Gambles separate distributions: the pairing is injective. -/
theorem pairing_injective [DecidableEq V] :
    Function.Injective (pairing (V := V)) := by
  intro μ ν h
  exact rieszEquiv.injective (Subtype.ext h)

end SuFunctor.Universe
