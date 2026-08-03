import SuFunctor.SpatialPlates.StokesRows
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Spatial plates: the wave-equation fixture — stationary action at the field stratum

The stationary-action design memo's field-theoretic acid test
(§1.2 there): for the Lagrangian density
`𝓛 = ½·uₜ² − ½·c²·uₓ²`, the Euler–Lagrange emission *is* the wave
equation, and energy conservation is the time-translation Noether row
— one polynomial identity plus one wrap-wall integral, both discharged
by machinery this directory already carries.

* **The 1+1-D jet alphabet** (`FieldJet`): one scalar field, temporal
  and spatial jets to order 2, **no position wires** — so every
  Lagrangian over this alphabet is autonomous and homogeneous
  *syntactically*, and the two canonical conservation laws (energy,
  momentum) have their symmetry rows discharged by structural absence,
  exactly as the plated `Body`'s `const`-refusal pattern prescribes.
* **The two truncated total derivatives** (`totalDerivT`,
  `totalDerivX`): the temporal and spatial twins of `totalDeriv`,
  written as explicit three-term operators; exact on first-order-jet
  content, truncated above (the same truncation the jet edition of S2
  performs).
* **EL emission = the wave equation** (`wave_euler_lagrange`):
  `EL(𝓛) = c²·uₓₓ − uₜₜ`, computed from the presentation by formal
  differentiation alone.
* **The generic Noether identity for time translation**
  (`noether_time_translation`): for *every* polynomial Lagrangian
  over this alphabet, with no hypothesis,
  `Dₜ(uₜ·∂_{uₜ}L − L) + Dₓ(uₜ·∂_{uₓ}L) = −uₜ·EL(L)` — the
  divergence of the canonical energy–momentum current is the EL row
  paired with `uₜ`; a checked symmetry row buys a conservation row by
  recomputation. The wave instance (`wave_energy_flux_row`)
  specializes it to `Dₜe − Dₓ(c²·uₜ·uₓ) = −uₜ·EL(𝓛)` with
  `e = ½uₜ² + ½c²uₓ²` (`energy_density_as_charge`) — on shell,
  `∂ₜe = Dₓ(c²·uₜ·uₓ)`.
* **The torus power balance** (`wave_power_balance_torus`): the
  semantic leg, riding `s2_wrap_sound` — at any fixed time, for a
  spatially periodic solution of `uₜₜ = c²·uₓₓ`, the pointwise time
  derivative of the energy density integrates to zero over the
  period: the flux `uₜ·uₓ` is the S2 witness, its jet wall is
  discharged by the product rule at the record stratum, and the wrap
  wall kills the boundary term. The checker never integrates — it
  differentiates the flux witness.
* **The wall's teeth** (`torus_wall_load_bearing`): on a non-periodic
  instance satisfying every other hypothesis, the same integral is
  `1 ≠ 0` — computed through `s1_sound`, so the refutation also rides
  the landed rows.

Deliberately absent (successors, priced in the design memo): the
two-directional semantic soundness of `totalDerivT`/`totalDerivX`
along a spacetime field (the `totalDeriv_sound` sibling with two
independent directions), and a multi-field plated alphabet — the
composite-tower trick in the torus leg is the honest single-field
workaround, and the gap it works around is recorded by it.
-/

namespace SuFunctor
namespace SpatialPlates

open MvPolynomial

noncomputable section

/-! ## The 1+1-D field-jet alphabet -/

/-- Jet variables for one scalar field over one temporal and one
spatial dimension, total jet order ≤ 2: `u`, its first jets `ut`,
`ux`, and its second jets `utt`, `utx`, `uxx`. No position wires —
every body over this alphabet is autonomous and homogeneous
syntactically (the structural-symmetry discipline of the plated
`Body`). -/
inductive FieldJet where
  | u | ut | ux | utt | utx | uxx
deriving DecidableEq

/-- **The truncated total time derivative**:
`Dₜp = uₜ·∂_u p + uₜₜ·∂_{uₜ}p + uₜₓ·∂_{uₓ}p` — exact on
first-order-jet content (third-order jets truncated, as in the S2 jet
edition). -/
def totalDerivT {R : Type*} [CommSemiring R]
    (p : MvPolynomial FieldJet R) : MvPolynomial FieldJet R :=
  X FieldJet.ut * pderiv FieldJet.u p
    + X FieldJet.utt * pderiv FieldJet.ut p
    + X FieldJet.utx * pderiv FieldJet.ux p

/-- **The truncated total space derivative**:
`Dₓp = uₓ·∂_u p + uₜₓ·∂_{uₜ}p + uₓₓ·∂_{uₓ}p`. -/
def totalDerivX {R : Type*} [CommSemiring R]
    (p : MvPolynomial FieldJet R) : MvPolynomial FieldJet R :=
  X FieldJet.ux * pderiv FieldJet.u p
    + X FieldJet.utx * pderiv FieldJet.ut p
    + X FieldJet.uxx * pderiv FieldJet.ux p

section Plumbing

variable {R : Type*} [CommRing R]

theorem totalDerivT_sub (p q : MvPolynomial FieldJet R) :
    totalDerivT (p - q) = totalDerivT p - totalDerivT q := by
  simp only [totalDerivT, map_sub]
  ring

theorem totalDerivX_sub (p q : MvPolynomial FieldJet R) :
    totalDerivX (p - q) = totalDerivX p - totalDerivX q := by
  simp only [totalDerivX, map_sub]
  ring

theorem totalDerivX_neg (p : MvPolynomial FieldJet R) :
    totalDerivX (-p) = -totalDerivX p := by
  simp only [totalDerivX, map_neg]
  ring

/-- Leibniz for the truncated time derivative. -/
theorem totalDerivT_mul (p q : MvPolynomial FieldJet R) :
    totalDerivT (p * q) = totalDerivT p * q + p * totalDerivT q := by
  simp only [totalDerivT, pderiv_mul]
  ring

/-- Leibniz for the truncated space derivative. -/
theorem totalDerivX_mul (p q : MvPolynomial FieldJet R) :
    totalDerivX (p * q) = totalDerivX p * q + p * totalDerivX q := by
  simp only [totalDerivX, pderiv_mul]
  ring

theorem totalDerivT_X_ut :
    totalDerivT (X FieldJet.ut : MvPolynomial FieldJet R)
      = X FieldJet.utt := by
  have hu : pderiv FieldJet.u (X FieldJet.ut : MvPolynomial FieldJet R) = 0 :=
    pderiv_X_of_ne (by simp)
  have hx : pderiv FieldJet.ux (X FieldJet.ut : MvPolynomial FieldJet R) = 0 :=
    pderiv_X_of_ne (by simp)
  simp [totalDerivT, hu, hx, pderiv_X_self]

theorem totalDerivX_X_ut :
    totalDerivX (X FieldJet.ut : MvPolynomial FieldJet R)
      = X FieldJet.utx := by
  have hu : pderiv FieldJet.u (X FieldJet.ut : MvPolynomial FieldJet R) = 0 :=
    pderiv_X_of_ne (by simp)
  have hx : pderiv FieldJet.ux (X FieldJet.ut : MvPolynomial FieldJet R) = 0 :=
    pderiv_X_of_ne (by simp)
  simp [totalDerivX, hu, hx, pderiv_X_self]

end Plumbing

/-! ## The field Euler–Lagrange operator and the Noether identity -/

/-- The Euler–Lagrange operator at one field, 1+1-D:
`EL(L) = ∂_u L − Dₜ(∂_{uₜ}L) − Dₓ(∂_{uₓ}L)` — the spatial by-parts
leg is the term that distinguishes the field case from mechanics. -/
def eulerLagrange {R : Type*} [CommRing R]
    (L : MvPolynomial FieldJet R) : MvPolynomial FieldJet R :=
  pderiv FieldJet.u L - totalDerivT (pderiv FieldJet.ut L)
    - totalDerivX (pderiv FieldJet.ux L)

/-- **The time-translation Noether-current identity**, generic: for
every polynomial Lagrangian `L` over this alphabet, with no hypothesis
whatsoever,
`Dₜ(uₜ·∂_{uₜ}L − L) + Dₓ(uₜ·∂_{uₓ}L) = −uₜ·EL(L)`.
The first argument of `Dₜ` is the canonical energy density
`T^t{}_t`, the argument of `Dₓ` the canonical flux `T^x{}_t`; a
checked symmetry row therefore buys conservation of the current by
pure recomputation. The proof consumes only Leibniz and the
definitional expansion of `Dₜ` — the identity holds for the truncated
operators on the whole ring. -/
theorem noether_time_translation {R : Type*} [CommRing R]
    (L : MvPolynomial FieldJet R) :
    totalDerivT (X FieldJet.ut * pderiv FieldJet.ut L - L)
      + totalDerivX (X FieldJet.ut * pderiv FieldJet.ux L)
      = -(X FieldJet.ut * eulerLagrange L) := by
  rw [totalDerivT_sub, totalDerivT_mul, totalDerivT_X_ut, totalDerivX_mul,
    totalDerivX_X_ut, eulerLagrange]
  rw [show totalDerivT L
      = X FieldJet.ut * pderiv FieldJet.u L
        + X FieldJet.utt * pderiv FieldJet.ut L
        + X FieldJet.utx * pderiv FieldJet.ux L from rfl]
  ring

/-! ## The wave Lagrangian and its rows -/

/-- The wave Lagrangian density `𝓛 = ½·uₜ² − ½·c²·uₓ²` (`csq` is the
squared propagation speed; squares as explicit products, so formal
differentiation computes by `pderiv_mul` alone). -/
def waveLagrangian (csq : ℚ) : MvPolynomial FieldJet ℚ :=
  C (1/2 : ℚ) * (X FieldJet.ut * X FieldJet.ut)
    - C (1/2 : ℚ) * C csq * (X FieldJet.ux * X FieldJet.ux)

/-- The energy density `e = ½·uₜ² + ½·c²·uₓ²`. -/
def energyDensity (csq : ℚ) : MvPolynomial FieldJet ℚ :=
  C (1/2 : ℚ) * (X FieldJet.ut * X FieldJet.ut)
    + C (1/2 : ℚ) * C csq * (X FieldJet.ux * X FieldJet.ux)

/-- The energy flux `c²·uₜ·uₓ`. -/
def fluxDensity (csq : ℚ) : MvPolynomial FieldJet ℚ :=
  C csq * (X FieldJet.ut * X FieldJet.ux)

/-- **EL emission = the wave equation**: `EL(𝓛) = c²·uₓₓ − uₜₜ`,
computed from the presentation. The wave equation is the vanishing of
this row. -/
theorem wave_euler_lagrange (csq : ℚ) :
    eulerLagrange (waveLagrangian csq)
      = C csq * X FieldJet.uxx - X FieldJet.utt := by
  apply MvPolynomial.funext
  intro x
  simp [eulerLagrange, totalDerivT, totalDerivX, waveLagrangian, pderiv_mul,
    pderiv_C_mul, pderiv_C, pderiv_one, pderiv_X_self, pderiv_X_of_ne,
    map_add, map_sub, map_mul, map_neg, map_zero, map_one, eval_C, eval_X,
    eval_mul, eval_add, eval_sub, eval_neg]
  ring

/-- The energy density *is* the time-translation charge's density:
`uₜ·∂_{uₜ}𝓛 − 𝓛 = e` (note the potential term's sign flip between
`𝓛` and `e`). -/
theorem energy_density_as_charge (csq : ℚ) :
    X FieldJet.ut * pderiv FieldJet.ut (waveLagrangian csq)
        - waveLagrangian csq
      = energyDensity csq := by
  apply MvPolynomial.funext
  intro x
  simp [waveLagrangian, energyDensity, pderiv_mul, pderiv_C_mul, pderiv_C,
    pderiv_one, pderiv_X_self, pderiv_X_of_ne, map_add, map_sub, map_mul,
    map_neg, map_zero, map_one, eval_C, eval_X, eval_mul, eval_add, eval_sub,
    eval_neg]
  ring

/-- The canonical flux of time translation is minus the energy flux:
`uₜ·∂_{uₓ}𝓛 = −c²·uₜ·uₓ`. -/
theorem flux_as_current (csq : ℚ) :
    X FieldJet.ut * pderiv FieldJet.ux (waveLagrangian csq)
      = -fluxDensity csq := by
  apply MvPolynomial.funext
  intro x
  simp [waveLagrangian, fluxDensity, pderiv_mul, pderiv_C_mul, pderiv_C,
    pderiv_one, pderiv_X_self, pderiv_X_of_ne, map_add, map_sub, map_mul,
    map_neg, map_zero, map_one, eval_C, eval_X, eval_mul, eval_add, eval_sub,
    eval_neg]
  ring

/-- **The wave energy–flux row** (the instance of the Noether
identity): `Dₜe − Dₓ(c²·uₜ·uₓ) = −uₜ·EL(𝓛)` — on the EL locus,
`∂ₜe = Dₓ(c²·uₜ·uₓ)`: energy conservation with the flux exhibited. -/
theorem wave_energy_flux_row (csq : ℚ) :
    totalDerivT (energyDensity csq) - totalDerivX (fluxDensity csq)
      = -(X FieldJet.ut * eulerLagrange (waveLagrangian csq)) := by
  have h := noether_time_translation (waveLagrangian csq)
  rw [energy_density_as_charge, flux_as_current, totalDerivX_neg] at h
  linear_combination h

/-! ## The torus power balance: the semantic leg, on the landed S2 rows -/

/-- **Instantaneous power balance on the torus.** Fix a time; let
`f 0, f 1` be the field's time-derivative slice `uₜ(t,·)` and its
spatial derivative `uₜₓ(t,·)`; let `g 0, g 1, g 2` be the field
slice's spatial jets `u(t,·), uₓ(t,·), uₓₓ(t,·)`; let `w` be the
second time derivative's slice `uₜₜ(t,·)`. If the wave equation holds
at this time (`w = c²·g 2`) and the slices are `L`-periodic, then the
pointwise time derivative of the energy density —
`uₜ·uₜₜ + c²·uₓ·uₜₓ` — integrates to zero over the period.

Rides `s2_wrap_sound`: the S2 witness is the flux `uₜ·uₓ` (the
composite tower `h 0 = f 0 · g 1`, `h 1 = (f 0 · g 1)′`), its jet
wall is discharged by the product rule at the record stratum, and
periodicity is the wrap wall. -/
theorem wave_power_balance_torus (csq L : ℝ) (f g : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (hf : ∀ y, HasDerivAt (f 0) (f 1 y) y)
    (hg0 : ∀ y, HasDerivAt (g 0) (g 1 y) y)
    (hg1 : ∀ y, HasDerivAt (g 1) (g 2 y) y)
    (hcf1 : Continuous (f 1)) (hcg2 : Continuous (g 2))
    (hwave : ∀ x, w x = csq * g 2 x)
    (hperf : f 0 L = f 0 0) (hperg : g 1 L = g 1 0) :
    ∫ x in (0:ℝ)..L, (f 0 x * w x + csq * (g 1 x * f 1 x)) = 0 := by
  classical
  -- the composite tower: the flux witness and its spatial derivative
  set T : ℕ → ℝ → ℝ := fun j =>
    if j = 0 then fun x => f 0 x * g 1 x
    else if j = 1 then fun x => f 1 x * g 1 x + f 0 x * g 2 x
    else fun _ => 0 with hT
  have hT0 : T 0 = fun x => f 0 x * g 1 x := by simp [hT]
  have hT1 : T 1 = fun x => f 1 x * g 1 x + f 0 x * g 2 x := by simp [hT]
  have hu : ∀ j : Fin 1, ∀ y, HasDerivAt (T j) (T (j + 1) y) y := by
    intro j y
    fin_cases j
    show HasDerivAt (T 0) (T 1 y) y
    rw [hT0, hT1]
    exact (hf y).mul (hg1 y)
  have hcf0 : Continuous (f 0) :=
    continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  have hcg1 : Continuous (g 1) :=
    continuous_iff_continuousAt.mpr fun y => (hg1 y).continuousAt
  have hck : Continuous (T 1) := by
    rw [hT1]
    exact ((hcf1.mul hcg1).add (hcf0.mul hcg2))
  have hwall :
      evalJet T L (X (some 0) : MvPolynomial (JetVar 0) ℝ)
        = evalJet T 0 (X (some 0) : MvPolynomial (JetVar 0) ℝ) := by
    show eval (jetAssignR T L) (X (some 0))
      = eval (jetAssignR T 0) (X (some 0))
    simp only [eval_X, jetAssignR, Fin.val_zero, hT0]
    rw [hperf, hperg]
  have hzero := s2_wrap_sound T L hu hck
    (X (some 0) : MvPolynomial (JetVar 0) ℝ) hwall
  rw [totalDeriv_X_some] at hzero
  have hev : ∀ x : ℝ,
      evalJet T x (X (some ((0 : Fin 1).succ)) : MvPolynomial (JetVar 1) ℝ)
        = f 1 x * g 1 x + f 0 x * g 2 x := by
    intro x
    show eval (jetAssignR T x) (X (some (0 : Fin 1).succ))
      = f 1 x * g 1 x + f 0 x * g 2 x
    have hsucc : ((0 : Fin 1).succ : Fin 2) = 1 := by decide
    simp only [eval_X, hsucc, jetAssignR, Fin.val_one, hT1]
  simp only [hev] at hzero
  have hint : ∀ x : ℝ,
      f 0 x * w x + csq * (g 1 x * f 1 x)
        = csq * (f 1 x * g 1 x + f 0 x * g 2 x) := by
    intro x
    rw [hwave x]
    ring
  calc ∫ x in (0:ℝ)..L, (f 0 x * w x + csq * (g 1 x * f 1 x))
      = ∫ x in (0:ℝ)..L, csq * (f 1 x * g 1 x + f 0 x * g 2 x) :=
        intervalIntegral.integral_congr fun x _ => hint x
    _ = csq * ∫ x in (0:ℝ)..L, (f 1 x * g 1 x + f 0 x * g 2 x) :=
        intervalIntegral.integral_const_mul csq _
    _ = 0 := by rw [hzero, mul_zero]

/-- **The wrap wall has teeth**: at `csq = 1`, `L = 1`, the
non-periodic instance `f 0 = id`, `f 1 = 1`, `g 0 = x²/2`, `g 1 = id`,
`g 2 = 1`, `w = 1` satisfies every hypothesis of the power balance
*except* the two wrap walls (`f 0 1 = 1 ≠ 0 = f 0 0`, likewise
`g 1`), and the same integral is `1`, not `0`. Computed through
`s1_sound` with witness `Q = X²`, so the refutation also rides the
landed rows. -/
theorem torus_wall_load_bearing :
    ∫ x in (0:ℝ)..1, (x * 1 + 1 * (x * 1)) = 1 := by
  have h := s1_sound (Polynomial.X ^ 2 : Polynomial ℚ) 0 1
  have heq : ∀ x : ℝ,
      (((Polynomial.X ^ 2 : Polynomial ℚ).derivative.map
          (algebraMap ℚ ℝ)).eval x)
        = x * 1 + 1 * (x * 1) := by
    intro x
    simp [Polynomial.derivative_X_pow]
    ring
  rw [intervalIntegral.integral_congr (g := fun x =>
      (((Polynomial.X ^ 2 : Polynomial ℚ).derivative.map
        (algebraMap ℚ ℝ)).eval x)) fun x _ => (heq x).symm]
  rw [h]
  simp

end

end SpatialPlates
end SuFunctor
