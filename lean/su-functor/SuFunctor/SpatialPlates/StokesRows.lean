import SuFunctor.SpatialPlates.Body
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Spatial plates: the Stokes row species (S1–S2), ℚ-pinned, with semantic soundness

The design's checker slogan: **the checker never integrates — it
differentiates witnesses.**  The ℤ probe (`spatial-plate-probe/`)
mechanized the division-free checker core; this module generalizes it
to the ℚ-pinned piecewise-polynomial fragment and adds the stratum the
probe deliberately did not touch: soundness of the rows against
mathlib's interval integral.

* **S1** (`s1Value`, `s1_welldef`, `s1_chain`, `s1_sound`): the
  antiderivative row over `Polynomial ℚ`, with FTC-2 soundness.
* **The Jacobian block** (`s1_cov_gate`, `s1_cov_value`,
  `s1_dilation_refused`): naturality-on-densities at the checker face —
  a transported witness passes the gate only against the integrand
  carrying the Jacobian factor `φ.derivative`; the twist is forced by
  the chain rule, and the sans-Jacobian gate is *refuted* at the
  probe's own dilation instance.  (The graded-equivariance tower's
  bottom floor, §4.2.1 of the design memo, at arbitrary polynomial
  reparametrization.)
* **S2, jet edition** (`totalDeriv`, `totalDeriv_sound`,
  `s2_stokes_sound`, `s2_wrap_sound`, `xfree_wrap`): the formal total
  derivative through declared jets — the checker's gate is a
  polynomial identity; its soundness is the chain rule along a jet
  curve, with the **jet wall as hypothesis** (`u⁽ʲ⁾′ = u⁽ʲ⁺¹⁾`,
  record-side, exactly as the design places it).  Boundary terms are
  dimension-0 evaluations; on a wrap wall they cancel.
* **The acid test, symbolic stratum** (`heat_witness_identity`,
  `heat_by_parts_sound`, `heat_dissipation_symbolic`): the design
  memo §6.3's rows for the heat-torus energy certificate —
  `D_ξ(u·u′) = (u′)² + u·u″` as a checked polynomial identity, the
  by-parts conclusion `∫ u·u″ = −∫ (u′)²` under the wrap wall, and the
  dissipation sign, proved once, symbolically, for every region length
  and every field at once: no mesh anywhere in the statements.
-/

namespace SuFunctor
namespace SpatialPlates

open MvPolynomial

noncomputable section

/-! ## S1: the antiderivative row over ℚ -/

/-- The S1 row's value, read off a witness `Q`: the endpoint
difference.  The row is `(q, Q, a, b)` with gate `Q.derivative = q`;
the checker never integrates. -/
def s1Value (Q : Polynomial ℚ) (a b : ℚ) : ℚ := Q.eval b - Q.eval a

/-- Witness irrelevance: any witness passing the gate yields the same
row value (two antiderivatives differ by a constant; the endpoint
difference kills it). -/
theorem s1_welldef {Q Q' : Polynomial ℚ}
    (h : Q.derivative = Q'.derivative) (a b : ℚ) :
    s1Value Q a b = s1Value Q' a b := by
  have hsub : (Q - Q').derivative = 0 := by
    rw [Polynomial.derivative_sub, h, sub_self]
  have hC := Polynomial.eq_C_of_derivative_eq_zero hsub
  have hev : ∀ x : ℚ, Q.eval x - Q'.eval x = (Q - Q').coeff 0 := by
    intro x
    have hx := congrArg (Polynomial.eval x) hC
    simpa [Polynomial.eval_sub] using hx
  have hb := hev b
  have ha := hev a
  simp only [s1Value]
  linarith

/-- Subdivision additivity — T-DESC_σ's 1-D face at the ℚ stratum. -/
theorem s1_chain (Q : Polynomial ℚ) (a b c : ℚ) :
    s1Value Q a b + s1Value Q b c = s1Value Q a c := by
  simp only [s1Value]; ring

/-- **S1 soundness**: the row's value *is* the interval integral of
the gate's integrand — the semantic stratum the ℤ probe deliberately
did not touch.  (FTC-2; the ℚ-pinned data enters ℝ along the algebra
map.) -/
theorem s1_sound (Q : Polynomial ℚ) (a b : ℝ) :
    ∫ x in a..b, (Q.derivative.map (algebraMap ℚ ℝ)).eval x
      = (Q.map (algebraMap ℚ ℝ)).eval b - (Q.map (algebraMap ℚ ℝ)).eval a := by
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y => (Q.map (algebraMap ℚ ℝ)).eval y)
        ((Q.derivative.map (algebraMap ℚ ℝ)).eval x) x := by
    intro x _
    have hx := Polynomial.hasDerivAt (Q.map (algebraMap ℚ ℝ)) x
    rwa [Polynomial.derivative_map] at hx
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Polynomial.continuous _).intervalIntegrable a b)

/-! ## The Jacobian block: naturality on densities at the checker face

Transport along a polynomial reparametrization `φ` sends the witness
`Q ↦ Q.comp φ`.  The gate the transported witness passes is against
`φ.derivative * (q.comp φ)` — the integrand **with the Jacobian
factor** — and the row value transports to the reparametrized
endpoints.  Without the factor the gate is refutable, and refuted
below at the probe's own dilation instance. -/

/-- The transported witness's gate carries the Jacobian factor —
structurally forced by the chain rule, not chosen. -/
theorem s1_cov_gate (Q φ : Polynomial ℚ) :
    (Q.comp φ).derivative = φ.derivative * Q.derivative.comp φ :=
  Polynomial.derivative_comp Q φ

/-- Change of variables at the value level: the transported row reads
the original row at the transported endpoints. -/
theorem s1_cov_value (Q φ : Polynomial ℚ) (a b : ℚ) :
    s1Value (Q.comp φ) a b = s1Value Q (φ.eval a) (φ.eval b) := by
  simp [s1Value, Polynomial.eval_comp]

/-- The sans-Jacobian gate refused: at `Q = X²`, `φ = 2X` (the ℤ
probe's dilation pair, over ℚ), the transported witness does NOT pass
the gate against the merely-precomposed integrand.  Bare bijections of
the index set are not reindexings — the operational content of spatial
non-exchangeability, at the general-witness stratum. -/
theorem s1_dilation_refused :
    ((Polynomial.X ^ 2 : Polynomial ℚ).comp
        (Polynomial.C 2 * Polynomial.X)).derivative
      ≠ ((Polynomial.X ^ 2 : Polynomial ℚ).derivative).comp
          (Polynomial.C 2 * Polynomial.X) := by
  intro h
  rw [Polynomial.derivative_comp] at h
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.derivative_C_mul_X, Polynomial.derivative_X_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow] at h1
  norm_num at h1

/-! ## S2, jet edition: the formal total derivative -/

variable {R : Type*} [CommSemiring R]

/-- The jet-alphabet embedding `JetVar k ↪ JetVar (k+1)`. -/
def liftJet {k : ℕ} : JetVar k → JetVar (k + 1) :=
  Option.map Fin.castSucc

/-- The checker's formal total derivative through declared jets:
`D_ξ W = W_x + Σ_j W_{u⁽ʲ⁾} · u⁽ʲ⁺¹⁾` — a polynomial one jet order up.
Division-free in the design's sense: differentiation, evaluation,
comparison. -/
def totalDeriv {k : ℕ} (W : MvPolynomial (JetVar k) R) :
    MvPolynomial (JetVar (k + 1)) R :=
  rename liftJet (pderiv none W)
    + ∑ j : Fin (k + 1), rename liftJet (pderiv (some j) W) * X (some j.succ)

theorem totalDeriv_C {k : ℕ} (a : R) :
    totalDeriv (C a : MvPolynomial (JetVar k) R) = 0 := by
  simp [totalDeriv]

theorem totalDeriv_add {k : ℕ} (p q : MvPolynomial (JetVar k) R) :
    totalDeriv (p + q) = totalDeriv p + totalDeriv q := by
  unfold totalDeriv
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem totalDeriv_X_none {k : ℕ} :
    totalDeriv (X (none : JetVar k) : MvPolynomial (JetVar k) R) = 1 := by
  unfold totalDeriv
  rw [pderiv_X_self, map_one,
    Finset.sum_eq_zero fun i _ => by
      rw [pderiv_X_of_ne (by simp), map_zero, zero_mul],
    add_zero]

theorem totalDeriv_X_some {k : ℕ} (j : Fin (k + 1)) :
    totalDeriv (X (some j) : MvPolynomial (JetVar k) R) = X (some j.succ) := by
  unfold totalDeriv
  rw [pderiv_X_of_ne (by simp), map_zero, zero_add,
    Finset.sum_eq_single j
      (fun i _ hne => by
        rw [pderiv_X_of_ne (by simpa using Ne.symm hne), map_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h),
    pderiv_X_self, map_one, one_mul]

/-- Leibniz for the total derivative (lifted factors along
`liftJet`). -/
theorem totalDeriv_mul {k : ℕ} (p q : MvPolynomial (JetVar k) R) :
    totalDeriv (p * q)
      = totalDeriv p * rename liftJet q + rename liftJet p * totalDeriv q := by
  have hsplit : ∀ j : Fin (k + 1),
      (rename (liftJet (k := k)) (pderiv (some j) p) * rename liftJet q
        + rename liftJet p * rename liftJet (pderiv (some j) q))
          * X (some j.succ)
      = rename liftJet (pderiv (some j) p) * X (some j.succ)
          * rename liftJet q
        + rename liftJet p
          * (rename liftJet (pderiv (some j) q) * X (some j.succ)) := by
    intro j; ring
  unfold totalDeriv
  simp only [pderiv_mul, map_add, map_mul, hsplit, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ### Semantic soundness along a jet curve -/

/-- The jet-curve assignment: `pos_ξ ↦ x`, `u⁽ʲ⁾ ↦ u j x`. -/
def jetAssignR {k : ℕ} (u : ℕ → ℝ → ℝ) (x : ℝ) : JetVar k → ℝ
  | none => x
  | some j => u j x

/-- Evaluation of a jet polynomial along the jet curve of `u` at
position `x`. -/
abbrev evalJet {k : ℕ} (u : ℕ → ℝ → ℝ) (x : ℝ)
    (W : MvPolynomial (JetVar k) ℝ) : ℝ :=
  eval (jetAssignR u x) W

@[simp] theorem jetAssignR_liftJet {k : ℕ} (u : ℕ → ℝ → ℝ) (x : ℝ)
    (i : JetVar k) :
    jetAssignR (k := k + 1) u x (liftJet i) = jetAssignR (k := k) u x i := by
  cases i with
  | none => rfl
  | some j => simp [jetAssignR, liftJet]

@[simp] theorem evalJet_rename {k : ℕ} (u : ℕ → ℝ → ℝ) (x : ℝ)
    (W : MvPolynomial (JetVar k) ℝ) :
    evalJet u x (rename liftJet W) = evalJet u x W := by
  have hg : jetAssignR (k := k + 1) u x ∘ liftJet = jetAssignR (k := k) u x :=
    funext fun i => jetAssignR_liftJet u x i
  show eval _ (rename _ _) = _
  rw [eval_rename, hg]

/-- **S2 soundness — the chain rule through declared jets.**  With the
jet wall as hypothesis (`u⁽ʲ⁾` has derivative `u⁽ʲ⁺¹⁾`, the wall the
record stratum discharges), the derivative of a jet polynomial's
evaluation along the jet curve is the evaluation of its formal total
derivative: "differentiate the witness" is semantically exact. -/
theorem totalDeriv_sound {k : ℕ} (u : ℕ → ℝ → ℝ)
    (hu : ∀ j : Fin (k + 1), ∀ y, HasDerivAt (u j) (u (j + 1) y) y)
    (W : MvPolynomial (JetVar k) ℝ) (x : ℝ) :
    HasDerivAt (fun y => evalJet u y W) (evalJet u x (totalDeriv W)) x := by
  induction W using MvPolynomial.induction_on with
  | C a =>
    simpa [totalDeriv_C] using hasDerivAt_const x a
  | add p q ihp ihq =>
    simp only [totalDeriv_add, map_add]
    exact ihp.add ihq
  | mul_X p i ihp =>
    have hbase : HasDerivAt (fun y => jetAssignR (k := k) u y i)
        (evalJet u x (totalDeriv (X i))) x := by
      cases i with
      | none =>
        have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
          first
          | exact hasDerivAt_id'
          | exact hasDerivAt_id x
        simpa [jetAssignR, totalDeriv_X_none] using hid
      | some j =>
        simpa [jetAssignR, totalDeriv_X_some, Fin.val_succ] using hu j x
    have hval : evalJet u x (totalDeriv (p * X i))
        = evalJet u x (totalDeriv p) * jetAssignR u x i
          + evalJet u x p * evalJet u x (totalDeriv (X i)) := by
      rw [totalDeriv_mul]
      simp [map_add, map_mul, rename_X]
    have hfun : (fun y => evalJet u y (p * X i))
        = fun y => evalJet u y p * jetAssignR u y i := by
      funext y
      simp [map_mul]
    rw [hfun, hval]
    exact ihp.mul hbase

/-- Continuity of jet evaluation, from continuity of the jets. -/
theorem continuous_evalJet {k : ℕ} (u : ℕ → ℝ → ℝ)
    (hc : ∀ j : Fin (k + 1), Continuous (u j))
    (W : MvPolynomial (JetVar k) ℝ) :
    Continuous fun x => evalJet u x W := by
  induction W using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q ihp ihq =>
    simp only [map_add]
    exact ihp.add ihq
  | mul_X p i ihp =>
    have hbase : Continuous fun x => jetAssignR (k := k) u x i := by
      cases i with
      | none => exact continuous_id
      | some j => exact hc j
    simp only [map_mul, eval_X]
    exact ihp.mul hbase

/-- **S2 with boundary terms** (1-D): the integral of a total
derivative is the endpoint difference of the witness — the boundary
"contraction" grounds at dimension-0 evaluations. -/
theorem s2_stokes_sound {k : ℕ} (u : ℕ → ℝ → ℝ) (L : ℝ)
    (hu : ∀ j : Fin (k + 1), ∀ y, HasDerivAt (u j) (u (j + 1) y) y)
    (hck : Continuous (u (k + 1)))
    (W : MvPolynomial (JetVar k) ℝ) :
    ∫ x in (0:ℝ)..L, evalJet u x (totalDeriv W)
      = evalJet u L W - evalJet u 0 W := by
  have hcont : ∀ j : Fin (k + 2), Continuous (u j) := by
    intro j
    rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hlt | heq
    · exact continuous_iff_continuousAt.mpr
        fun y => (hu ⟨(j : ℕ), hlt⟩ y).continuousAt
    · rw [heq]; exact hck
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => totalDeriv_sound u hu W x)
    ((continuous_evalJet u hcont (totalDeriv W)).intervalIntegrable 0 L)

/-- **S2 on the wrap wall**: `∮ D_ξ W = 0` — the wall as hypothesis,
transposing the probe's `rowValue_wrap` to the semantic stratum. -/
theorem s2_wrap_sound {k : ℕ} (u : ℕ → ℝ → ℝ) (L : ℝ)
    (hu : ∀ j : Fin (k + 1), ∀ y, HasDerivAt (u j) (u (j + 1) y) y)
    (hck : Continuous (u (k + 1)))
    (W : MvPolynomial (JetVar k) ℝ)
    (hW : evalJet u L W = evalJet u 0 W) :
    ∫ x in (0:ℝ)..L, evalJet u x (totalDeriv W) = 0 := by
  rw [s2_stokes_sound u L hu hck W, hW, sub_self]

/-- For x-free witnesses (jet-pure bodies), periodic jets discharge
the wrap-wall hypothesis syntactically. -/
theorem xfree_wrap {k : ℕ} (u : ℕ → ℝ → ℝ) (L : ℝ)
    (hper : ∀ j : Fin (k + 1), u j L = u j 0)
    (W₀ : MvPolynomial (Fin (k + 1)) ℝ) :
    evalJet u L (rename some W₀) = evalJet u 0 (rename some W₀) := by
  have hass : (jetAssignR (k := k) u L ∘ some)
      = (jetAssignR (k := k) u 0 ∘ some) := by
    funext j
    simpa [jetAssignR] using hper j
  show eval _ (rename _ _) = eval _ (rename _ _)
  rw [eval_rename, eval_rename, hass]

/-! ### The acid test, symbolic stratum (design memo §6.3) -/

/-- The heat-torus by-parts witness's gate, discharged as a polynomial
identity: `D_ξ(u·u′) = (u′)² + u·u″`.  Generic in the coefficient
(semi)ring — ℚ gives the checker's exact data, ℝ the soundness
instance. -/
theorem heat_witness_identity (R : Type*) [CommSemiring R] :
    totalDeriv (X (some 0) * X (some 1) : MvPolynomial (JetVar 1) R)
      = X (some 1) * X (some 1) + X (some 0) * X (some 2) := by
  have h1 : (0 : Fin 2).succ = 1 := by decide
  have h2 : (1 : Fin 2).succ = 2 := by decide
  have h3 : Fin.castSucc (0 : Fin 2) = 0 := by decide
  have h4 : Fin.castSucc (1 : Fin 2) = 1 := by decide
  rw [totalDeriv_mul, totalDeriv_X_some, totalDeriv_X_some]
  simp only [liftJet, rename_X, Option.map_some]
  rw [h1, h2, h3, h4]

/-- **The by-parts row, sound**: on the wrap wall,
`∫ u·u″ = −∫ (u′)²` — the §6.3 row-2 conclusion, for every period `L`
and every field at once. -/
theorem heat_by_parts_sound (u : ℕ → ℝ → ℝ) (L : ℝ)
    (hu0 : ∀ y, HasDerivAt (u 0) (u 1 y) y)
    (hu1 : ∀ y, HasDerivAt (u 1) (u 2 y) y)
    (hc2 : Continuous (u 2))
    (hper0 : u 0 L = u 0 0) (hper1 : u 1 L = u 1 0) :
    ∫ x in (0:ℝ)..L, u 0 x * u 2 x
      = -∫ x in (0:ℝ)..L, (u 1 x) ^ 2 := by
  have hu : ∀ j : Fin 2, ∀ y, HasDerivAt (u j) (u (j + 1) y) y := by
    intro j
    fin_cases j
    · simpa using hu0
    · simpa using hu1
  have hwall :
      evalJet u L (X (some 0) * X (some 1) : MvPolynomial (JetVar 1) ℝ)
        = evalJet u 0 (X (some 0) * X (some 1) : MvPolynomial (JetVar 1) ℝ) := by
    simp [map_mul, jetAssignR, hper0, hper1]
  have hzero := s2_wrap_sound u L hu hc2
    (X (some 0) * X (some 1) : MvPolynomial (JetVar 1) ℝ) hwall
  have hint : ∀ x : ℝ,
      evalJet u x
          (totalDeriv (X (some 0) * X (some 1) : MvPolynomial (JetVar 1) ℝ))
        = u 1 x * u 1 x + u 0 x * u 2 x := by
    intro x
    rw [heat_witness_identity]
    simp [map_add, map_mul, jetAssignR]
  simp only [hint] at hzero
  have c0 : Continuous (u 0) :=
    continuous_iff_continuousAt.mpr fun y => (hu0 y).continuousAt
  have c1 : Continuous (u 1) :=
    continuous_iff_continuousAt.mpr fun y => (hu1 y).continuousAt
  have i1 : IntervalIntegrable (fun x => u 1 x * u 1 x)
      MeasureTheory.volume 0 L := (c1.mul c1).intervalIntegrable 0 L
  have i2 : IntervalIntegrable (fun x => u 0 x * u 2 x)
      MeasureTheory.volume 0 L := (c0.mul hc2).intervalIntegrable 0 L
  rw [intervalIntegral.integral_add i1 i2] at hzero
  have hsq : ∫ x in (0:ℝ)..L, (u 1 x) ^ 2
      = ∫ x in (0:ℝ)..L, u 1 x * u 1 x := by
    simp only [pow_two]
  rw [hsq]
  linarith

/-- **The dissipation sign, symbolic stratum** (§6.3 rows 2+3): the
by-parts row plus the S4 sign row (`(u′)² ≥ 0`, `integral_nonneg`)
give `2D·∫ u·u″ ≤ 0` for every diffusivity `D ≥ 0`, every period, and
every field — certified once; no per-point and no per-mesh obligation
anywhere. -/
theorem heat_dissipation_symbolic (u : ℕ → ℝ → ℝ) (L D : ℝ)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hu0 : ∀ y, HasDerivAt (u 0) (u 1 y) y)
    (hu1 : ∀ y, HasDerivAt (u 1) (u 2 y) y)
    (hc2 : Continuous (u 2))
    (hper0 : u 0 L = u 0 0) (hper1 : u 1 L = u 1 0) :
    2 * D * ∫ x in (0:ℝ)..L, u 0 x * u 2 x ≤ 0 := by
  rw [heat_by_parts_sound u L hu0 hu1 hc2 hper0 hper1]
  have hnn : 0 ≤ ∫ x in (0:ℝ)..L, (u 1 x) ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x _ => sq_nonneg _
  nlinarith [mul_nonneg hD hnn]

end

end SpatialPlates
end SuFunctor
