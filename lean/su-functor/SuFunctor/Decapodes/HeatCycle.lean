import SuFunctor.Decapodes.Lowering
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Worked receipt: heat on the torus, through the lowering

The heat equation on the circle `𝕋¹ = ℝ/L`, presented as a Decapode
over the discrete-exterior-calculus signature and discretized on the
uniform cyclic mesh with `n` vertices and spacing `h`: cochain spaces
are `ℚⁿ` (all four wire types — primal/dual, degree 0/1 — have
dimension `n` on the circle), the exterior derivative and its dual
are the cyclic difference matrices (integer incidence), and both
Hodge stars are diagonal with *rational* entries — the
structured-mesh case: no algebraic-number entries enter, and the
whole receipt is exact arithmetic.

The chain presentation is the honest DEC composite for the Laplacian
on 0-cochains, `Δ = ⋆₀⁻¹ ∘ d̃₀ ∘ ⋆₁ ∘ d₀`, followed by a diffusivity
scaling `ν`:

  `C —d₀→ G —⋆₁→ F —d̃₀→ H —⋆₀⁻¹→ L —ν·→ Ċ`,  `∂ₜC = Ċ`.

What is proved:

* `heat_driftRows` — the lowering produces **verbatim** the
  second-difference stencil rows
  `Ċⱼ = ν·h⁻²·(C_{j+1} − 2Cⱼ + C_{j−1})`, cyclically indexed.
* `heat_dissipation` — the exact discrete energy identity along the
  drift: `∑ⱼ 2·uⱼ·u̇ⱼ = −(2νh⁻²)·∑ⱼ (u_{j+1} − uⱼ)²` (summation by
  parts on the cycle, an exact rational identity), with
  `heat_dissipation_nonpos` reading it as dissipation for `0 ≤ ν` —
  the same certificate genre (exact syzygy row + nonnegativity cone
  row) as the mode-truncated dissipation receipts of the PDE model
  class, on the sibling DEC discretization; and the same equation
  whose continuum record-tier adequacy is
  `SuFunctor.Adequacy.HeatTorus` (there the circle is covered by
  three arcs of the spacetime window and glued; here it is
  discretized outright — the two tiers meet at the equation).
* `heat_equilibrium` — constants are equilibria of the drift (the
  discrete face of the continuum module's constants-as-equilibria
  consistency witness).
* `fused_driftRows_eq` — the fused one-operator presentation (a
  single symbol interpreted as the whole stencil) lowers to the same
  drift rows as the five-operator chain: two presentations, one
  mechanism.
-/

namespace SuFunctor
namespace Decapodes

noncomputable section

open MvPolynomial

/-- Wire types on the circle: primal and dual cochains of degree 0
and 1. -/
inductive HeatTy where
  | p0 | p1 | dual0 | dual1
  deriving DecidableEq

/-- Operator symbols of the heat chain: exterior derivative, Hodge
star on primal 1-cochains, dual exterior derivative, inverse Hodge
star into primal 0-cochains, diffusivity scaling. -/
inductive HeatOp1 where
  | exd | hodge1 | dualExd | hodge0inv | nuScale
  deriving DecidableEq

/-- The DEC signature fragment consumed by the heat chain. -/
abbrev heatSig : Signature where
  Ty := HeatTy
  Op1 := HeatOp1
  dom1 o := match o with
    | .exd => .p0
    | .hodge1 => .p1
    | .dualExd => .dual0
    | .hodge0inv => .dual1
    | .nuScale => .p0
  cod1 o := match o with
    | .exd => .p1
    | .hodge1 => .dual0
    | .dualExd => .dual1
    | .hodge0inv => .p0
    | .nuScale => .p0
  Op2 := Empty
  dom2l o := o.elim
  dom2r o := o.elim
  cod2 o := o.elim

/-- The heat Decapode: six variables
(`C, G = d₀C, F = ⋆₁G, H = d̃₀F, L = ⋆₀⁻¹H, Ċ = ν·L`), five unary
rows, one state (`C`) with tangent `Ċ`. -/
abbrev heatPode : Decapode heatSig where
  nVar := 6
  nOp1 := 5
  nOp2 := 0
  nSum := 0
  nSummand := 0
  nState := 1
  ty := ![.p0, .p1, .dual0, .dual1, .p0, .p0]
  op1 := ![.exd, .hodge1, .dualExd, .hodge0inv, .nuScale]
  src := ![0, 1, 2, 3, 4]
  tgt := ![1, 2, 3, 4, 5]
  op2 := Fin.elim0
  proj1 := Fin.elim0
  proj2 := Fin.elim0
  res := Fin.elim0
  sum := Fin.elim0
  summation := Fin.elim0
  summand := Fin.elim0
  state := ![0]
  tvar := ![5]
  ty_src := by decide
  ty_tgt := by decide
  ty_proj1 := fun e => e.elim0
  ty_proj2 := fun e => e.elim0
  ty_res := fun e => e.elim0
  ty_summand := fun j => j.elim0
  ty_tvar := by decide

/-! ### Substitution helpers

The three shapes of polynomial the DEC interpretation uses, pushed
through `bind₁`. -/

private lemma bind₁_X_sub_X {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (a b : σ) :
    bind₁ f (X a - X b) = f a - f b := by
  simp [map_sub, bind₁_X_right]

private lemma bind₁_C_mul_X {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (a : R) (b : σ) :
    bind₁ f (C a * X b) = C a * f b := by
  simp [map_mul, bind₁_X_right]

private lemma bind₁_stencil {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (a : R) (i j k : σ) :
    bind₁ f (C a * (X i - 2 * X j + X k)) =
      C a * (f i - 2 * f j + f k) := by
  simp [map_mul, map_sub, map_add, map_ofNat, bind₁_X_right]

variable (n : ℕ) [NeZero n] (h ν : ℚ)

/-! ### Cyclic index arithmetic -/

private lemma sub_one_add_one (c : Fin n) : c - 1 + 1 = c := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

private lemma add_one_sub_one (c : Fin n) : c + 1 - 1 = c := by
  rw [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]

/-- The uniform-cyclic-mesh interpretation: every cochain space is
`ℚⁿ`; `d₀` and `d̃₀` are the cyclic difference matrices (integer
incidence); both Hodge stars are diagonal with the *rational* entries
of the uniform mesh (`⋆₁ = h⁻¹·id` on primal 1-cochains, and
`⋆₀ = h·id` so `⋆₀⁻¹ = h⁻¹·id`); the scaling is `ν·id`.  Cyclic
indexing is `Fin n` arithmetic. -/
abbrev heatInterp : Interp heatSig ℚ where
  dim _ := n
  op1 o := match o with
    | .exd => fun j => X (j + 1) - X j
    | .hodge1 => fun j => C h⁻¹ * X j
    | .dualExd => fun j => X j - X (j - 1)
    | .hodge0inv => fun j => C h⁻¹ * X j
    | .nuScale => fun j => C ν * X j
  op2 o := o.elim

/-- Scheduled polynomial for `C`: the state coordinates. -/
def pC : Fin n → DPoly heatPode (heatInterp n h ν) := fun c => X ⟨0, c⟩

/-- Scheduled polynomial for `G = d₀C`. -/
def pG : Fin n → DPoly heatPode (heatInterp n h ν) := fun j =>
  pC n h ν (j + 1) - pC n h ν j

/-- Scheduled polynomial for `F = ⋆₁G`. -/
def pF : Fin n → DPoly heatPode (heatInterp n h ν) := fun j =>
  C h⁻¹ * pG n h ν j

/-- Scheduled polynomial for `H = d̃₀F`. -/
def pH : Fin n → DPoly heatPode (heatInterp n h ν) := fun j =>
  pF n h ν j - pF n h ν (j - 1)

/-- Scheduled polynomial for `L = ⋆₀⁻¹H`. -/
def pL : Fin n → DPoly heatPode (heatInterp n h ν) := fun j =>
  C h⁻¹ * pH n h ν j

/-- Scheduled polynomial for `Ċ = ν·L`. -/
def pCdot : Fin n → DPoly heatPode (heatInterp n h ν) := fun j =>
  C ν * pL n h ν j

/-- The certified schedule of the heat chain: the topological sort's
witness, with rank the variable index. -/
def heatSchedule : Schedule heatPode (heatInterp n h ν) where
  poly := ![pC n h ν, pG n h ν, pF n h ν, pH n h ν, pL n h ν, pCdot n h ν]
  rank := Fin.val
  poly_state := by
    intro s c
    fin_cases s
    rfl
  row_op1 := by
    intro e
    fin_cases e
    · funext c
      show pG n h ν c =
        bind₁ (fun k => pC n h ν k) (X (c + 1) - X c)
      rw [bind₁_X_sub_X]
      rfl
    · funext c
      show pF n h ν c =
        bind₁ (fun k => pG n h ν k) (C h⁻¹ * X c)
      rw [bind₁_C_mul_X]
      rfl
    · funext c
      show pH n h ν c =
        bind₁ (fun k => pF n h ν k) (X c - X (c - 1))
      rw [bind₁_X_sub_X]
      rfl
    · funext c
      show pL n h ν c =
        bind₁ (fun k => pH n h ν k) (C h⁻¹ * X c)
      rw [bind₁_C_mul_X]
      rfl
    · funext c
      show pCdot n h ν c =
        bind₁ (fun k => pL n h ν k) (C ν * X c)
      rw [bind₁_C_mul_X]
      rfl
  row_op2 := fun e => e.elim0
  row_sum := fun s => s.elim0
  defined := by
    intro i hi
    fin_cases i
    · exact absurd ⟨0, rfl⟩ hi
    · exact ⟨.op1 0, rfl, fun j hj => by
        have hj' : heatPode.src 0 = j := hj
        subst hj'
        decide⟩
    · exact ⟨.op1 1, rfl, fun j hj => by
        have hj' : heatPode.src 1 = j := hj
        subst hj'
        decide⟩
    · exact ⟨.op1 2, rfl, fun j hj => by
        have hj' : heatPode.src 2 = j := hj
        subst hj'
        decide⟩
    · exact ⟨.op1 3, rfl, fun j hj => by
        have hj' : heatPode.src 3 = j := hj
        subst hj'
        decide⟩
    · exact ⟨.op1 4, rfl, fun j hj => by
        have hj' : heatPode.src 4 = j := hj
        subst hj'
        decide⟩

/-- **Verbatim rows**: the lowering of the DEC heat chain is the
second-difference stencil, cyclically indexed — the drift rows of the
discretized heat equation, exactly. -/
theorem heat_driftRows (s : Fin 1) (c : Fin n) :
    driftRows heatPode (heatInterp n h ν) (heatSchedule n h ν) s c =
      C (ν * h⁻¹ * h⁻¹) *
        (X ⟨0, c + 1⟩ - 2 * X ⟨0, c⟩ + X ⟨0, c - 1⟩) := by
  fin_cases s
  show pCdot n h ν c = _
  simp only [pCdot, pL, pH, pF, pG, pC, C_mul, sub_one_add_one]
  ring

/-- The drift, evaluated: the right-hand side the method of lines
hands to an ODE solver. -/
def heatDrift (u : Fin n → ℚ) (j : Fin n) : ℚ :=
  MvPolynomial.eval
    (flat heatPode (heatInterp n h ν) (fun _ c => u c))
    (driftRows heatPode (heatInterp n h ν) (heatSchedule n h ν) 0 j)

theorem heatDrift_eq (u : Fin n → ℚ) (j : Fin n) :
    heatDrift n h ν u j =
      ν * h⁻¹ * h⁻¹ * (u (j + 1) - 2 * u j + u (j - 1)) := by
  unfold heatDrift
  rw [heat_driftRows]
  simp only [map_mul, map_sub, map_add, map_ofNat, eval_C, eval_X, flat]
  try ring

/-- Cyclic reindexing: summing a function of `j + 1` over the cycle
is summing the function. -/
theorem sum_shift (f : Fin n → ℚ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

/-- **The dissipation syzygy**: along the lowered drift, the discrete
energy `∑ u²` moves at exactly `−(2νh⁻²)·∑ (u_{j+1} − uⱼ)²` —
summation by parts on the cycle, as an exact rational identity.  This
is the syzygy row of the dissipation certificate genre; the cone row
is the corollary below. -/
theorem heat_dissipation (u : Fin n → ℚ) :
    ∑ j, 2 * u j * heatDrift n h ν u j =
      -(2 * ν * h⁻¹ * h⁻¹) * ∑ j, (u (j + 1) - u j) ^ 2 := by
  -- per-term: drift term + dissipation term = a shift-difference
  have expand : ∀ j : Fin n,
      2 * u j * heatDrift n h ν u j +
        2 * ν * h⁻¹ * h⁻¹ * (u (j + 1) - u j) ^ 2 =
      2 * ν * h⁻¹ * h⁻¹ *
        ((u (j + 1) * u (j + 1) - u (j + 1) * u j) -
         (u j * u j - u j * u (j - 1))) := by
    intro j
    rw [heatDrift_eq]
    ring
  -- the shift-differences telescope to zero around the cycle
  have htel := sum_shift n (fun j => u j * u j - u j * u (j - 1))
  simp only [add_one_sub_one] at htel
  have hzero :
      ∑ j, (2 * u j * heatDrift n h ν u j +
        2 * ν * h⁻¹ * h⁻¹ * (u (j + 1) - u j) ^ 2) = 0 := by
    simp only [expand]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, htel, sub_self, mul_zero]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hzero
  linarith

/-- The cone row: for nonnegative diffusivity the energy is
nonincreasing along the drift (the shift-difference sum of squares is
nonnegative). -/
theorem heat_dissipation_nonpos (hν : 0 ≤ ν) (u : Fin n → ℚ) :
    ∑ j, 2 * u j * heatDrift n h ν u j ≤ 0 := by
  rw [heat_dissipation]
  have h1 : 0 ≤ ∑ j, (u (j + 1) - u j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ h⁻¹ * h⁻¹ := mul_self_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hν h2) h1]

/-- Constants are equilibria of the lowered drift — the discrete face
of the continuum adequacy suite's constants-as-equilibria witness. -/
theorem heat_equilibrium (a : ℚ) (j : Fin n) :
    heatDrift n h ν (fun _ => a) j = 0 := by
  rw [heatDrift_eq]
  ring

/-! ## The fused presentation

The same mechanism presented with a single operator symbol whose
interpretation is the whole ν-scaled stencil.  Its lowering agrees
with the chain's on the nose: presentation-equivalence at the
polynomial level. -/

/-- One symbol: the ν-scaled discrete Laplacian, fused. -/
inductive FusedOp1 where
  | nuLap
  deriving DecidableEq

/-- The fused signature: primal 0-cochains and one symbol. -/
abbrev fusedSig : Signature where
  Ty := HeatTy
  Op1 := FusedOp1
  dom1 _ := .p0
  cod1 _ := .p0
  Op2 := Empty
  dom2l o := o.elim
  dom2r o := o.elim
  cod2 o := o.elim

/-- The fused heat Decapode: two variables, one row. -/
abbrev fusedPode : Decapode fusedSig where
  nVar := 2
  nOp1 := 1
  nOp2 := 0
  nSum := 0
  nSummand := 0
  nState := 1
  ty := ![.p0, .p0]
  op1 := ![.nuLap]
  src := ![0]
  tgt := ![1]
  op2 := Fin.elim0
  proj1 := Fin.elim0
  proj2 := Fin.elim0
  res := Fin.elim0
  sum := Fin.elim0
  summation := Fin.elim0
  summand := Fin.elim0
  state := ![0]
  tvar := ![1]
  ty_src := by decide
  ty_tgt := by decide
  ty_proj1 := fun e => e.elim0
  ty_proj2 := fun e => e.elim0
  ty_res := fun e => e.elim0
  ty_summand := fun j => j.elim0
  ty_tvar := by decide

/-- The fused interpretation: the stencil, whole. -/
abbrev fusedInterp : Interp fusedSig ℚ where
  dim _ := n
  op1 _ := fun j =>
    C (ν * h⁻¹ * h⁻¹) * (X (j + 1) - 2 * X j + X (j - 1))
  op2 o := o.elim

/-- Scheduled state polynomial of the fused presentation. -/
def qC : Fin n → DPoly fusedPode (fusedInterp n h ν) := fun c => X ⟨0, c⟩

/-- Scheduled tangent polynomial of the fused presentation. -/
def qCdot : Fin n → DPoly fusedPode (fusedInterp n h ν) := fun j =>
  C (ν * h⁻¹ * h⁻¹) *
    (qC n h ν (j + 1) - 2 * qC n h ν j + qC n h ν (j - 1))

/-- The fused schedule. -/
def fusedSchedule : Schedule fusedPode (fusedInterp n h ν) where
  poly := ![qC n h ν, qCdot n h ν]
  rank := Fin.val
  poly_state := by
    intro s c
    fin_cases s
    rfl
  row_op1 := by
    intro e
    fin_cases e
    funext c
    show qCdot n h ν c =
      bind₁ (fun k => qC n h ν k)
        (C (ν * h⁻¹ * h⁻¹) * (X (c + 1) - 2 * X c + X (c - 1)))
    rw [bind₁_stencil]
    rfl
  row_op2 := fun e => e.elim0
  row_sum := fun s => s.elim0
  defined := by
    intro i hi
    fin_cases i
    · exact absurd ⟨0, rfl⟩ hi
    · exact ⟨.op1 0, rfl, fun j hj => by
        have hj' : fusedPode.src 0 = j := hj
        subst hj'
        decide⟩

/-- **Presentation invariance**: the fused presentation and the
five-operator DEC chain lower to the same drift rows — two
presentations, one mechanism. -/
theorem fused_driftRows_eq (s : Fin 1) (c : Fin n) :
    driftRows fusedPode (fusedInterp n h ν) (fusedSchedule n h ν) s c =
      driftRows heatPode (heatInterp n h ν) (heatSchedule n h ν) s c := by
  rw [heat_driftRows]
  fin_cases s
  show qCdot n h ν c = _
  simp only [qCdot, qC, C_mul]

end

end Decapodes
end SuFunctor
