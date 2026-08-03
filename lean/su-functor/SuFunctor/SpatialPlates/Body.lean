import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots

/-! # Spatial plates: plated bodies and T-POLY

The spatial-plates design's second extent species declares a spatial
variable `ξ : R` and endows exactly one tautological wire — the
coordinate wire `pos_ξ` — while `const` keeps its refusal: a literal
with a `ξ`-axis would be an uncountable table.  This module mechanizes
the theorem that refusal-plus-grant buys (the sibling of the Bag
species' T-NAT):

**T-POLY** (`Body.den_eq_eval`, `Body.poly_totalDegree_le`): in a
well-formed plated body, every wire's dependence on the spatial
variable is *polynomial* in `(pos_ξ, plated inputs)`, with syntactic
degree data — definable dependence for free, which is exactly what
symbolic integration consumes.  The proof is the design's SSA
induction, one clause per box: no constructor creates ξ-structure
except `pos` itself.

The refusal's *necessity* is also a theorem
(`indicator_not_polynomial`): had `const` admitted field literals (a
function of position — the "infinite table" of the design memo), T-POLY
would be refuted; the witness is the indicator of `{0}`.

Bodies here are the disjunction-free (`cell`-free) fragment at one
spatial variable, jet order `k`: the fragment the design's tier-1
contraction stratum consumes (globally polynomial bodies; `cell`
introduces piece structure and nothing else, so the piecewise case is
this theorem applied per piece).
-/

namespace SuFunctor
namespace SpatialPlates

open MvPolynomial

/-- Jet variables at order `k`: `none` is the coordinate wire
`pos_ξ`; `some j` is the jet wire `u⁽ʲ⁾` (`u = u⁽⁰⁾`). -/
abbrev JetVar (k : ℕ) := Option (Fin (k + 1))

/-- A plated body at jet order `k` — the box vocabulary over the
spatial alphabet.  `lit` is `const`: a ℚ-literal ONLY (the refusal is
structural — no constructor admits a function of position); `pos` is
the coordinate wire (the grant); `jet j` are the plated interface
wires. -/
inductive Body (k : ℕ) where
  | lit (q : ℚ)
  | pos
  | jet (j : Fin (k + 1))
  | add (a b : Body k)
  | mul (a b : Body k)

/-- Pointwise denotation: at position `x` with jet values `v`. -/
def Body.den {k : ℕ} : Body k → ℚ → (Fin (k + 1) → ℚ) → ℚ
  | .lit q, _, _ => q
  | .pos, x, _ => x
  | .jet j, _, v => v j
  | .add a b, x, v => a.den x v + b.den x v
  | .mul a b, x, v => a.den x v * b.den x v

/-- The assignment packaging position and jets. -/
def jetAssign {k : ℕ} (x : ℚ) (v : Fin (k + 1) → ℚ) : JetVar k → ℚ
  | none => x
  | some j => v j

/-- The compile: one polynomial per body, by SSA induction (one
clause per box). -/
noncomputable def Body.poly {k : ℕ} : Body k → MvPolynomial (JetVar k) ℚ
  | .lit q => C q
  | .pos => X none
  | .jet j => X (some j)
  | .add a b => a.poly + b.poly
  | .mul a b => a.poly * b.poly

/-- Syntactic degree data, computable from the syntax. -/
def Body.synDeg {k : ℕ} : Body k → ℕ
  | .lit _ => 0
  | .pos => 1
  | .jet _ => 1
  | .add a b => max a.synDeg b.synDeg
  | .mul a b => a.synDeg + b.synDeg

/-- **T-POLY, existence half**: every plated body's dependence on
`(pos_ξ, jets)` is the evaluation of its compiled polynomial.  The
base case is the const-refusal doing its work: no application creates
ξ-structure except from ξ-typed wires. -/
theorem Body.den_eq_eval {k : ℕ} (b : Body k) (x : ℚ)
    (v : Fin (k + 1) → ℚ) :
    b.den x v = eval (jetAssign x v) b.poly := by
  induction b with
  | lit q => simp [Body.den, Body.poly]
  | pos => simp [Body.den, Body.poly, jetAssign]
  | jet j => simp [Body.den, Body.poly, jetAssign]
  | add a b iha ihb => simp [Body.den, Body.poly, iha, ihb]
  | mul a b iha ihb => simp [Body.den, Body.poly, iha, ihb]

/-- **T-POLY, degree half**: the compiled polynomial's total degree
is bounded by the syntactic degree data. -/
theorem Body.poly_totalDegree_le {k : ℕ} (b : Body k) :
    b.poly.totalDegree ≤ b.synDeg := by
  induction b with
  | lit q => simp [Body.poly, Body.synDeg, totalDegree_C]
  | pos => simp [Body.poly, Body.synDeg, totalDegree_X]
  | jet j => simp [Body.poly, Body.synDeg, totalDegree_X]
  | add a b iha ihb =>
    exact le_trans (totalDegree_add a.poly b.poly) (max_le_max iha ihb)
  | mul a b iha ihb =>
    exact le_trans (totalDegree_mul a.poly b.poly) (Nat.add_le_add iha ihb)

section Refusal

/-- The specialization of a `(pos, jets)`-polynomial along the
position line, jets pinned to 0. -/
noncomputable def lineSpec (P : MvPolynomial (JetVar 0) ℚ) : Polynomial ℚ :=
  aeval (fun i : JetVar 0 =>
    match i with
    | none => Polynomial.X
    | some _ => (0 : Polynomial ℚ)) P

theorem lineSpec_eval (P : MvPolynomial (JetVar 0) ℚ) (x : ℚ) :
    (lineSpec P).eval x = eval (jetAssign x fun _ => 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [lineSpec]
  | add p₁ p₂ ih₁ ih₂ => simp [lineSpec, map_add] at ih₁ ih₂ ⊢; simp [ih₁, ih₂]
  | mul_X p i ih =>
    cases i with
    | none =>
      simp only [lineSpec, map_mul, aeval_X, Polynomial.eval_mul,
        Polynomial.eval_X] at ih ⊢
      simp [ih, jetAssign]
    | some j =>
      simp only [lineSpec, map_mul, aeval_X, Polynomial.eval_mul,
        Polynomial.eval_zero, eval_X] at ih ⊢
      simp [jetAssign]

/-- **The refusal's necessity.** Had `const` admitted field literals
(an arbitrary function of position — the "infinite table"), T-POLY
would be false: the indicator of `{0}` is realized by no polynomial in
`(pos_ξ, jets)`.  Proof: specialize along the position line into
`Polynomial ℚ`; a polynomial vanishing on the infinite set `{x ≠ 0}`
is zero, contradicting its value 1 at the origin. -/
theorem indicator_not_polynomial :
    ¬ ∃ P : MvPolynomial (JetVar 0) ℚ,
        ∀ (x : ℚ) (v : Fin 1 → ℚ),
          (if x = 0 then (1 : ℚ) else 0) = eval (jetAssign x v) P := by
  rintro ⟨P, hP⟩
  -- the line specialization vanishes away from 0 …
  have hroot : {x : ℚ | x ≠ 0} ⊆ {x : ℚ | (lineSpec P).IsRoot x} := by
    intro x hx
    have h := hP x fun _ => 0
    simp only [if_neg hx] at h
    simpa [Polynomial.IsRoot, lineSpec_eval P x] using h.symm
  -- … an infinite set, so it is the zero polynomial
  have hinf : ({x : ℚ | x ≠ 0}).Infinite :=
    (Set.finite_singleton (0 : ℚ)).infinite_compl
  have hq0 : lineSpec P = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot (lineSpec P) (hinf.mono hroot)
  -- but its value at 0 is 1
  have h1 := hP 0 fun _ => 0
  rw [← lineSpec_eval P 0, hq0] at h1
  simp at h1

end Refusal

end SpatialPlates
end SuFunctor
