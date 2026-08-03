import SuFunctor.Decapodes.Schema
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Decapodes, discrete tier: the lowering to drift rows

The upstream compiler applies the method of lines: it topologically
sorts the hypergraph into a straight-line program computing every
non-state variable from the states, and returns the tangent variables
— an ODE right-hand side.  This module certifies that reading.  A
`Schedule` is the *witness* the topological sort produces (not the
algorithm): a polynomial value for every variable in terms of the
flattened state coordinates, such that

* state variables carry the coordinate polynomials,
* **every** row of the Decapode holds as a polynomial identity, and
* every non-state variable is targeted by some row whose inputs all
  have strictly smaller rank (definedness + acyclicity — upstream's
  "all non-state variables must appear alone on the side of at least
  one equation", plus the well-foundedness its sort supplies).

Because the row condition quantifies over all rows, parallel rows
into one target must agree at the polynomial level for a schedule to
exist: genuinely-constraining parallel rows (implicit presentations)
are outside the schedulable fragment, exactly as they are outside the
upstream compiler's — relationally they remain perfectly good
equation systems, and their solution sets remain walls.

The lowering-adequacy theorem (`solSet_eq_range`, `solEquivState`,
`tangent_eq_drift`): the discretized Decapode's solution set *is* the
graph of its drift — solutions project bijectively onto arbitrary
states, and on every solution the tangent variables evaluate the
`driftRows`, which are one polynomial per flattened state coordinate:
verbatim the ⟨variable, polynomial⟩ drift-row premise shape of the
ODE model class.  Soundness (`sat_generatedFrom`) needs no
acyclicity; completeness (`generated_of_sat`) is what the rank
condition pays for.  The schedule is auxiliary: any two schedules
induce the same drift evaluations (`driftRows_eval_unique`), and over
an infinite integral domain the same drift polynomials
(`driftRows_unique`).
-/

namespace SuFunctor
namespace Decapodes

noncomputable section

open MvPolynomial

section Main

variable {S : Signature} {R : Type*} [CommSemiring R]

/-- Evaluation after substitution is evaluation of the composite:
`eval` is `aeval` into the base ring, so this is `aeval_bind₁`. -/
private theorem eval_bind₁ {σ τ : Type*} (x : τ → R)
    (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    MvPolynomial.eval x (bind₁ g φ) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) φ :=
  aeval_bind₁ x g φ

/-- The `Sum.elim` form of `eval_bind₁`, shaped for binary rows. -/
private theorem eval_bind₁_elim {σ₁ σ₂ τ : Type*} (x : τ → R)
    (g₁ : σ₁ → MvPolynomial τ R) (g₂ : σ₂ → MvPolynomial τ R)
    (φ : MvPolynomial (σ₁ ⊕ σ₂) R) :
    MvPolynomial.eval x (bind₁ (Sum.elim g₁ g₂) φ) =
      MvPolynomial.eval
        (Sum.elim (fun i => MvPolynomial.eval x (g₁ i))
                  (fun i => MvPolynomial.eval x (g₂ i))) φ := by
  have h : (Sum.elim (fun i => MvPolynomial.eval x (g₁ i))
      (fun i => MvPolynomial.eval x (g₂ i)))
      = fun i => MvPolynomial.eval x (Sum.elim g₁ g₂ i) := by
    funext k
    cases k <;> rfl
  rw [eval_bind₁, h]

variable (D : Decapode S) (I : Interp S R)

/-- The flattened state index: one coordinate per state variable and
cochain component.  This is the ODE model class's variable set. -/
abbrev StIdx : Type :=
  (s : Fin D.nState) × Fin (vdim D I (D.state s))

/-- A state assignment: a vector in each state variable's cochain
space. -/
def StateVal : Type _ :=
  (s : Fin D.nState) → Fin (vdim D I (D.state s)) → R

/-- Flattening a state assignment over the state index. -/
def flat (x : StateVal D I) : StIdx D I → R := fun k => x k.1 k.2

/-- Polynomials over the flattened state coordinates. -/
abbrev DPoly : Type _ := MvPolynomial (StIdx D I) R

/-- Polynomial-level output of a unary row: the symbol's
interpretation, with the input variable's polynomials substituted. -/
def op1Poly (P : (i : Fin D.nVar) → Fin (vdim D I i) → DPoly D I)
    (e : Fin D.nOp1) : Fin (vdim D I (D.tgt e)) → DPoly D I := fun c =>
  bind₁
    (fun k => P (D.src e) (Fin.cast (congrArg I.dim (D.ty_src e)).symm k))
    (I.op1 (D.op1 e) (Fin.cast (congrArg I.dim (D.ty_tgt e)) c))

/-- Polynomial-level output of a binary row. -/
def op2Poly (P : (i : Fin D.nVar) → Fin (vdim D I i) → DPoly D I)
    (e : Fin D.nOp2) : Fin (vdim D I (D.res e)) → DPoly D I := fun c =>
  bind₁
    (Sum.elim
      (fun k => P (D.proj1 e) (Fin.cast (congrArg I.dim (D.ty_proj1 e)).symm k))
      (fun k => P (D.proj2 e) (Fin.cast (congrArg I.dim (D.ty_proj2 e)).symm k)))
    (I.op2 (D.op2 e) (Fin.cast (congrArg I.dim (D.ty_res e)) c))

/-- Polynomial-level output of a summation row. -/
def sumPoly (P : (i : Fin D.nVar) → Fin (vdim D I i) → DPoly D I)
    (s : Fin D.nSum) : Fin (vdim D I (D.sum s)) → DPoly D I := fun c =>
  ∑ j : Fin D.nSummand,
    if hj : D.summation j = s then
      P (D.summand j)
        (Fin.cast (congrArg I.dim (ty_summand_of_summation D j hj)).symm c)
    else 0

/-- A reference to a row of the Decapode. -/
inductive RowRef (P : Decapode S) where
  | op1 (e : Fin P.nOp1)
  | op2 (e : Fin P.nOp2)
  | sigma (s : Fin P.nSum)

/-- The variable a row targets. -/
def RowRef.rowTgt {P : Decapode S} : RowRef P → Fin P.nVar
  | .op1 e => P.tgt e
  | .op2 e => P.res e
  | .sigma s => P.sum s

/-- The input relation of a row. -/
def RowRef.IsInput {P : Decapode S} : RowRef P → Fin P.nVar → Prop
  | .op1 e, i => P.src e = i
  | .op2 e, i => P.proj1 e = i ∨ P.proj2 e = i
  | .sigma s, i => ∃ j, P.summation j = s ∧ P.summand j = i

/-- Whether a variable is a state variable. -/
def IsState (P : Decapode S) (i : Fin P.nVar) : Prop := ∃ s, P.state s = i

/-- A certified schedule: the witness produced by (any) topological
sort of the hypergraph.  `poly` assigns each variable its value as a
polynomial in the flattened states; the three `row_*` fields say every
row holds as a polynomial identity; `defined` is definedness +
acyclicity for the non-state variables. -/
structure Schedule where
  poly : (i : Fin D.nVar) → Fin (vdim D I i) → DPoly D I
  rank : Fin D.nVar → ℕ
  poly_state : ∀ s c, poly (D.state s) c = X ⟨s, c⟩
  row_op1 : ∀ e, poly (D.tgt e) = op1Poly D I poly e
  row_op2 : ∀ e, poly (D.res e) = op2Poly D I poly e
  row_sum : ∀ s, poly (D.sum s) = sumPoly D I poly s
  defined : ∀ i, ¬IsState D i →
    ∃ r : RowRef D, r.rowTgt = i ∧ ∀ j, r.IsInput j → rank j < rank i

/-- The valuation generated from a state assignment by evaluating the
schedule's polynomials. -/
def generatedFrom (sch : Schedule D I) (x : StateVal D I) :
    Valuation D I := fun i c =>
  MvPolynomial.eval (flat D I x) (sch.poly i c)

/-- The state part of a valuation. -/
def stateOf (v : Valuation D I) : StateVal D I := fun s => v (D.state s)

theorem stateOf_generatedFrom (sch : Schedule D I) (x : StateVal D I) :
    stateOf D I (generatedFrom D I sch x) = x := by
  funext s c
  simp [stateOf, generatedFrom, sch.poly_state, flat]

/-- **Soundness of the lowering**: the valuation generated from any
state assignment satisfies every row.  Acyclicity is not consumed. -/
theorem sat_generatedFrom (sch : Schedule D I) (x : StateVal D I) :
    Sat D I (generatedFrom D I sch x) := by
  refine ⟨fun e => ?_, fun e => ?_, fun s => ?_⟩
  · funext c
    show MvPolynomial.eval (flat D I x) (sch.poly (D.tgt e) c) = _
    rw [sch.row_op1 e]
    simp only [op1Poly, op1Out, eval_bind₁, generatedFrom]
  · funext c
    show MvPolynomial.eval (flat D I x) (sch.poly (D.res e) c) = _
    rw [sch.row_op2 e]
    simp only [op2Poly, op2Out, eval_bind₁_elim, generatedFrom]
  · funext c
    show MvPolynomial.eval (flat D I x) (sch.poly (D.sum s) c) = _
    rw [sch.row_sum s]
    simp only [sumPoly, sumOut, map_sum, generatedFrom]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · simp

/-- **Completeness of the lowering**: every satisfying valuation is
generated from its own state part.  This is the direction the rank
condition pays for: the proof is strong induction on rank, and the
induction step consumes exactly the definedness-with-smaller-inputs
clause. -/
theorem generated_of_sat (sch : Schedule D I) {v : Valuation D I}
    (hv : Sat D I v) :
    v = generatedFrom D I sch (stateOf D I v) := by
  have key : ∀ n (i : Fin D.nVar), sch.rank i < n → ∀ c,
      v i c = MvPolynomial.eval (flat D I (stateOf D I v)) (sch.poly i c) := by
    intro n
    induction n with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
    | succ n IH =>
      intro i hi c
      by_cases hst : IsState D i
      · obtain ⟨s, rfl⟩ := hst
        rw [sch.poly_state s c]
        simp [flat, stateOf]
      · obtain ⟨r, hrt, hrk⟩ := sch.defined i hst
        subst hrt
        cases r with
        | op1 e =>
          simp only [RowRef.rowTgt] at hi hrk ⊢
          have hin : sch.rank (D.src e) < n :=
            lt_of_lt_of_le (hrk (D.src e) rfl) (Nat.lt_succ_iff.mp hi)
          rw [congrFun (hv.op1 e) c, congrFun (sch.row_op1 e) c]
          simp only [op1Out, op1Poly, eval_bind₁]
          have harg :
              (fun k => v (D.src e)
                (Fin.cast (congrArg I.dim (D.ty_src e)).symm k))
              = (fun k => MvPolynomial.eval (flat D I (stateOf D I v))
                  (sch.poly (D.src e)
                    (Fin.cast (congrArg I.dim (D.ty_src e)).symm k))) := by
            funext k
            exact IH (D.src e) hin _
          rw [harg]
        | op2 e =>
          simp only [RowRef.rowTgt] at hi hrk ⊢
          have hin1 : sch.rank (D.proj1 e) < n :=
            lt_of_lt_of_le (hrk (D.proj1 e) (Or.inl rfl)) (Nat.lt_succ_iff.mp hi)
          have hin2 : sch.rank (D.proj2 e) < n :=
            lt_of_lt_of_le (hrk (D.proj2 e) (Or.inr rfl)) (Nat.lt_succ_iff.mp hi)
          rw [congrFun (hv.op2 e) c, congrFun (sch.row_op2 e) c]
          simp only [op2Out, op2Poly, eval_bind₁_elim]
          have harg1 :
              (fun k => v (D.proj1 e)
                (Fin.cast (congrArg I.dim (D.ty_proj1 e)).symm k))
              = (fun k => MvPolynomial.eval (flat D I (stateOf D I v))
                  (sch.poly (D.proj1 e)
                    (Fin.cast (congrArg I.dim (D.ty_proj1 e)).symm k))) := by
            funext k
            exact IH (D.proj1 e) hin1 _
          have harg2 :
              (fun k => v (D.proj2 e)
                (Fin.cast (congrArg I.dim (D.ty_proj2 e)).symm k))
              = (fun k => MvPolynomial.eval (flat D I (stateOf D I v))
                  (sch.poly (D.proj2 e)
                    (Fin.cast (congrArg I.dim (D.ty_proj2 e)).symm k))) := by
            funext k
            exact IH (D.proj2 e) hin2 _
          rw [harg1, harg2]
        | sigma s =>
          simp only [RowRef.rowTgt] at hi hrk ⊢
          rw [congrFun (hv.sum s) c, congrFun (sch.row_sum s) c]
          simp only [sumOut, sumPoly, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · exact IH (D.summand j)
              (lt_of_lt_of_le (hrk (D.summand j) ⟨j, hj, rfl⟩)
                (Nat.lt_succ_iff.mp hi)) _
          · simp
  funext i c
  exact key (sch.rank i + 1) i (Nat.lt_succ_self _) c

/-- **Lowering adequacy, set form**: the solution set of the
discretized Decapode is exactly the range of the generation map —
the graph of the drift over arbitrary states. -/
theorem solSet_eq_range (sch : Schedule D I) :
    {v | Sat D I v} = Set.range (generatedFrom D I sch) := by
  ext v
  constructor
  · intro hv
    exact ⟨stateOf D I v, (generated_of_sat D I sch hv).symm⟩
  · rintro ⟨x, rfl⟩
    exact sat_generatedFrom D I sch x

/-- **Lowering adequacy, bijection form**: solutions correspond
bijectively to arbitrary state assignments — the discretized Decapode
is a *mechanism*, not a constraint, on its states. -/
def solEquivState (sch : Schedule D I) :
    {v : Valuation D I // Sat D I v} ≃ StateVal D I where
  toFun v := stateOf D I v.1
  invFun x := ⟨generatedFrom D I sch x, sat_generatedFrom D I sch x⟩
  left_inv v := Subtype.ext (generated_of_sat D I sch v.2).symm
  right_inv x := stateOf_generatedFrom D I sch x

/-- The drift rows: one polynomial in the flattened state coordinates
per flattened state coordinate — the tangent variables' scheduled
values.  Verbatim the drift-row premise shape of the ODE model
class. -/
def driftRows (sch : Schedule D I) (s : Fin D.nState)
    (c : Fin (vdim D I (D.state s))) : DPoly D I :=
  sch.poly (D.tvar s) (Fin.cast (congrArg I.dim (D.ty_tvar s)).symm c)

/-- On every solution, the tangent variables evaluate the drift rows
at the solution's own state. -/
theorem tangent_eq_drift (sch : Schedule D I) {v : Valuation D I}
    (hv : Sat D I v) (s : Fin D.nState)
    (c : Fin (vdim D I (D.state s))) :
    v (D.tvar s) (Fin.cast (congrArg I.dim (D.ty_tvar s)).symm c) =
      MvPolynomial.eval (flat D I (stateOf D I v)) (driftRows D I sch s c) := by
  conv_lhs => rw [generated_of_sat D I sch hv]
  rfl

/-- The schedule is auxiliary: any two schedules for the same
Decapode and interpretation induce the same drift evaluations. -/
theorem driftRows_eval_unique (sch sch' : Schedule D I)
    (x : StateVal D I) (s : Fin D.nState)
    (c : Fin (vdim D I (D.state s))) :
    MvPolynomial.eval (flat D I x) (driftRows D I sch s c) =
      MvPolynomial.eval (flat D I x) (driftRows D I sch' s c) := by
  have h2 := generated_of_sat D I sch' (sat_generatedFrom D I sch x)
  rw [stateOf_generatedFrom] at h2
  exact congrFun (congrFun h2 (D.tvar s))
    (Fin.cast (congrArg I.dim (D.ty_tvar s)).symm c)

end Main

/-- Over an infinite integral domain, the drift rows themselves are
schedule-independent polynomials: the lowering is canonical, the
schedule a mere witness. -/
theorem driftRows_unique {S : Signature} {R : Type*}
    [CommRing R] [IsDomain R] [Infinite R]
    (D : Decapode S) (I : Interp S R) (sch sch' : Schedule D I)
    (s : Fin D.nState) (c : Fin (vdim D I (D.state s))) :
    driftRows D I sch s c = driftRows D I sch' s c := by
  apply MvPolynomial.funext
  intro x
  have hx : x = flat D I (fun s c => x ⟨s, c⟩) := by
    funext k
    rfl
  rw [hx]
  exact driftRows_eval_unique D I sch sch' _ s c

end

end Decapodes
end SuFunctor
