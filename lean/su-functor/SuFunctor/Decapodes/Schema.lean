import Mathlib.Algebra.MvPolynomial.Monad

/-! # Decapodes, discrete tier: the schema as data

A *Decapode* (Morris–Baas–Arias–Gatlin–Patterson–Fairbanks, "Decapodes:
A Diagrammatic Tool for Representing, Composing, and Computing
Spatialized Partial Differential Equations") presents a system of
equations as a typed directed hypergraph over a monoidal signature:
variables are vertices carrying a wire type (in the intended instance,
a differential-form degree together with primality), operator
occurrences are hyperedges labelled in the signature, and two edges
pointing at the same vertex impose an equality between their results.
The artifact is stored as a relational database instance — tables of
variables, unary-operator occurrences, binary-operator occurrences,
and summations, with foreign keys — and this module renders that
database instance as data, together with its relational semantics
under a *discrete interpretation*: each wire type becomes a
finite-dimensional coordinate space (a cochain space, once a mesh is
fixed) and each operator symbol becomes a polynomial map.

Two fidelity notes, both deliberate:

* Upstream stores occurrences of the formal time derivative as
  unary-operator rows with a distinguished label, plus a table `TVar`
  marking its images; the compiler skips those rows and pairs each
  state variable with its tangent variable.  Here that pairing is
  taken in normal form as primitive data (`state`, `tvar`), and the
  formal time derivative imposes no satisfaction constraint — exactly
  as upstream's own gloss has it: the tangent variable is "a purely
  formal symbol" whose meaning is supplied by the drift reading, which
  lives in `SuFunctor.Decapodes.Lowering`.

* The interpretation assigns *polynomial* maps.  This is the fence,
  not an oversight: pointwise operators beyond the polynomial fragment
  are unrepresentable here rather than discouraged, and the drift
  mechanisms this tier lowers to are exactly the
  differential-polynomial ones the ODE model class consumes.

The `Name` attribute of the upstream schema is presentation data with
no semantic role and is omitted.
-/

namespace SuFunctor
namespace Decapodes

noncomputable section

open MvPolynomial

/-- A monoidal signature for diagrammatic equations: wire types and
typed unary/binary operator symbols.  (Summation needs no symbol: it
is interpreted uniformly as addition, which is why the upstream schema
gives it a table of its own rather than rows in the binary table.) -/
structure Signature where
  /-- wire types (in the discrete-exterior-calculus instance: form
  degree × primality) -/
  Ty : Type
  /-- unary operator symbols -/
  Op1 : Type
  dom1 : Op1 → Ty
  cod1 : Op1 → Ty
  /-- binary operator symbols -/
  Op2 : Type
  dom2l : Op2 → Ty
  dom2r : Op2 → Ty
  cod2 : Op2 → Ty

/-- The Decapode schema as data: finite tables with foreign keys.
`Var` is `Fin nVar` with its `ty` attribute; `Op1`/`Op2` rows carry
their label and their source/target (resp. projections/result)
foreign keys; summation rows carry their `sum` output, with a
separate summand table relating summations to their summands; and
the formal-time-derivative pairing appears in normal form as
`state`/`tvar`.  The `ty_*` fields are the well-typedness of every
foreign key. -/
structure Decapode (S : Signature) where
  nVar : ℕ
  nOp1 : ℕ
  nOp2 : ℕ
  nSum : ℕ
  nSummand : ℕ
  nState : ℕ
  ty : Fin nVar → S.Ty
  op1 : Fin nOp1 → S.Op1
  src : Fin nOp1 → Fin nVar
  tgt : Fin nOp1 → Fin nVar
  op2 : Fin nOp2 → S.Op2
  proj1 : Fin nOp2 → Fin nVar
  proj2 : Fin nOp2 → Fin nVar
  res : Fin nOp2 → Fin nVar
  sum : Fin nSum → Fin nVar
  summation : Fin nSummand → Fin nSum
  summand : Fin nSummand → Fin nVar
  state : Fin nState → Fin nVar
  tvar : Fin nState → Fin nVar
  ty_src : ∀ e, ty (src e) = S.dom1 (op1 e)
  ty_tgt : ∀ e, ty (tgt e) = S.cod1 (op1 e)
  ty_proj1 : ∀ e, ty (proj1 e) = S.dom2l (op2 e)
  ty_proj2 : ∀ e, ty (proj2 e) = S.dom2r (op2 e)
  ty_res : ∀ e, ty (res e) = S.cod2 (op2 e)
  ty_summand : ∀ j, ty (summand j) = ty (sum (summation j))
  ty_tvar : ∀ s, ty (tvar s) = ty (state s)

/-- A discrete interpretation of a signature over a commutative
(semi)ring: cochain dimensions per wire type, and per-*symbol*
polynomial maps (occurrences share their symbol's interpretation —
the exterior derivative is interpreted once, as its incidence
matrix, and used at every occurrence). -/
structure Interp (S : Signature) (R : Type*) [CommSemiring R] where
  dim : S.Ty → ℕ
  op1 : (o : S.Op1) →
    Fin (dim (S.cod1 o)) → MvPolynomial (Fin (dim (S.dom1 o))) R
  op2 : (o : S.Op2) →
    Fin (dim (S.cod2 o)) →
      MvPolynomial (Fin (dim (S.dom2l o)) ⊕ Fin (dim (S.dom2r o))) R

variable {S : Signature} {R : Type*} [CommSemiring R]

/-- The coordinate dimension of a variable: its wire type's cochain
dimension. -/
abbrev vdim (D : Decapode S) (I : Interp S R) (i : Fin D.nVar) : ℕ :=
  I.dim (D.ty i)

/-- A valuation assigns to each variable a vector in its cochain
space. -/
def Valuation (D : Decapode S) (I : Interp S R) : Type _ :=
  (i : Fin D.nVar) → Fin (vdim D I i) → R

variable (D : Decapode S) (I : Interp S R)

/-- The interpreted output of a unary row, at a valuation.  Index
casts ride `Fin.cast` along the row's typing facts. -/
def op1Out (v : Valuation D I) (e : Fin D.nOp1) :
    Fin (vdim D I (D.tgt e)) → R := fun c =>
  MvPolynomial.eval
    (fun k => v (D.src e) (Fin.cast (congrArg I.dim (D.ty_src e)).symm k))
    (I.op1 (D.op1 e) (Fin.cast (congrArg I.dim (D.ty_tgt e)) c))

/-- The interpreted output of a binary row, at a valuation. -/
def op2Out (v : Valuation D I) (e : Fin D.nOp2) :
    Fin (vdim D I (D.res e)) → R := fun c =>
  MvPolynomial.eval
    (Sum.elim
      (fun k => v (D.proj1 e) (Fin.cast (congrArg I.dim (D.ty_proj1 e)).symm k))
      (fun k => v (D.proj2 e) (Fin.cast (congrArg I.dim (D.ty_proj2 e)).symm k)))
    (I.op2 (D.op2 e) (Fin.cast (congrArg I.dim (D.ty_res e)) c))

/-- The typing fact carried by a summand row whose summation is `s`. -/
theorem ty_summand_of_summation (j : Fin D.nSummand) {s : Fin D.nSum}
    (hj : D.summation j = s) : D.ty (D.summand j) = D.ty (D.sum s) :=
  (D.ty_summand j).trans (congrArg (fun t => D.ty (D.sum t)) hj)

/-- The interpreted output of a summation row, at a valuation:
the sum of its summands (summation is interpreted uniformly as
coordinatewise addition; it consumes no signature symbol). -/
def sumOut (v : Valuation D I) (s : Fin D.nSum) :
    Fin (vdim D I (D.sum s)) → R := fun c =>
  ∑ j : Fin D.nSummand,
    if hj : D.summation j = s then
      v (D.summand j)
        (Fin.cast (congrArg I.dim (ty_summand_of_summation D j hj)).symm c)
    else 0

/-- Satisfaction: every row's output variable carries its interpreted
output.  Two rows targeting one variable thereby impose an equality
between their results — the diagrammatic-equation reading.  The
formal time derivative imposes nothing here; the `state`/`tvar`
pairing enters only the drift reading (`Lowering`). -/
structure Sat (v : Valuation D I) : Prop where
  op1 : ∀ e, v (D.tgt e) = op1Out D I v e
  op2 : ∀ e, v (D.res e) = op2Out D I v e
  sum : ∀ s, v (D.sum s) = sumOut D I v s

end

end Decapodes
end SuFunctor
