import SuFunctor.QtslSem.Decode.Rows
import Qtsl.Catalogue

/-!
# The ground-fragment element decoder (the `qsat_eval` seam)

A satisfaction claim's evaluation leaf is a polynomial-calculus
`Proof` element whose concluded `Judgment` is a sequent of the
certificate calculus — the exact types the wired QtslSem carriers
consume.  This module decodes that seam for the S1 fragment: ground
terms (constants and their ring operations), ground formulas (the
comparison atoms, the connectives, the constants), the judgment's
pre/post pair as a `PPLC.Sequent`, and the leaf's `Proof/concludes`
hop.  Everything outside the ground fragment refuses by name
(`…_outside_s1_fragment`): wires, indexing, regions — the full BL
element decode at baked-closure counters is the S5 seam leg's,
riding `Reflection`'s `RowCtx` machinery once its pins move to the
minted closures.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC PPLC.Geolog

/-- The ground term-constructor roster. -/
def groundTermCtors : List String :=
  ["TConst", "TAdd", "TMul", "TSub", "TNeg", "TVar", "TIdx"]

/-- The ground formula-constructor roster. -/
def groundFormulaCtors : List String :=
  ["FAtomLE", "FAtomLT", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
   "FAnd", "FOr", "FTrue", "FFalse", "FInRegion"]

/-- Two local-element arguments, or refuse. -/
private def twoElems (args : List GValue) (tag : String) (w : Nat) :
    QRes (Nat × Nat) :=
  match args with
  | [a, b] =>
    match elemOfVal a, elemOfVal b with
    | some x, some y => pure (x, y)
    | _, _ => qerr .unreadable tag w
  | _ => qerr .unreadable tag w

/-- Decode a ground term element (fuel-bounded recursion through
constructor rows). -/
def decodeTerm (tb : QRowTbls) : Nat → Nat → QRes Term
  | 0, e => qerr .unreadable "term_fuel" e
  | fuel + 1, e => do
    let _ ← tb.demandSort e "Term" "term_not_term_sorted"
    let (n, args) ← tb.ctor1 groundTermCtors e
      "term_ctor_missing" "term_ctor_ambiguous"
    match n with
    | "TConst" =>
      match args with
      | [v] =>
        match qOfVal v with
        | some q => pure (.const q)
        | none => qerr .unreadable "tconst_not_q" e
      | _ => qerr .unreadable "tconst_arity" e
    | "TAdd" => do
      let (l, r) ← twoElems args "tadd_args" e
      pure (.add (← decodeTerm tb fuel l) (← decodeTerm tb fuel r))
    | "TMul" => do
      let (l, r) ← twoElems args "tmul_args" e
      pure (.mul (← decodeTerm tb fuel l) (← decodeTerm tb fuel r))
    | "TSub" => do
      let (l, r) ← twoElems args "tsub_args" e
      pure (.sub (← decodeTerm tb fuel l) (← decodeTerm tb fuel r))
    | "TNeg" =>
      match args with
      | [v] =>
        match elemOfVal v with
        | some t => do pure (.neg (← decodeTerm tb fuel t))
        | none => qerr .unreadable "tneg_args" e
      | _ => qerr .unreadable "tneg_arity" e
    | other => qerr .unsupported ("term_ctor_outside_s1_fragment:" ++ other) e

/-- The comparison-atom name → `BowTie` reading. -/
def bowtieOfName : String → Option BowTie
  | "FAtomLE" => some .le
  | "FAtomLT" => some .lt
  | "FAtomEQ" => some .eq
  | "FAtomGE" => some .ge
  | "FAtomGT" => some .gt
  | "FAtomNE" => some .ne
  | _ => none

/-- Decode a ground formula element. -/
def decodeFormula (tb : QRowTbls) : Nat → Nat → QRes Formula
  | 0, e => qerr .unreadable "formula_fuel" e
  | fuel + 1, e => do
    let _ ← tb.demandSort e "Formula" "formula_not_formula_sorted"
    let (n, args) ← tb.ctor1 groundFormulaCtors e
      "formula_ctor_missing" "formula_ctor_ambiguous"
    match bowtieOfName n with
    | some b => do
      let (l, r) ← twoElems args "fatom_args" e
      pure (.atom b (← decodeTerm tb fuel l) (← decodeTerm tb fuel r))
    | none =>
      match n with
      | "FTrue" =>
        match args with
        | [] => pure .tt
        | _ => qerr .unreadable "ftrue_arity" e
      | "FFalse" =>
        match args with
        | [] => pure .ff
        | _ => qerr .unreadable "ffalse_arity" e
      | "FAnd" => do
        let (l, r) ← twoElems args "fand_args" e
        pure (.and (← decodeFormula tb fuel l) (← decodeFormula tb fuel r))
      | "FOr" => do
        let (l, r) ← twoElems args "for_args" e
        pure (.or (← decodeFormula tb fuel l) (← decodeFormula tb fuel r))
      | other =>
        qerr .unsupported ("formula_ctor_outside_s1_fragment:" ++ other) e

/-- Decode a certificate-calculus judgment element as a sequent:
exactly one `Judgment/pre` and one `Judgment/post` row, both decoding
in the ground fragment. -/
def decodeSequentOfJudgment (tb : QRowTbls) (e : Nat) : QRes Sequent := do
  let _ ← tb.demandSort e "Judgment" "judgment_not_judgment_sorted"
  let fuel := tb.sorts.length + 1
  let preE ← tb.fld1Elem "Judgment/pre" e
    "judgment_missing_pre" "judgment_dup_pre"
  let postE ← tb.fld1Elem "Judgment/post" e
    "judgment_missing_post" "judgment_dup_post"
  let pre ← decodeFormula tb fuel preE
  let post ← decodeFormula tb fuel postE
  pure ⟨pre, post⟩

/-- Decode an evaluation leaf's concluded sequent: the `Proof`
element's `Proof/concludes` hop, then the judgment decode. -/
def leafSequent (tb : QRowTbls) (e : Nat) : QRes Sequent := do
  let _ ← tb.demandSort e "Proof" "leaf_not_proof_sorted"
  let j ← tb.fld1Elem "Proof/concludes" e
    "leaf_unconcluded" "leaf_dup_concludes"
  decodeSequentOfJudgment tb j

end Decode

end QtslSem

end SuFunctor
