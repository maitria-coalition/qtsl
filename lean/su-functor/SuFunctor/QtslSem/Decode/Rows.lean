import SuFunctor.QtslSem.Decode.Pins
import Reflection.CertRows

/-!
# The QTSL-stratum row scan

`Reflection.CertRows`' scan discipline at the theory-Qtsl stratum: a
sealed artifact's body ops are scanned, fail-closed, into generic row
tables keyed by the *names* the pin table resolves — element sorts in
declaration order, valued function rows, and relation rows.  The scan
is deliberately reading-free: constructor rows and field rows share
the `funa` wire shape, and which reading applies is the assembly's
per-name decision (`Decode.Present`), so the tables stay uniform and
the class-stratum campaign extends coverage by widening the pin table
and adding assembly reads — never by touching the scan.

Refusal classes are `Reflection`'s own (`unreadable` / `unsupported`),
with stable tags and the op index as witness.  Per the CertRows
posture, no stage carries a soundness obligation: downstream
consumption quantifies over whatever was reconstructed, so a decode
defect can lose completeness, never soundness.
-/

namespace SuFunctor

namespace QtslSem

namespace Decode

open PPLC.Geolog

/-- Scanned row tables: element sort names in declaration order,
valued function rows (name, argument cells, value cell) in row order,
and relation rows (name, argument cells) in row order. -/
structure QRowTbls where
  sorts : List String
  funs  : List (String × List GValue × GValue)
  rels  : List (String × List GValue)
  deriving Repr, DecidableEq

/-- Refusal payload: class, stable tag, witness (the CertRows shape). -/
abbrev QFail := RClass × String × Nat

abbrev QRes (α : Type) := Except QFail α

def qerr {α} (c : RClass) (t : String) (w : Nat) : QRes α :=
  .error (c, t, w)

private structure QScanSt where
  sorts : List String := []
  funs  : List (String × List GValue × GValue) := []
  rels  : List (String × List GValue) := []
  i     : Nat := 0

private def qscanOp (deps : List Bytes) (st : QScanSt) :
    GOp → QRes QScanSt
  | .elta r =>
    match r with
    | .loc _ => qerr .unreadable "local_schema_sort_ref" st.i
    | .ext _ _ =>
      match resolveQPin deps r with
      | none => qerr .unsupported "schema_ref_unpinned" st.i
      | some p =>
        if p.kind == .sort then
          pure { st with sorts := p.name :: st.sorts, i := st.i + 1 }
        else qerr .unreadable "sort_position_not_a_sort" st.i
  | .funa r args value =>
    match resolveQPin deps r with
    | none => qerr .unsupported "schema_ref_unpinned" st.i
    | some p =>
      match p.kind with
      | .fn =>
        pure { st with funs := (p.name, args, value) :: st.funs,
                       i := st.i + 1 }
      | .rel => qerr .unreadable "rel_in_fun_position" st.i
      | .sort => qerr .unreadable "sort_in_fun_position" st.i
  | .rela r args =>
    match resolveQPin deps r with
    | none => qerr .unsupported "schema_ref_unpinned" st.i
    | some p =>
      match p.kind with
      | .rel =>
        pure { st with rels := (p.name, args) :: st.rels, i := st.i + 1 }
      | .fn => qerr .unreadable "fun_in_rel_position" st.i
      | .sort => qerr .unreadable "sort_in_rel_position" st.i
  | .eltd _ => qerr .unsupported "eltd_in_qtsl_body" st.i
  | .cert _ _ _ => qerr .unsupported "certblob_in_qtsl_body" st.i
  | .unknown _ _ => qerr .unsupported "op_kind_in_qtsl_body" st.i

private def qscanOpsA (deps : List Bytes) (st : QScanSt) :
    List GOp → QRes QRowTbls
  | [] => pure ⟨st.sorts.reverse, st.funs.reverse, st.rels.reverse⟩
  | op :: rest => do qscanOpsA deps (← qscanOp deps st op) rest

/-- Scan a QTSL-stratum artifact's ops into row tables, fail-closed
against the fragment pin table. -/
def scanQtslOps (deps : List Bytes) (ops : List GOp) : QRes QRowTbls :=
  qscanOpsA deps {} ops

/-! ## Table reads (the assembly's primitives) -/

/-- The sort name of a local element. -/
def QRowTbls.sortAt (tb : QRowTbls) (e : Nat) : Option String :=
  tb.sorts[e]?

/-- Elements of one sort, ascending. -/
def QRowTbls.elemsOfSort (tb : QRowTbls) (s : String) : List Nat :=
  (List.range tb.sorts.length).filter (fun e => tb.sorts[e]? == some s)

/-- All rows of one valued function whose single argument is the given
subject element. -/
def QRowTbls.fldRows (tb : QRowTbls) (name : String) (e : Nat) :
    List GValue :=
  tb.funs.filterMap (fun r =>
    if r.1 == name && r.2.1 == [GValue.ref (.loc e)] then some r.2.2
    else none)

/-- Exactly-one field read: zero rows refuse with `missTag`, two or
more refuse with `dupTag`, the witness is the subject element. -/
def QRowTbls.fld1 (tb : QRowTbls) (name : String) (e : Nat)
    (missTag dupTag : String) : QRes GValue :=
  match tb.fldRows name e with
  | [v] => pure v
  | [] => qerr .unreadable missTag e
  | _ => qerr .unreadable dupTag e

/-- Exactly-one field read, demanding a local-element value. -/
def QRowTbls.fld1Elem (tb : QRowTbls) (name : String) (e : Nat)
    (missTag dupTag : String) : QRes Nat := do
  match elemOfVal (← tb.fld1 name e missTag dupTag) with
  | some v => pure v
  | none => qerr .unreadable (name ++ "_value_not_elem") e

/-- Constructor rows claiming a given element, restricted to a
constructor-name roster (field rows also carry element values, so the
roster is what makes the read a constructor read). -/
def QRowTbls.ctorRowsOf (tb : QRowTbls) (roster : List String)
    (e : Nat) : List (String × List GValue) :=
  tb.funs.filterMap (fun r =>
    if roster.contains r.1 && r.2.2 == GValue.ref (.loc e) then
      some (r.1, r.2.1)
    else none)

/-- Exactly-one constructor read against a roster. -/
def QRowTbls.ctor1 (tb : QRowTbls) (roster : List String) (e : Nat)
    (missTag dupTag : String) : QRes (String × List GValue) :=
  match tb.ctorRowsOf roster e with
  | [c] => pure c
  | [] => qerr .unreadable missTag e
  | _ => qerr .unreadable dupTag e

/-- Relation rows of one name. -/
def QRowTbls.relRows (tb : QRowTbls) (name : String) :
    List (List GValue) :=
  tb.rels.filterMap (fun r => if r.1 == name then some r.2 else none)

/-- Sort check on a local element: refuse with the tag if the element
is missing or of a different sort. -/
def QRowTbls.demandSort (tb : QRowTbls) (e : Nat) (s : String)
    (tag : String) : QRes Unit :=
  if tb.sortAt e == some s then pure () else qerr .unreadable tag e

end Decode

end QtslSem

end SuFunctor
