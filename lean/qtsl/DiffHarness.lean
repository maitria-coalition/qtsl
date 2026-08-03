import Qtsl.QArith

/-!
# Differential-testing harness (Lean leg)

Reads a shared case file, runs the exact-rational Bernstein
forward-difference core (`PPLC.QArith.fdBernstein`), and emits a keyed
output grammar shared with independent implementations of the same
arithmetic, so that the implementations can adjudicate one another over
a common corpus. Enumeration order is not part of the contract; the
comparison is by key.

This module is an instrument, not part of the trusted base.
-/

open PPLC.QArith

namespace DiffHarness

def parseInt! (s : String) : Int :=
  match s.toInt? with
  | some i => i
  | none => panic! s!"bad int: {s}"

def parseNat! (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none => panic! s!"bad nat: {s}"

def parseQ (s : String) : ℚ :=
  match s.splitOn "/" with
  | [n] => mkRat (parseInt! n) 1
  | [n, d] => mkRat (parseInt! n) (parseNat! d)
  | _ => panic! s!"bad rational: {s}"

def fmtQ (q : ℚ) : String := s!"{q.num}/{q.den}"

def fmtIdx (v : List Nat) : String :=
  if v.isEmpty then "-" else String.intercalate "," (v.map toString)

structure Case where
  id : String
  n : Nat
  d : Nat
  sSet : List Nat
  verts : List (List ℚ)
  terms : List (List Nat × ℚ)

def runCase (c : Case) : List String := Id.run do
  let nv := c.n + 1
  let smask := (List.range nv).map (c.sSet.contains ·)
  let p : Poly := Poly.canon (c.terms.map fun (mu, coeff) => (vecToMono mu, coeff))
  match fdBernstein c.verts smask c.d p with
  | none => panic! s!"{c.id}: fdBernstein returned none (mask/degree guard)"
  | some t =>
    let mut out : List String := [s!"CASE {c.id}"]
    for (alpha, b) in t.base do
      out := s!"B {fmtIdx alpha} {fmtQ b}" :: out
    for (j, row) in t.grid do
      for (gamma, cjg) in row do
        out := s!"G {fmtIdx j} {fmtIdx gamma} {fmtQ cjg}" :: out
    return ("END" :: out).reverse

def parseCases (text : String) : List Case := Id.run do
  let mut cases : List Case := []
  let mut cur : Case := ⟨"", 0, 0, [], [], []⟩
  for line in text.splitOn "\n" do
    let toks := (line.splitOn " ").filter (· ≠ "")
    match toks with
    | [] => pure ()
    | key :: rest =>
      match key with
      | "CASE" => cur := ⟨rest.head!, 0, 0, [], [], []⟩
      | "N" => cur := { cur with n := parseNat! rest.head! }
      | "D" => cur := { cur with d := parseNat! rest.head! }
      | "S" => cur := { cur with sSet := rest.map parseNat! }
      | "V" => cur := { cur with verts := cur.verts ++ [rest.map parseQ] }
      | "T" =>
        let exps := (rest.dropLast).map parseNat!
        let coeff := parseQ rest.getLast!
        cur := { cur with terms := cur.terms ++ [(exps, coeff)] }
      | "END" => cases := cur :: cases
      | other => panic! s!"unknown line key: {other}"
  return cases.reverse

end DiffHarness

def main (args : List String) : IO Unit := do
  let (src, dst) :=
    match args with
    | [s, d] => (s, d)
    | _ => panic! "usage: diffharness <cases.txt> <out.txt>"
  let text ← IO.FS.readFile src
  let cases := DiffHarness.parseCases text
  let out := cases.flatMap DiffHarness.runCase
  IO.FS.writeFile dst (String.intercalate "\n" out ++ "\n")
  IO.println s!"lean: {cases.length} cases -> {dst}"
