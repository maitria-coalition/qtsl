import Reflection.Accept

/-!
# Sequent printer for the program route

A total, structure-preserving rendering of accepted claims: terms and
formulas print fully parenthesized (no associativity is flattened
away), region atoms print their whole simplicial complex, and deep
`and`/`or` chains render through an explicit work stack rather than
call recursion — the structural-fact conjunction of a large
certificate nests thousands deep, past any comfortable C stack.

This module is part of the program route's trusted base (see the
package README), not of any kernel-checked path, so `partial` is used
freely.
-/

namespace QtslabLean

open PPLC

/-- Rational constants: `n` when integral, `n/d` otherwise. -/
def renderRat (r : Rat) : String :=
  if r.den == 1 then toString r.num else s!"{r.num}/{r.den}"

/-- Vertex subset of a complex as the set of member indices. -/
def renderVertexSet {n : Nat} (s : Fin n → Bool) : String :=
  let mem := (List.finRange n).filter (fun v => s v)
  "{" ++ String.intercalate "," (mem.map (fun v => toString v.val)) ++ "}"

/-- The full simplicial-complex data (the `Prop` fields carry no
data and do not print). -/
def renderSimpC (K : SimpC) : String :=
  let row (v : Fin K.nVertices) : String :=
    "[" ++ String.intercalate ","
      ((List.finRange K.ambDim).map (fun j => renderRat (K.coord v j))) ++ "]"
  let coords := String.intercalate ","
    ((List.finRange K.nVertices).map row)
  let simps := String.intercalate ","
    (K.simplices.map renderVertexSet)
  let cells := String.intercalate ","
    (K.cells.map (fun c => "(" ++ renderVertexSet c.1 ++ "," ++ renderVertexSet c.2 ++ ")"))
  s!"complex(nv={K.nVertices},dim={K.ambDim},coord=[{coords}],simplices=[{simps}],cells=[{cells}])"

def renderSimplex (s : Simplex) : String :=
  s!"simplex({renderSimpC s.complex},verts={renderVertexSet s.contains})"

def renderExtensionSet (S : ExtensionSet) : String :=
  s!"extset({renderSimplex S.simplex},verts={renderVertexSet S.contains})"

def renderBowTie : BowTie → String
  | .lt => "<" | .le => "<=" | .eq => "=" | .ge => ">=" | .gt => ">" | .ne => "!="

/-- Work items for the iterative renderer. -/
private inductive Tok where
  | str  (s : String)
  | term (t : Term)
  | form (f : Formula)

/-- Structure-preserving render loop: pops a work item, emits string
pieces, pushes children (in reverse) — constant call depth however
deep the formula nests. -/
private partial def renderLoop (stack : List Tok) (acc : Array String) : Array String :=
  match stack with
  | [] => acc
  | .str s :: rest => renderLoop rest (acc.push s)
  | .term t :: rest =>
    match t with
    | .var w    => renderLoop rest (acc.push s!"w{w}")
    | .const c  => renderLoop rest (acc.push (renderRat c))
    | .add l r  => renderLoop (.str "(" :: .term l :: .str " + " :: .term r :: .str ")" :: rest) acc
    | .mul l r  => renderLoop (.str "(" :: .term l :: .str " * " :: .term r :: .str ")" :: rest) acc
    | .sub l r  => renderLoop (.str "(" :: .term l :: .str " - " :: .term r :: .str ")" :: rest) acc
    | .neg u    => renderLoop (.str "(- " :: .term u :: .str ")" :: rest) acc
    | .idx u i  => renderLoop (.str "(" :: .term u :: .str s!")[{i}]" :: rest) acc
  | .form f :: rest =>
    match f with
    | .atom b l r =>
      renderLoop (.str "(" :: .term l :: .str s!" {renderBowTie b} " :: .term r :: .str ")" :: rest) acc
    | .inRegion t sx S =>
      renderLoop (.str "(" :: .term t
        :: .str s!" in {renderSimplex sx} ext {renderExtensionSet S})" :: rest) acc
    | .and l r =>
      renderLoop (.str "(" :: .form l :: .str " /\\ " :: .form r :: .str ")" :: rest) acc
    | .or l r =>
      renderLoop (.str "(" :: .form l :: .str " \\/ " :: .form r :: .str ")" :: rest) acc
    | .tt => renderLoop rest (acc.push "true")
    | .ff => renderLoop rest (acc.push "false")

def renderTerm (t : Term) : String :=
  String.join (renderLoop [.term t] #[]).toList

def renderFormula (f : Formula) : String :=
  String.join (renderLoop [.form f] #[]).toList

/-- The whole accepted sequent: antecedent, turnstile, succedent. -/
def renderSequent (seq : Sequent) : String :=
  String.join (renderLoop [.form seq.pre, .str " |- ", .form seq.post] #[]).toList

end QtslabLean
