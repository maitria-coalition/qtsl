import Qtsl.Core.Prim

/-!
# Exact rational arithmetic (computational core)

The exact-ℚ computational core of the decision procedures: sparse
polynomials as canonically sorted association lists — `Mono`, `Poly`,
canonicalization, the ring operations, substitution, and the Bernstein
forward-difference extraction `fdBernstein`. Everything is computable,
with no floats and no matrix inversion. The correctness theory lives in
`Qtsl.QArithLemmas` and its companions.
-/

namespace PPLC.QArith

abbrev Mono := List (Nat × Nat)

def monoCmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (v₁, e₁) :: r₁, (v₂, e₂) :: r₂ =>
    match compare v₁ v₂ with
    | .lt => .lt
    | .gt => .gt
    | .eq =>
      match compare e₁ e₂ with
      | .lt => .lt
      | .gt => .gt
      | .eq => monoCmp r₁ r₂

def insertVar : Nat × Nat → Mono → Mono
  | p, [] => [p]
  | (v, e), (v', e') :: r =>
    if v < v' then (v, e) :: (v', e') :: r
    else if v = v' then (v, e + e') :: r
    else (v', e') :: insertVar (v, e) r

def monoCanon (m : Mono) : Mono :=
  (m.foldr insertVar []).filter (fun p => p.2 ≠ 0)

def monoMul (a b : Mono) : Mono := monoCanon (a ++ b)

def monoDeg (m : Mono) : Nat := m.foldr (fun p acc => p.2 + acc) 0

abbrev Poly := List (Mono × Rat)

def insertTerm : Mono × Rat → Poly → Poly
  | t, [] => [t]
  | (m, c), (m', c') :: r =>
    match monoCmp m m' with
    | .lt => (m, c) :: (m', c') :: r
    | .eq => (m, c + c') :: r
    | .gt => (m', c') :: insertTerm (m, c) r

namespace Poly

def canon (p : Poly) : Poly :=
  (p.foldr insertTerm []).filter (fun t => t.2 ≠ 0)

def add (p q : Poly) : Poly := canon (p ++ q)

def neg (p : Poly) : Poly := p.map (fun (m, c) => (m, -c))

def sub (p q : Poly) : Poly := add p (neg q)

def scale (a : Rat) (p : Poly) : Poly :=
  if a = 0 then [] else p.map (fun (m, c) => (m, a * c))

def mul (p q : Poly) : Poly :=
  canon (p.flatMap fun (m, c) => q.map fun (m', c') => (monoMul m m', c * c'))

def const (c : Rat) : Poly := if c = 0 then [] else [([], c)]

def var (v : Nat) : Poly := [([(v, 1)], 1)]

def pow (p : Poly) : Nat → Poly
  | 0 => const 1
  | n + 1 => mul p (pow p n)

def totalDeg (p : Poly) : Nat := p.foldr (fun t acc => max (monoDeg t.1) acc) 0

def coeffOf (p : Poly) (m : Mono) : Rat :=
  match p.find? (fun t => decide (t.1 = m)) with
  | some t => t.2
  | none => 0

def vars (p : Poly) : List Nat :=
  (p.flatMap fun t => t.1.map (·.1)).eraseDups

def eval (σ : Nat → Rat) (p : Poly) : Rat :=
  p.foldr (fun (m, c) acc => c * (m.foldr (fun (v, e) a => (σ v) ^ e * a) 1) + acc) 0

def substInto (σ : Nat → Poly) (p : Poly) : Poly :=
  p.foldr (fun (m, c) acc =>
    add acc (scale c (m.foldr (fun (v, e) a => mul (pow (σ v) e) a) (const 1)))) []

end Poly

def multinomial : List Nat → Nat
  | [] => 1
  | a :: rest => Prim.nchoose (a + rest.foldr (·+·) 0) a * multinomial rest

def compositions : Nat → Nat → List (List Nat)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | parts + 1, total =>
    (List.range (total + 1)).flatMap fun a =>
      (compositions parts (total - a)).map (a :: ·)

def compositionsUpTo (parts bound : Nat) : List (List Nat) :=
  (List.range (bound + 1)).flatMap (compositions parts)

def subCompositions : List Nat → List (List Nat)
  | [] => [[]]
  | a :: rest =>
    (List.range (a + 1)).flatMap fun k =>
      (subCompositions rest).map (k :: ·)

def vecToMono (v : List Nat) : Mono :=
  ((List.range v.length).zip v).filter (fun p => p.2 ≠ 0)

def assembleVec : List Bool → List Nat → List Nat → List Nat
  | [], _, _ => []
  | true :: rest, k₀ :: ks, β => k₀ :: assembleVec rest ks β
  | true :: rest, [], β => 0 :: assembleVec rest [] β
  | false :: rest, k, b₀ :: bs => b₀ :: assembleVec rest k bs
  | false :: rest, k, [] => 0 :: assembleVec rest k []

def sumVars (m : Nat) : Poly :=
  Poly.canon ((List.range m).map fun i => ([(i, 1)], (1 : Rat)))

def coordPoly (verts : List (List Rat)) (j : Nat) : Poly :=
  Poly.canon ((List.range verts.length).map fun i =>
    ([(i, 1)], (verts.getD i []).getD j 0))

def homogenize (m d : Nat) (p : Poly) : Option Poly :=
  p.foldr
    (fun (mo, c) acc => do
      let acc ← acc
      let e := monoDeg mo
      if e ≤ d then
        pure (Poly.add acc (Poly.mul [(mo, c)] (Poly.pow (sumVars m) (d - e))))
      else none)
    (some [])

def bernCoeffRows (m d : Nat) (hp : Poly) : List (List Nat × Rat) :=
  (compositions m d).map fun α =>
    (α, hp.coeffOf (vecToMono α) / (multinomial α : Rat))

structure FDTable where

  base : List (List Nat × Rat)

  grid : List (List Nat × List (List Nat × Rat))
  deriving Repr, DecidableEq

def fdBernstein (verts : List (List Rat)) (smask : List Bool) (d : Nat)
    (p : Poly) : Option FDTable := do
  let m := verts.length
  guard (smask.length = m)
  let mS := (smask.filter id).length
  let mB := m - mS
  guard (0 < mB)

  let pLam := Poly.substInto (coordPoly verts) p
  let hp ← homogenize m d pLam
  let base := bernCoeffRows m d hp

  let bAt := fun (k β : List Nat) =>
    let α := assembleVec smask k β
    hp.coeffOf (vecToMono α) / (multinomial α : Rat)

  let grid := (compositionsUpTo mS d).map fun j =>
    let pj := (subCompositions j).foldr
      (fun k acc =>
        let sgn : Rat := if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1
        let binomProd : Nat := ((j.zip k).map fun (ji, ki) => Prim.nchoose ji ki).foldr (·*·) 1

        let kSum := k.foldr (·+·) 0
        let qk := Poly.canon ((compositions mB (d - kSum)).map fun β =>
          (vecToMono β, bAt k β * (multinomial β : Rat)))

        let hk := Poly.mul qk (Poly.pow (sumVars mB) kSum)
        Poly.add acc (Poly.scale (sgn * (binomProd : Rat)) hk))
      []
    (j, bernCoeffRows mB d pj)
  pure { base := base, grid := grid }

def gridAll (pred : Rat → Bool) (t : FDTable) : Bool :=
  t.grid.all fun (_, row) => row.all fun (_, c) => pred c

def starIdentityCheck (verts : List (List Rat)) (smask : List Bool) (d : Nat)
    (p : Poly) (u : List Rat) (yFace : List Rat) : Option Bool := do
  let t ← fdBernstein verts smask d p
  let mB := (smask.filter (!·)).length
  guard (u.length = (smask.filter id).length)
  guard (yFace.length = mB)
  let bigU := u.foldr (·+·) 0

  let lamS : List Rat := u.map (fun ui => -ui)
  let lamB : List Rat := yFace.map (fun yi => (1 + bigU) * yi)
  let lam : List Rat := assembleVecQ smask lamS lamB

  let lhs := t.base.foldr
    (fun (α, b) acc =>
      acc + b * (multinomial α : Rat) *
        ((α.zip lam).foldr (fun (e, l) a => l ^ e * a) 1))
    (0 : Rat)

  let rhs := t.grid.foldr
    (fun (j, row) acc =>
      let jSum := j.foldr (·+·) 0
      let mult : Rat := (Prim.nchoose d jSum : Rat) * (multinomial j : Rat)
      let uPow := ((j.zip u).foldr (fun (e, ui) a => ui ^ e * a) 1)
      let pjAtY := row.foldr
        (fun (γ, c) a =>
          a + c * (multinomial γ : Rat) *
            ((γ.zip yFace).foldr (fun (e, yi) b => yi ^ e * b) 1))
        0
      acc + mult * uPow * pjAtY)
    (0 : Rat)
  pure (decide (lhs = rhs))
where

  assembleVecQ : List Bool → List Rat → List Rat → List Rat
    | [], _, _ => []
    | true :: rest, k₀ :: ks, β => k₀ :: assembleVecQ rest ks β
    | true :: rest, [], β => 0 :: assembleVecQ rest [] β
    | false :: rest, k, b₀ :: bs => b₀ :: assembleVecQ rest k bs
    | false :: rest, k, [] => 0 :: assembleVecQ rest k []

end PPLC.QArith
