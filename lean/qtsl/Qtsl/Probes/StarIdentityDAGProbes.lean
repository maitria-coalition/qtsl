import Qtsl.QArith

/-!
# Computational probes for the star-identity lemma graph

Statement-level probes for the risky lemmas of
`Qtsl.StarIdentityDAG`: each `#eval` prints
`(lhs, rhs, lhs == rhs)`, with `true` expected in the third slot.
-/

open PPLC PPLC.QArith

def hashL (l : List Nat) : Rat :=
  l.foldr (fun a acc => acc * 31 + (a : Rat) + 1/7) 1

def hash2 (a b : List Nat) : Rat := hashL a * 131 + hashL b * (5/3)

def zipPowQ (γ : List Nat) (x : List Rat) : Rat :=
  (γ.zip x).foldr (fun (e, l) a => l ^ e * a) 1

def d5probe (smask : List Bool) (d : Nat) : (Rat × Rat × Bool) :=
  let m := smask.length
  let mS := (smask.filter id).length
  let mB := (smask.filter (!·)).length
  let lhs := ((compositions m d).map hashL).foldr (·+·) 0
  let rhs := ((compositionsUpTo mS d).map (fun k =>
    ((compositions mB (d - k.foldr (·+·) 0)).map (fun β =>
      hashL (assembleVec smask k β))).foldr (·+·) 0)).foldr (·+·) 0
  (lhs, rhs, lhs == rhs)

#eval d5probe [true, false] 3
#eval d5probe [false, true, true, false] 2
#eval d5probe [true, true, false] 4
#eval d5probe [false, false, false] 3
#eval d5probe [true, true] 0
#eval d5probe [] 0
#eval d5probe [] 2
#eval d5probe [true] 2

def d6probe (n d : Nat) : (Rat × Rat × Bool) :=
  let lhs := ((compositionsUpTo n d).map (fun j =>
    ((subCompositions j).map (fun k => hash2 j k)).foldr (·+·) 0)).foldr (·+·) 0
  let rhs := ((compositionsUpTo n d).map (fun k =>
    ((compositionsUpTo n (d - k.foldr (·+·) 0)).map (fun t =>
      hash2 (List.zipWith (·+·) k t) k)).foldr (·+·) 0)).foldr (·+·) 0
  (lhs, rhs, lhs == rhs)

#eval d6probe 1 3
#eval d6probe 2 2
#eval d6probe 2 4
#eval d6probe 3 2
#eval d6probe 0 2
#eval d6probe 0 0

def c5probe (d : Nat) (k t : List Nat) : (Nat × Nat × Bool) :=
  let j := List.zipWith (·+·) k t
  let sj := j.foldr (·+·) 0
  let sk := k.foldr (·+·) 0
  let st := t.foldr (·+·) 0
  let binomProd := ((j.zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1
  let lhs := Prim.nchoose d sj * multinomial j * binomProd
  let rhs := Prim.nchoose d sk * multinomial k * Prim.nchoose (d - sk) st * multinomial t
  (lhs, rhs, lhs == rhs)

#eval c5probe 5 [1,0,2] [0,1,1]
#eval c5probe 4 [2,0] [1,1]
#eval c5probe 7 [0,3] [2,0]
#eval c5probe 3 [] []
#eval c5probe 6 [1,1,1] [1,1,0]

def c3probe (smask : List Bool) (k β : List Nat) : (Nat × Nat × Bool) :=
  let d := k.foldr (·+·) 0 + β.foldr (·+·) 0
  let lhs := multinomial (assembleVec smask k β)
  let rhs := Prim.nchoose d (k.foldr (·+·) 0) * multinomial k * multinomial β
  (lhs, rhs, lhs == rhs)

#eval c3probe [true, false, false] [2] [1, 3]
#eval c3probe [false, true, true, false] [1, 2] [0, 4]
#eval c3probe [true, true] [3, 1] []
#eval c3probe [false] [] [5]

def g1probe (smask : List Bool) (d : Nat) (u y : List Rat) : (Rat × Rat × Bool) :=
  let m := smask.length
  let mS := (smask.filter id).length
  let mB := (smask.filter (!·)).length
  let bigU := u.foldr (·+·) 0
  let lamS := u.map (fun ui => -ui)
  let lamB := y.map (fun yi => (1 + bigU) * yi)

  let rec asmQ : List Bool → List Rat → List Rat → List Rat
    | [], _, _ => []
    | true :: rest, k₀ :: ks, b => k₀ :: asmQ rest ks b
    | true :: rest, [], b => 0 :: asmQ rest [] b
    | false :: rest, k, b₀ :: bs => b₀ :: asmQ rest k bs
    | false :: rest, k, [] => 0 :: asmQ rest k []
  let lam := asmQ smask lamS lamB
  let lhs := ((compositions m d).map (fun α => hashL α * zipPowQ α lam)).foldr (·+·) 0
  let rhs := ((compositionsUpTo mS d).map (fun j =>
    (Prim.nchoose d (j.foldr (·+·) 0) : Rat) * (multinomial j : Rat) * zipPowQ j u *
      ((subCompositions j).map (fun k =>
        (if (k.foldr (·+·) 0) % 2 = 0 then (1:Rat) else -1) *
          (((j.zip k).map fun q => Prim.nchoose q.1 q.2).foldr (·*·) 1 : Nat) *
          ((compositions mB (d - k.foldr (·+·) 0)).map (fun β =>
            hashL (assembleVec smask k β)
              / (multinomial (assembleVec smask k β) : Rat)
              * (multinomial β : Rat) * zipPowQ β y)).foldr (·+·) 0)).foldr (·+·) 0)).foldr (·+·) 0
  (lhs, rhs, lhs == rhs)

#eval g1probe [true, false, false] 2 [1/2] [1/3, 5]
#eval g1probe [false, true, true, false] 3 [1/2, -1/3] [2, -3/4]
#eval g1probe [true, true, false] 4 [-1/2, 1/3] [7/5]
#eval g1probe [false, false] 2 [] [1/2, 1/3]
#eval g1probe [true, false] 3 [2/3] [-4]
