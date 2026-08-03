import Qtsl.Soundness
import Qtsl.Decide
import Qtsl.Admissible

/-!
# Composite syzygy certificate (generated)

Generated from certificate bytes by the untrusted export tool — a wrong
translation is refused by Lean, never silently accepted. Do not edit by
hand. Interned pools and `ProofObject` definitions for the primitive
subtrees; side conditions by `decide +kernel`; the endpoint is the
`_valid` theorem and its axiom closure.
-/

namespace PPLC.Handshake.DpCompositeSyzygy

open PPLC

set_option maxRecDepth 4096

set_option maxHeartbeats 40000000

def cx0coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(9/20), (9/10), (-3/20)],
   [(9/20), (99/100), (-3/20)],
   [(9/20), (99/100), (3/20)]]

def cx0 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx0coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx1coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(9/20), (9/10), (-3/20)],
   [(9/20), (9/10), (3/20)],
   [(9/20), (99/100), (3/20)]]

def cx1 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx1coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx2coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(-9/20), (99/100), (-3/20)],
   [(9/20), (99/100), (-3/20)],
   [(9/20), (99/100), (3/20)]]

def cx2 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx2coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx3coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(-9/20), (99/100), (-3/20)],
   [(-9/20), (99/100), (3/20)],
   [(9/20), (99/100), (3/20)]]

def cx3 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx3coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx4coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(-9/20), (9/10), (3/20)],
   [(9/20), (9/10), (3/20)],
   [(9/20), (99/100), (3/20)]]

def cx4 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx4coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx5coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/20)],
   [(-9/20), (9/10), (3/20)],
   [(-9/20), (99/100), (3/20)],
   [(9/20), (99/100), (3/20)]]

def cx5 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx5coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx6coords : List (List Rat) :=
  [[0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0],
   [(9/20), 1, (3/5)]]

def cx6 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx6coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx7coords : List (List Rat) :=
  [[0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), (9/10), (3/5)],
   [(9/20), 1, (3/5)]]

def cx7 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx7coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx8coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, 1, 0],
   [(9/20), 1, 0],
   [(9/20), 1, (3/5)]]

def cx8 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx8coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx9coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, 1, 0],
   [0, 1, (3/5)],
   [(9/20), 1, (3/5)]]

def cx9 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx9coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx10coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, (9/10), (3/5)],
   [(9/20), (9/10), (3/5)],
   [(9/20), 1, (3/5)]]

def cx10 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx10coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx11coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)],
   [(9/20), 1, (3/5)]]

def cx11 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx11coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx12coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)],
   [0, 1, (3/5)]]

def cx12 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx12coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx13coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)]]

def cx13 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx13coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx14coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)],
   [0, 1, (3/5)]]

def cx14 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx14coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx15coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [(-9/20), 1, (3/5)],
   [0, 1, (3/5)]]

def cx15 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx15coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx16coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), (9/10), (3/5)],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)]]

def cx16 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx16coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx17coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), (9/10), (3/5)],
   [(-9/20), 1, (3/5)],
   [0, 1, (3/5)]]

def cx17 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx17coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx18coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, 1, 0],
   [0, 1, (3/10)]]

def cx18 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx18coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx19coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)]]

def cx19 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx19coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx20coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [0, 1, 0],
   [0, 1, (3/10)]]

def cx20 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx20coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx21coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)]]

def cx21 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx21coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx22coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)]]

def cx22 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx22coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx23coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)]]

def cx23 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx23coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx24coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)],
   [(9/20), 1, 0]]

def cx24 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx24coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx25coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0]]

def cx25 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx25coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx26coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)],
   [(9/20), 1, 0]]

def cx26 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx26coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx27coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [0, 1, 0],
   [(9/20), 1, 0]]

def cx27 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx27coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx28coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0]]

def cx28 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx28coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx29coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, (9/10), 0],
   [0, 1, 0],
   [(9/20), 1, 0]]

def cx29 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx29coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx30coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [(9/20), (9/10), (-3/5)],
   [(9/20), 1, (-3/5)],
   [(9/20), 1, (-3/10)]]

def cx30 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx30coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx31coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [(9/20), (9/10), (-3/5)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx31 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx31coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx32coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [(9/20), 1, (-3/5)],
   [(9/20), 1, (-3/10)]]

def cx32 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx32coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx33coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx33 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx33coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx34coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx34 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx34coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx35coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx35 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx35coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx36coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, 0]]

def cx36 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx36coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx37coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [0, (9/10), (-3/5)],
   [0, (9/10), 0],
   [0, 1, 0]]

def cx37 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx37coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx38coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), 1, (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, 0]]

def cx38 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx38coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx39coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), 1, (-3/5)],
   [(-9/20), 1, 0],
   [0, 1, 0]]

def cx39 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx39coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx40coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, 1, 0]]

def cx40 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx40coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def cx41coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [0, 1, 0]]

def cx41 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx41coords.getD v.val []).getD j.val 0
  simplices :=
  [
    fun v => [true, false, false, false].getD v.val false,
    fun v => [false, true, false, false].getD v.val false,
    fun v => [true, true, false, false].getD v.val false,
    fun v => [false, false, true, false].getD v.val false,
    fun v => [true, false, true, false].getD v.val false,
    fun v => [false, true, true, false].getD v.val false,
    fun v => [true, true, true, false].getD v.val false,
    fun v => [false, false, false, true].getD v.val false,
    fun v => [true, false, false, true].getD v.val false,
    fun v => [false, true, false, true].getD v.val false,
    fun v => [true, true, false, true].getD v.val false,
    fun v => [false, false, true, true].getD v.val false,
    fun v => [true, false, true, true].getD v.val false,
    fun v => [false, true, true, true].getD v.val false,
    fun _ => true
  ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def Hnet : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[3], Dtype.Q⟩ else if w = 1 then some ⟨[1], Dtype.Q⟩ else if w = 2 then some ⟨[3], Dtype.Q⟩ else if w = 3 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

def spH : Formula := Hnet.spConjunction

def tm0 : Term :=
  (.add (.mul (.const 1) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.mul (.const 1) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))))

def f0 : Formula :=
  .atom .eq tm0 (.const 1)

def sx0 : Simplex :=
  ⟨cx0, fun _ => true, by decide +kernel⟩

def ex0 : ExtensionSet :=
  ⟨sx0, fun _ => false, by decide +kernel, by decide +kernel⟩

def f1 : Formula :=
  .inRegion (.var 0) sx0 ex0

def sx1 : Simplex :=
  ⟨cx1, fun _ => true, by decide +kernel⟩

def ex1 : ExtensionSet :=
  ⟨sx1, fun _ => false, by decide +kernel, by decide +kernel⟩

def f2 : Formula :=
  .inRegion (.var 0) sx1 ex1

def sx2 : Simplex :=
  ⟨cx2, fun _ => true, by decide +kernel⟩

def ex2 : ExtensionSet :=
  ⟨sx2, fun _ => false, by decide +kernel, by decide +kernel⟩

def f3 : Formula :=
  .inRegion (.var 0) sx2 ex2

def sx3 : Simplex :=
  ⟨cx3, fun _ => true, by decide +kernel⟩

def ex3 : ExtensionSet :=
  ⟨sx3, fun _ => false, by decide +kernel, by decide +kernel⟩

def f4 : Formula :=
  .inRegion (.var 0) sx3 ex3

def sx4 : Simplex :=
  ⟨cx4, fun _ => true, by decide +kernel⟩

def ex4 : ExtensionSet :=
  ⟨sx4, fun _ => false, by decide +kernel, by decide +kernel⟩

def f5 : Formula :=
  .inRegion (.var 0) sx4 ex4

def sx5 : Simplex :=
  ⟨cx5, fun _ => true, by decide +kernel⟩

def ex5 : ExtensionSet :=
  ⟨sx5, fun _ => false, by decide +kernel, by decide +kernel⟩

def f6 : Formula :=
  .inRegion (.var 0) sx5 ex5

def f7 : Formula :=
  .or f5 f6

def f8 : Formula :=
  .or f4 f7

def f9 : Formula :=
  .or f3 f8

def f10 : Formula :=
  .or f2 f9

def f11 : Formula :=
  .or f1 f10

def f12 : Formula :=
  .and f0 f11

def tm1 : Term :=
  (.add (.mul (.const 1) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.mul (.const 1) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))))

def f13 : Formula :=
  .atom .eq tm1 (.const 1)

def sx6 : Simplex :=
  ⟨cx6, fun _ => true, by decide +kernel⟩

def ex6 : ExtensionSet :=
  ⟨sx6, fun _ => false, by decide +kernel, by decide +kernel⟩

def f14 : Formula :=
  .inRegion (.var 2) sx6 ex6

def sx7 : Simplex :=
  ⟨cx7, fun _ => true, by decide +kernel⟩

def ex7 : ExtensionSet :=
  ⟨sx7, fun _ => false, by decide +kernel, by decide +kernel⟩

def f15 : Formula :=
  .inRegion (.var 2) sx7 ex7

def sx8 : Simplex :=
  ⟨cx8, fun _ => true, by decide +kernel⟩

def ex8 : ExtensionSet :=
  ⟨sx8, fun _ => false, by decide +kernel, by decide +kernel⟩

def f16 : Formula :=
  .inRegion (.var 2) sx8 ex8

def sx9 : Simplex :=
  ⟨cx9, fun _ => true, by decide +kernel⟩

def ex9 : ExtensionSet :=
  ⟨sx9, fun _ => false, by decide +kernel, by decide +kernel⟩

def f17 : Formula :=
  .inRegion (.var 2) sx9 ex9

def sx10 : Simplex :=
  ⟨cx10, fun _ => true, by decide +kernel⟩

def ex10 : ExtensionSet :=
  ⟨sx10, fun _ => false, by decide +kernel, by decide +kernel⟩

def f18 : Formula :=
  .inRegion (.var 2) sx10 ex10

def sx11 : Simplex :=
  ⟨cx11, fun _ => true, by decide +kernel⟩

def ex11 : ExtensionSet :=
  ⟨sx11, fun _ => false, by decide +kernel, by decide +kernel⟩

def f19 : Formula :=
  .inRegion (.var 2) sx11 ex11

def sx12 : Simplex :=
  ⟨cx12, fun _ => true, by decide +kernel⟩

def ex12 : ExtensionSet :=
  ⟨sx12, fun _ => false, by decide +kernel, by decide +kernel⟩

def f20 : Formula :=
  .inRegion (.var 2) sx12 ex12

def sx13 : Simplex :=
  ⟨cx13, fun _ => true, by decide +kernel⟩

def ex13 : ExtensionSet :=
  ⟨sx13, fun _ => false, by decide +kernel, by decide +kernel⟩

def f21 : Formula :=
  .inRegion (.var 2) sx13 ex13

def sx14 : Simplex :=
  ⟨cx14, fun _ => true, by decide +kernel⟩

def ex14 : ExtensionSet :=
  ⟨sx14, fun _ => false, by decide +kernel, by decide +kernel⟩

def f22 : Formula :=
  .inRegion (.var 2) sx14 ex14

def sx15 : Simplex :=
  ⟨cx15, fun _ => true, by decide +kernel⟩

def ex15 : ExtensionSet :=
  ⟨sx15, fun _ => false, by decide +kernel, by decide +kernel⟩

def f23 : Formula :=
  .inRegion (.var 2) sx15 ex15

def sx16 : Simplex :=
  ⟨cx16, fun _ => true, by decide +kernel⟩

def ex16 : ExtensionSet :=
  ⟨sx16, fun _ => false, by decide +kernel, by decide +kernel⟩

def f24 : Formula :=
  .inRegion (.var 2) sx16 ex16

def sx17 : Simplex :=
  ⟨cx17, fun _ => true, by decide +kernel⟩

def ex17 : ExtensionSet :=
  ⟨sx17, fun _ => false, by decide +kernel, by decide +kernel⟩

def f25 : Formula :=
  .inRegion (.var 2) sx17 ex17

def sx18 : Simplex :=
  ⟨cx18, fun _ => true, by decide +kernel⟩

def ex18 : ExtensionSet :=
  ⟨sx18, fun _ => false, by decide +kernel, by decide +kernel⟩

def f26 : Formula :=
  .inRegion (.var 2) sx18 ex18

def sx19 : Simplex :=
  ⟨cx19, fun _ => true, by decide +kernel⟩

def ex19 : ExtensionSet :=
  ⟨sx19, fun _ => false, by decide +kernel, by decide +kernel⟩

def f27 : Formula :=
  .inRegion (.var 2) sx19 ex19

def sx20 : Simplex :=
  ⟨cx20, fun _ => true, by decide +kernel⟩

def ex20 : ExtensionSet :=
  ⟨sx20, fun _ => false, by decide +kernel, by decide +kernel⟩

def f28 : Formula :=
  .inRegion (.var 2) sx20 ex20

def sx21 : Simplex :=
  ⟨cx21, fun _ => true, by decide +kernel⟩

def ex21 : ExtensionSet :=
  ⟨sx21, fun _ => false, by decide +kernel, by decide +kernel⟩

def f29 : Formula :=
  .inRegion (.var 2) sx21 ex21

def sx22 : Simplex :=
  ⟨cx22, fun _ => true, by decide +kernel⟩

def ex22 : ExtensionSet :=
  ⟨sx22, fun _ => false, by decide +kernel, by decide +kernel⟩

def f30 : Formula :=
  .inRegion (.var 2) sx22 ex22

def sx23 : Simplex :=
  ⟨cx23, fun _ => true, by decide +kernel⟩

def ex23 : ExtensionSet :=
  ⟨sx23, fun _ => false, by decide +kernel, by decide +kernel⟩

def f31 : Formula :=
  .inRegion (.var 2) sx23 ex23

def sx24 : Simplex :=
  ⟨cx24, fun _ => true, by decide +kernel⟩

def ex24 : ExtensionSet :=
  ⟨sx24, fun _ => false, by decide +kernel, by decide +kernel⟩

def f32 : Formula :=
  .inRegion (.var 2) sx24 ex24

def sx25 : Simplex :=
  ⟨cx25, fun _ => true, by decide +kernel⟩

def ex25 : ExtensionSet :=
  ⟨sx25, fun _ => false, by decide +kernel, by decide +kernel⟩

def f33 : Formula :=
  .inRegion (.var 2) sx25 ex25

def sx26 : Simplex :=
  ⟨cx26, fun _ => true, by decide +kernel⟩

def ex26 : ExtensionSet :=
  ⟨sx26, fun _ => false, by decide +kernel, by decide +kernel⟩

def f34 : Formula :=
  .inRegion (.var 2) sx26 ex26

def sx27 : Simplex :=
  ⟨cx27, fun _ => true, by decide +kernel⟩

def ex27 : ExtensionSet :=
  ⟨sx27, fun _ => false, by decide +kernel, by decide +kernel⟩

def f35 : Formula :=
  .inRegion (.var 2) sx27 ex27

def sx28 : Simplex :=
  ⟨cx28, fun _ => true, by decide +kernel⟩

def ex28 : ExtensionSet :=
  ⟨sx28, fun _ => false, by decide +kernel, by decide +kernel⟩

def f36 : Formula :=
  .inRegion (.var 2) sx28 ex28

def sx29 : Simplex :=
  ⟨cx29, fun _ => true, by decide +kernel⟩

def ex29 : ExtensionSet :=
  ⟨sx29, fun _ => false, by decide +kernel, by decide +kernel⟩

def f37 : Formula :=
  .inRegion (.var 2) sx29 ex29

def sx30 : Simplex :=
  ⟨cx30, fun _ => true, by decide +kernel⟩

def ex30 : ExtensionSet :=
  ⟨sx30, fun _ => false, by decide +kernel, by decide +kernel⟩

def f38 : Formula :=
  .inRegion (.var 2) sx30 ex30

def sx31 : Simplex :=
  ⟨cx31, fun _ => true, by decide +kernel⟩

def ex31 : ExtensionSet :=
  ⟨sx31, fun _ => false, by decide +kernel, by decide +kernel⟩

def f39 : Formula :=
  .inRegion (.var 2) sx31 ex31

def sx32 : Simplex :=
  ⟨cx32, fun _ => true, by decide +kernel⟩

def ex32 : ExtensionSet :=
  ⟨sx32, fun _ => false, by decide +kernel, by decide +kernel⟩

def f40 : Formula :=
  .inRegion (.var 2) sx32 ex32

def sx33 : Simplex :=
  ⟨cx33, fun _ => true, by decide +kernel⟩

def ex33 : ExtensionSet :=
  ⟨sx33, fun _ => false, by decide +kernel, by decide +kernel⟩

def f41 : Formula :=
  .inRegion (.var 2) sx33 ex33

def sx34 : Simplex :=
  ⟨cx34, fun _ => true, by decide +kernel⟩

def ex34 : ExtensionSet :=
  ⟨sx34, fun _ => false, by decide +kernel, by decide +kernel⟩

def f42 : Formula :=
  .inRegion (.var 2) sx34 ex34

def sx35 : Simplex :=
  ⟨cx35, fun _ => true, by decide +kernel⟩

def ex35 : ExtensionSet :=
  ⟨sx35, fun _ => false, by decide +kernel, by decide +kernel⟩

def f43 : Formula :=
  .inRegion (.var 2) sx35 ex35

def sx36 : Simplex :=
  ⟨cx36, fun _ => true, by decide +kernel⟩

def ex36 : ExtensionSet :=
  ⟨sx36, fun _ => false, by decide +kernel, by decide +kernel⟩

def f44 : Formula :=
  .inRegion (.var 2) sx36 ex36

def sx37 : Simplex :=
  ⟨cx37, fun _ => true, by decide +kernel⟩

def ex37 : ExtensionSet :=
  ⟨sx37, fun _ => false, by decide +kernel, by decide +kernel⟩

def f45 : Formula :=
  .inRegion (.var 2) sx37 ex37

def sx38 : Simplex :=
  ⟨cx38, fun _ => true, by decide +kernel⟩

def ex38 : ExtensionSet :=
  ⟨sx38, fun _ => false, by decide +kernel, by decide +kernel⟩

def f46 : Formula :=
  .inRegion (.var 2) sx38 ex38

def sx39 : Simplex :=
  ⟨cx39, fun _ => true, by decide +kernel⟩

def ex39 : ExtensionSet :=
  ⟨sx39, fun _ => false, by decide +kernel, by decide +kernel⟩

def f47 : Formula :=
  .inRegion (.var 2) sx39 ex39

def sx40 : Simplex :=
  ⟨cx40, fun _ => true, by decide +kernel⟩

def ex40 : ExtensionSet :=
  ⟨sx40, fun _ => false, by decide +kernel, by decide +kernel⟩

def f48 : Formula :=
  .inRegion (.var 2) sx40 ex40

def sx41 : Simplex :=
  ⟨cx41, fun _ => true, by decide +kernel⟩

def ex41 : ExtensionSet :=
  ⟨sx41, fun _ => false, by decide +kernel, by decide +kernel⟩

def f49 : Formula :=
  .inRegion (.var 2) sx41 ex41

def f50 : Formula :=
  .or f48 f49

def f51 : Formula :=
  .or f47 f50

def f52 : Formula :=
  .or f46 f51

def f53 : Formula :=
  .or f45 f52

def f54 : Formula :=
  .or f44 f53

def f55 : Formula :=
  .or f43 f54

def f56 : Formula :=
  .or f42 f55

def f57 : Formula :=
  .or f41 f56

def f58 : Formula :=
  .or f40 f57

def f59 : Formula :=
  .or f39 f58

def f60 : Formula :=
  .or f38 f59

def f61 : Formula :=
  .or f37 f60

def f62 : Formula :=
  .or f36 f61

def f63 : Formula :=
  .or f35 f62

def f64 : Formula :=
  .or f34 f63

def f65 : Formula :=
  .or f33 f64

def f66 : Formula :=
  .or f32 f65

def f67 : Formula :=
  .or f31 f66

def f68 : Formula :=
  .or f30 f67

def f69 : Formula :=
  .or f29 f68

def f70 : Formula :=
  .or f28 f69

def f71 : Formula :=
  .or f27 f70

def f72 : Formula :=
  .or f26 f71

def f73 : Formula :=
  .or f25 f72

def f74 : Formula :=
  .or f24 f73

def f75 : Formula :=
  .or f23 f74

def f76 : Formula :=
  .or f22 f75

def f77 : Formula :=
  .or f21 f76

def f78 : Formula :=
  .or f20 f77

def f79 : Formula :=
  .or f19 f78

def f80 : Formula :=
  .or f18 f79

def f81 : Formula :=
  .or f17 f80

def f82 : Formula :=
  .or f16 f81

def f83 : Formula :=
  .or f15 f82

def f84 : Formula :=
  .or f14 f83

def f85 : Formula :=
  .and f13 f84

def f86 : Formula :=
  .and f12 f85

def f87 : Formula :=
  .and f86 spH

def tm2 : Term :=
  (.add (.mul (.const 400) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const 400) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2000)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2000)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const 7)))))))))

def f88 : Formula :=
  .atom .le tm2 (.const 0)

def sq0 : Sequent := ⟨f87, f88⟩

def tm3 : Term :=
  (.add (.mul (.const 40) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-80)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-160)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-200)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const 1)))))

def f89 : Formula :=
  .atom .le tm3 (.const 0)

def sq1 : Sequent := ⟨f12, f89⟩

def f90 : Formula :=
  .and f0 f1

def sq2 : Sequent := ⟨f90, f89⟩

def tm4 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-430029/3497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (143059/719344)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (364595/80499)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-443783/258464)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (139023790/188939)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-2305084/425353)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24842764/213797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1199836943/866674)) (.idx (.var 0) 1)) (.add (.mul (.const (1619845/584147)) (.idx (.var 0) 2)) (.const (266029763/407891))))))))))) (.sub (.const 1) (.const 1))))

def f91 : Formula :=
  .atom .le tm4 (.const 0)

def sq3 : Sequent := ⟨f90, f91⟩

def sq4 : Sequent := ⟨f90, f0⟩

def sq5 : Sequent := ⟨f90, f90⟩

def tm5 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-430029/3497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (143059/719344)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (364595/80499)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-443783/258464)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (139023790/188939)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-2305084/425353)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24842764/213797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1199836943/866674)) (.idx (.var 0) 1)) (.add (.mul (.const (1619845/584147)) (.idx (.var 0) 2)) (.const (266029763/407891))))))))))) (.sub tm0 (.const 1))))

def f92 : Formula :=
  .atom .le tm5 (.const 0)

def sq6 : Sequent := ⟨f90, f92⟩

def sq7 : Sequent := ⟨f90, f1⟩

def f93 : Formula :=
  .atom .le (.var predicateHole) (.const 0)

def tm6 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-430029/3497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (143059/719344)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (364595/80499)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-443783/258464)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (139023790/188939)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-2305084/425353)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24842764/213797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1199836943/866674)) (.idx (.var 0) 1)) (.add (.mul (.const (1619845/584147)) (.idx (.var 0) 2)) (.const (266029763/407891))))))))))) (.sub (.var 1) (.const 1))))

def f94 : Formula :=
  .atom .le tm6 (.const 0)

def f95 : Formula :=
  .and f90 f91

def sq8 : Sequent := ⟨f95, f89⟩

def tm7 : Term :=
  (.add (.mul (.const 100) tm4) (.const 0))

def f96 : Formula :=
  .and f0 f10

def sq9 : Sequent := ⟨f96, f89⟩

def f97 : Formula :=
  .and f0 f2

def sq10 : Sequent := ⟨f97, f89⟩

def tm8 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-81777215/865404)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19907631/767852)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-66443/148076)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-157723339/723139)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (357203052/362143)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-6825332/430139)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (88227629/993847)) (.idx (.var 0) 0)) (.add (.mul (.const (-915866787/494506)) (.idx (.var 0) 1)) (.add (.mul (.const (199860113/967500)) (.idx (.var 0) 2)) (.const (631688098/725509))))))))))) (.sub (.const 1) (.const 1))))

def f98 : Formula :=
  .atom .le tm8 (.const 0)

def sq11 : Sequent := ⟨f97, f98⟩

def sq12 : Sequent := ⟨f97, f0⟩

def sq13 : Sequent := ⟨f97, f97⟩

def tm9 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-81777215/865404)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19907631/767852)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-66443/148076)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-157723339/723139)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (357203052/362143)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-6825332/430139)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (88227629/993847)) (.idx (.var 0) 0)) (.add (.mul (.const (-915866787/494506)) (.idx (.var 0) 1)) (.add (.mul (.const (199860113/967500)) (.idx (.var 0) 2)) (.const (631688098/725509))))))))))) (.sub tm0 (.const 1))))

def f99 : Formula :=
  .atom .le tm9 (.const 0)

def sq14 : Sequent := ⟨f97, f99⟩

def sq15 : Sequent := ⟨f97, f2⟩

def tm10 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-81777215/865404)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19907631/767852)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-66443/148076)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-157723339/723139)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (357203052/362143)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-6825332/430139)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (88227629/993847)) (.idx (.var 0) 0)) (.add (.mul (.const (-915866787/494506)) (.idx (.var 0) 1)) (.add (.mul (.const (199860113/967500)) (.idx (.var 0) 2)) (.const (631688098/725509))))))))))) (.sub (.var 1) (.const 1))))

def f100 : Formula :=
  .atom .le tm10 (.const 0)

def f101 : Formula :=
  .and f97 f98

def sq16 : Sequent := ⟨f101, f89⟩

def tm11 : Term :=
  (.add (.mul (.const 100) tm8) (.const 0))

def f102 : Formula :=
  .and f0 f9

def sq17 : Sequent := ⟨f102, f89⟩

def f103 : Formula :=
  .and f0 f3

def sq18 : Sequent := ⟨f103, f89⟩

def tm12 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-31362509/424797)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2908768/759537)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-232625/728916)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (81158843/897295)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (613730647/672316)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (69701509/953625)) (.idx (.var 0) 0)) (.add (.mul (.const (-1514327825/855586)) (.idx (.var 0) 1)) (.add (.mul (.const (-15641879/174684)) (.idx (.var 0) 2)) (.const (453691192/528087))))))))))) (.sub (.const 1) (.const 1))))

def f104 : Formula :=
  .atom .le tm12 (.const 0)

def sq19 : Sequent := ⟨f103, f104⟩

def sq20 : Sequent := ⟨f103, f0⟩

def sq21 : Sequent := ⟨f103, f103⟩

def tm13 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-31362509/424797)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2908768/759537)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-232625/728916)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (81158843/897295)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (613730647/672316)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (69701509/953625)) (.idx (.var 0) 0)) (.add (.mul (.const (-1514327825/855586)) (.idx (.var 0) 1)) (.add (.mul (.const (-15641879/174684)) (.idx (.var 0) 2)) (.const (453691192/528087))))))))))) (.sub tm0 (.const 1))))

def f105 : Formula :=
  .atom .le tm13 (.const 0)

def sq22 : Sequent := ⟨f103, f105⟩

def sq23 : Sequent := ⟨f103, f3⟩

def tm14 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-31362509/424797)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2908768/759537)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-232625/728916)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (81158843/897295)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (613730647/672316)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (69701509/953625)) (.idx (.var 0) 0)) (.add (.mul (.const (-1514327825/855586)) (.idx (.var 0) 1)) (.add (.mul (.const (-15641879/174684)) (.idx (.var 0) 2)) (.const (453691192/528087))))))))))) (.sub (.var 1) (.const 1))))

def f106 : Formula :=
  .atom .le tm14 (.const 0)

def f107 : Formula :=
  .and f103 f104

def sq24 : Sequent := ⟨f107, f89⟩

def tm15 : Term :=
  (.add (.mul (.const 100) tm12) (.const 0))

def f108 : Formula :=
  .and f0 f8

def sq25 : Sequent := ⟨f108, f89⟩

def f109 : Formula :=
  .and f0 f4

def sq26 : Sequent := ⟨f109, f89⟩

def tm16 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-7714834/217979)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2914501/761034)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-291259/912642)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21961087/405691)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (568672020/436883)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7947287/226815)) (.idx (.var 0) 0)) (.add (.mul (.const (-1559096086/610471)) (.idx (.var 0) 1)) (.add (.mul (.const (18254081/340617)) (.idx (.var 0) 2)) (.const (238477656/190141))))))))))) (.sub (.const 1) (.const 1))))

def f110 : Formula :=
  .atom .le tm16 (.const 0)

def sq27 : Sequent := ⟨f109, f110⟩

def sq28 : Sequent := ⟨f109, f0⟩

def sq29 : Sequent := ⟨f109, f109⟩

def tm17 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-7714834/217979)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2914501/761034)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-291259/912642)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21961087/405691)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (568672020/436883)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7947287/226815)) (.idx (.var 0) 0)) (.add (.mul (.const (-1559096086/610471)) (.idx (.var 0) 1)) (.add (.mul (.const (18254081/340617)) (.idx (.var 0) 2)) (.const (238477656/190141))))))))))) (.sub tm0 (.const 1))))

def f111 : Formula :=
  .atom .le tm17 (.const 0)

def sq30 : Sequent := ⟨f109, f111⟩

def sq31 : Sequent := ⟨f109, f4⟩

def tm18 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-7714834/217979)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (2914501/761034)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-291259/912642)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21961087/405691)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (568672020/436883)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8020/437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7947287/226815)) (.idx (.var 0) 0)) (.add (.mul (.const (-1559096086/610471)) (.idx (.var 0) 1)) (.add (.mul (.const (18254081/340617)) (.idx (.var 0) 2)) (.const (238477656/190141))))))))))) (.sub (.var 1) (.const 1))))

def f112 : Formula :=
  .atom .le tm18 (.const 0)

def f113 : Formula :=
  .and f109 f110

def sq32 : Sequent := ⟨f113, f89⟩

def tm19 : Term :=
  (.add (.mul (.const 100) tm16) (.const 0))

def f114 : Formula :=
  .and f0 f7

def sq33 : Sequent := ⟨f114, f89⟩

def f115 : Formula :=
  .and f0 f5

def sq34 : Sequent := ⟨f115, f89⟩

def tm20 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-203399967/825238)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-35956217/961853)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13783535/790628)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (117728210/495019)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (488437147/495192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1010/77)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (85958423/373273)) (.idx (.var 0) 0)) (.add (.mul (.const (-1581400307/853849)) (.idx (.var 0) 1)) (.add (.mul (.const (-73342493/336505)) (.idx (.var 0) 2)) (.const (582385693/668884))))))))))) (.sub (.const 1) (.const 1))))

def f116 : Formula :=
  .atom .le tm20 (.const 0)

def sq35 : Sequent := ⟨f115, f116⟩

def sq36 : Sequent := ⟨f115, f0⟩

def sq37 : Sequent := ⟨f115, f115⟩

def tm21 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-203399967/825238)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-35956217/961853)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13783535/790628)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (117728210/495019)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (488437147/495192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1010/77)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (85958423/373273)) (.idx (.var 0) 0)) (.add (.mul (.const (-1581400307/853849)) (.idx (.var 0) 1)) (.add (.mul (.const (-73342493/336505)) (.idx (.var 0) 2)) (.const (582385693/668884))))))))))) (.sub tm0 (.const 1))))

def f117 : Formula :=
  .atom .le tm21 (.const 0)

def sq38 : Sequent := ⟨f115, f117⟩

def sq39 : Sequent := ⟨f115, f5⟩

def tm22 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-203399967/825238)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-35956217/961853)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13783535/790628)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (117728210/495019)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (488437147/495192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1010/77)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (85958423/373273)) (.idx (.var 0) 0)) (.add (.mul (.const (-1581400307/853849)) (.idx (.var 0) 1)) (.add (.mul (.const (-73342493/336505)) (.idx (.var 0) 2)) (.const (582385693/668884))))))))))) (.sub (.var 1) (.const 1))))

def f118 : Formula :=
  .atom .le tm22 (.const 0)

def f119 : Formula :=
  .and f115 f116

def sq40 : Sequent := ⟨f119, f89⟩

def tm23 : Term :=
  (.add (.mul (.const 100) tm20) (.const 0))

def f120 : Formula :=
  .and f0 f6

def sq41 : Sequent := ⟨f120, f89⟩

def tm24 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-36497653/780717)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (3816569/794980)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-125/417)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-54844955/280636)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (948350739/897431)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-26878859/923501)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (43246141/960562)) (.idx (.var 0) 0)) (.add (.mul (.const (-611535567/298939)) (.idx (.var 0) 1)) (.add (.mul (.const (156605533/786391)) (.idx (.var 0) 2)) (.const (387209579/390902))))))))))) (.sub (.const 1) (.const 1))))

def f121 : Formula :=
  .atom .le tm24 (.const 0)

def sq42 : Sequent := ⟨f120, f121⟩

def sq43 : Sequent := ⟨f120, f0⟩

def sq44 : Sequent := ⟨f120, f120⟩

def tm25 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-36497653/780717)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (3816569/794980)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-125/417)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-54844955/280636)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (948350739/897431)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-26878859/923501)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (43246141/960562)) (.idx (.var 0) 0)) (.add (.mul (.const (-611535567/298939)) (.idx (.var 0) 1)) (.add (.mul (.const (156605533/786391)) (.idx (.var 0) 2)) (.const (387209579/390902))))))))))) (.sub tm0 (.const 1))))

def f122 : Formula :=
  .atom .le tm25 (.const 0)

def sq45 : Sequent := ⟨f120, f122⟩

def sq46 : Sequent := ⟨f120, f6⟩

def tm26 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (1/100)))))) (.mul (.add (.mul (.const (-36497653/780717)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (3816569/794980)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-125/417)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-54844955/280636)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (948350739/897431)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-26878859/923501)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (43246141/960562)) (.idx (.var 0) 0)) (.add (.mul (.const (-611535567/298939)) (.idx (.var 0) 1)) (.add (.mul (.const (156605533/786391)) (.idx (.var 0) 2)) (.const (387209579/390902))))))))))) (.sub (.var 1) (.const 1))))

def f123 : Formula :=
  .atom .le tm26 (.const 0)

def f124 : Formula :=
  .and f120 f121

def sq47 : Sequent := ⟨f124, f89⟩

def tm27 : Term :=
  (.add (.mul (.const 100) tm24) (.const 0))

def tm28 : Term :=
  (.add (.mul (.const 400) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2000)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3))))))

def f125 : Formula :=
  .atom .le tm28 (.const 0)

def sq48 : Sequent := ⟨f85, f125⟩

def f126 : Formula :=
  .and f13 f14

def sq49 : Sequent := ⟨f126, f125⟩

def tm29 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 2) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 2) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 2) 2)) (.const (286392834/561017))))))))))) (.sub (.const 1) (.const 1))))

def f127 : Formula :=
  .atom .le tm29 (.const 0)

def sq50 : Sequent := ⟨f126, f127⟩

def sq51 : Sequent := ⟨f126, f13⟩

def sq52 : Sequent := ⟨f126, f126⟩

def tm30 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 2) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 2) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 2) 2)) (.const (286392834/561017))))))))))) (.sub tm1 (.const 1))))

def f128 : Formula :=
  .atom .le tm30 (.const 0)

def sq53 : Sequent := ⟨f126, f128⟩

def sq54 : Sequent := ⟨f126, f14⟩

def tm31 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 2) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 2) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 2) 2)) (.const (286392834/561017))))))))))) (.sub (.var 3) (.const 1))))

def f129 : Formula :=
  .atom .le tm31 (.const 0)

def f130 : Formula :=
  .and f126 f127

def sq55 : Sequent := ⟨f130, f125⟩

def tm32 : Term :=
  (.add (.mul (.const 1000) tm29) (.const 0))

def f131 : Formula :=
  .and f13 f83

def sq56 : Sequent := ⟨f131, f125⟩

def f132 : Formula :=
  .and f13 f15

def sq57 : Sequent := ⟨f132, f125⟩

def tm33 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 2) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 2) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 2) 2)) (.const (2632947191/910618))))))))))) (.sub (.const 1) (.const 1))))

def f133 : Formula :=
  .atom .le tm33 (.const 0)

def sq58 : Sequent := ⟨f132, f133⟩

def sq59 : Sequent := ⟨f132, f13⟩

def sq60 : Sequent := ⟨f132, f132⟩

def tm34 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 2) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 2) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 2) 2)) (.const (2632947191/910618))))))))))) (.sub tm1 (.const 1))))

def f134 : Formula :=
  .atom .le tm34 (.const 0)

def sq61 : Sequent := ⟨f132, f134⟩

def sq62 : Sequent := ⟨f132, f15⟩

def tm35 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 2) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 2) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 2) 2)) (.const (2632947191/910618))))))))))) (.sub (.var 3) (.const 1))))

def f135 : Formula :=
  .atom .le tm35 (.const 0)

def f136 : Formula :=
  .and f132 f133

def sq63 : Sequent := ⟨f136, f125⟩

def tm36 : Term :=
  (.add (.mul (.const 1000) tm33) (.const 0))

def f137 : Formula :=
  .and f13 f82

def sq64 : Sequent := ⟨f137, f125⟩

def f138 : Formula :=
  .and f13 f16

def sq65 : Sequent := ⟨f138, f125⟩

def tm37 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 2) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 2) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 2) 2)) (.const (39124772/32805)))))))))) (.sub (.const 1) (.const 1))))

def f139 : Formula :=
  .atom .le tm37 (.const 0)

def sq66 : Sequent := ⟨f138, f139⟩

def sq67 : Sequent := ⟨f138, f13⟩

def sq68 : Sequent := ⟨f138, f138⟩

def tm38 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 2) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 2) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 2) 2)) (.const (39124772/32805)))))))))) (.sub tm1 (.const 1))))

def f140 : Formula :=
  .atom .le tm38 (.const 0)

def sq69 : Sequent := ⟨f138, f140⟩

def sq70 : Sequent := ⟨f138, f16⟩

def tm39 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 2) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 2) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 2) 2)) (.const (39124772/32805)))))))))) (.sub (.var 3) (.const 1))))

def f141 : Formula :=
  .atom .le tm39 (.const 0)

def f142 : Formula :=
  .and f138 f139

def sq71 : Sequent := ⟨f142, f125⟩

def tm40 : Term :=
  (.add (.mul (.const 1000) tm37) (.const 0))

def f143 : Formula :=
  .and f13 f81

def sq72 : Sequent := ⟨f143, f125⟩

def f144 : Formula :=
  .and f13 f17

def sq73 : Sequent := ⟨f144, f125⟩

def tm41 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 2) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 2) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 2) 2)) (.const (-1947116053/493198))))))))))) (.sub (.const 1) (.const 1))))

def f145 : Formula :=
  .atom .le tm41 (.const 0)

def sq74 : Sequent := ⟨f144, f145⟩

def sq75 : Sequent := ⟨f144, f13⟩

def sq76 : Sequent := ⟨f144, f144⟩

def tm42 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 2) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 2) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 2) 2)) (.const (-1947116053/493198))))))))))) (.sub tm1 (.const 1))))

def f146 : Formula :=
  .atom .le tm42 (.const 0)

def sq77 : Sequent := ⟨f144, f146⟩

def sq78 : Sequent := ⟨f144, f17⟩

def tm43 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 2) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 2) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 2) 2)) (.const (-1947116053/493198))))))))))) (.sub (.var 3) (.const 1))))

def f147 : Formula :=
  .atom .le tm43 (.const 0)

def f148 : Formula :=
  .and f144 f145

def sq79 : Sequent := ⟨f148, f125⟩

def tm44 : Term :=
  (.add (.mul (.const 1000) tm41) (.const 0))

def f149 : Formula :=
  .and f13 f80

def sq80 : Sequent := ⟨f149, f125⟩

def f150 : Formula :=
  .and f13 f18

def sq81 : Sequent := ⟨f150, f125⟩

def tm45 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 2) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 2) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 2) 2)) (.const (1648777036/878707))))))))))) (.sub (.const 1) (.const 1))))

def f151 : Formula :=
  .atom .le tm45 (.const 0)

def sq82 : Sequent := ⟨f150, f151⟩

def sq83 : Sequent := ⟨f150, f13⟩

def sq84 : Sequent := ⟨f150, f150⟩

def tm46 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 2) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 2) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 2) 2)) (.const (1648777036/878707))))))))))) (.sub tm1 (.const 1))))

def f152 : Formula :=
  .atom .le tm46 (.const 0)

def sq85 : Sequent := ⟨f150, f152⟩

def sq86 : Sequent := ⟨f150, f18⟩

def tm47 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 2) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 2) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 2) 2)) (.const (1648777036/878707))))))))))) (.sub (.var 3) (.const 1))))

def f153 : Formula :=
  .atom .le tm47 (.const 0)

def f154 : Formula :=
  .and f150 f151

def sq87 : Sequent := ⟨f154, f125⟩

def tm48 : Term :=
  (.add (.mul (.const 1000) tm45) (.const 0))

def f155 : Formula :=
  .and f13 f79

def sq88 : Sequent := ⟨f155, f125⟩

def f156 : Formula :=
  .and f13 f19

def sq89 : Sequent := ⟨f156, f125⟩

def tm49 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 2) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 2) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 2) 2)) (.const (-312678635/79278))))))))))) (.sub (.const 1) (.const 1))))

def f157 : Formula :=
  .atom .le tm49 (.const 0)

def sq90 : Sequent := ⟨f156, f157⟩

def sq91 : Sequent := ⟨f156, f13⟩

def sq92 : Sequent := ⟨f156, f156⟩

def tm50 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 2) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 2) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 2) 2)) (.const (-312678635/79278))))))))))) (.sub tm1 (.const 1))))

def f158 : Formula :=
  .atom .le tm50 (.const 0)

def sq93 : Sequent := ⟨f156, f158⟩

def sq94 : Sequent := ⟨f156, f19⟩

def tm51 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 2) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 2) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 2) 2)) (.const (-312678635/79278))))))))))) (.sub (.var 3) (.const 1))))

def f159 : Formula :=
  .atom .le tm51 (.const 0)

def f160 : Formula :=
  .and f156 f157

def sq95 : Sequent := ⟨f160, f125⟩

def tm52 : Term :=
  (.add (.mul (.const 1000) tm49) (.const 0))

def f161 : Formula :=
  .and f13 f78

def sq96 : Sequent := ⟨f161, f125⟩

def f162 : Formula :=
  .and f13 f20

def sq97 : Sequent := ⟨f162, f125⟩

def tm53 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 2) 2)) (.const (-162864022755/580618))))))))))) (.sub (.const 1) (.const 1))))

def f163 : Formula :=
  .atom .le tm53 (.const 0)

def sq98 : Sequent := ⟨f162, f163⟩

def sq99 : Sequent := ⟨f162, f13⟩

def sq100 : Sequent := ⟨f162, f162⟩

def tm54 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 2) 2)) (.const (-162864022755/580618))))))))))) (.sub tm1 (.const 1))))

def f164 : Formula :=
  .atom .le tm54 (.const 0)

def sq101 : Sequent := ⟨f162, f164⟩

def sq102 : Sequent := ⟨f162, f20⟩

def tm55 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 2) 2)) (.const (-162864022755/580618))))))))))) (.sub (.var 3) (.const 1))))

def f165 : Formula :=
  .atom .le tm55 (.const 0)

def f166 : Formula :=
  .and f162 f163

def sq103 : Sequent := ⟨f166, f125⟩

def tm56 : Term :=
  (.add (.mul (.const 1000) tm53) (.const 0))

def f167 : Formula :=
  .and f13 f77

def sq104 : Sequent := ⟨f167, f125⟩

def f168 : Formula :=
  .and f13 f21

def sq105 : Sequent := ⟨f168, f125⟩

def tm57 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 2) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 2) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 2) 2)) (.const (32302115855/771688))))))))))) (.sub (.const 1) (.const 1))))

def f169 : Formula :=
  .atom .le tm57 (.const 0)

def sq106 : Sequent := ⟨f168, f169⟩

def sq107 : Sequent := ⟨f168, f13⟩

def sq108 : Sequent := ⟨f168, f168⟩

def tm58 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 2) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 2) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 2) 2)) (.const (32302115855/771688))))))))))) (.sub tm1 (.const 1))))

def f170 : Formula :=
  .atom .le tm58 (.const 0)

def sq109 : Sequent := ⟨f168, f170⟩

def sq110 : Sequent := ⟨f168, f21⟩

def tm59 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 2) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 2) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 2) 2)) (.const (32302115855/771688))))))))))) (.sub (.var 3) (.const 1))))

def f171 : Formula :=
  .atom .le tm59 (.const 0)

def f172 : Formula :=
  .and f168 f169

def sq111 : Sequent := ⟨f172, f125⟩

def tm60 : Term :=
  (.add (.mul (.const 1000) tm57) (.const 0))

def f173 : Formula :=
  .and f13 f76

def sq112 : Sequent := ⟨f173, f125⟩

def f174 : Formula :=
  .and f13 f22

def sq113 : Sequent := ⟨f174, f125⟩

def tm61 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 2) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 2) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 2) 2)) (.const (-2074194415/944191))))))))))) (.sub (.const 1) (.const 1))))

def f175 : Formula :=
  .atom .le tm61 (.const 0)

def sq114 : Sequent := ⟨f174, f175⟩

def sq115 : Sequent := ⟨f174, f13⟩

def sq116 : Sequent := ⟨f174, f174⟩

def tm62 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 2) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 2) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 2) 2)) (.const (-2074194415/944191))))))))))) (.sub tm1 (.const 1))))

def f176 : Formula :=
  .atom .le tm62 (.const 0)

def sq117 : Sequent := ⟨f174, f176⟩

def sq118 : Sequent := ⟨f174, f22⟩

def tm63 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 2) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 2) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 2) 2)) (.const (-2074194415/944191))))))))))) (.sub (.var 3) (.const 1))))

def f177 : Formula :=
  .atom .le tm63 (.const 0)

def f178 : Formula :=
  .and f174 f175

def sq119 : Sequent := ⟨f178, f125⟩

def tm64 : Term :=
  (.add (.mul (.const 1000) tm61) (.const 0))

def f179 : Formula :=
  .and f13 f75

def sq120 : Sequent := ⟨f179, f125⟩

def f180 : Formula :=
  .and f13 f23

def sq121 : Sequent := ⟨f180, f125⟩

def tm65 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 2) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 2) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 2) 2)) (.const (-461424968/955333))))))))))) (.sub (.const 1) (.const 1))))

def f181 : Formula :=
  .atom .le tm65 (.const 0)

def sq122 : Sequent := ⟨f180, f181⟩

def sq123 : Sequent := ⟨f180, f13⟩

def sq124 : Sequent := ⟨f180, f180⟩

def tm66 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 2) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 2) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 2) 2)) (.const (-461424968/955333))))))))))) (.sub tm1 (.const 1))))

def f182 : Formula :=
  .atom .le tm66 (.const 0)

def sq125 : Sequent := ⟨f180, f182⟩

def sq126 : Sequent := ⟨f180, f23⟩

def tm67 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 2) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 2) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 2) 2)) (.const (-461424968/955333))))))))))) (.sub (.var 3) (.const 1))))

def f183 : Formula :=
  .atom .le tm67 (.const 0)

def f184 : Formula :=
  .and f180 f181

def sq127 : Sequent := ⟨f184, f125⟩

def tm68 : Term :=
  (.add (.mul (.const 1000) tm65) (.const 0))

def f185 : Formula :=
  .and f13 f74

def sq128 : Sequent := ⟨f185, f125⟩

def f186 : Formula :=
  .and f13 f24

def sq129 : Sequent := ⟨f186, f125⟩

def tm69 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 2) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 2) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 2) 2)) (.const (5893227809/74342))))))))))) (.sub (.const 1) (.const 1))))

def f187 : Formula :=
  .atom .le tm69 (.const 0)

def sq130 : Sequent := ⟨f186, f187⟩

def sq131 : Sequent := ⟨f186, f13⟩

def sq132 : Sequent := ⟨f186, f186⟩

def tm70 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 2) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 2) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 2) 2)) (.const (5893227809/74342))))))))))) (.sub tm1 (.const 1))))

def f188 : Formula :=
  .atom .le tm70 (.const 0)

def sq133 : Sequent := ⟨f186, f188⟩

def sq134 : Sequent := ⟨f186, f24⟩

def tm71 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 2) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 2) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 2) 2)) (.const (5893227809/74342))))))))))) (.sub (.var 3) (.const 1))))

def f189 : Formula :=
  .atom .le tm71 (.const 0)

def f190 : Formula :=
  .and f186 f187

def sq135 : Sequent := ⟨f190, f125⟩

def tm72 : Term :=
  (.add (.mul (.const 1000) tm69) (.const 0))

def f191 : Formula :=
  .and f13 f73

def sq136 : Sequent := ⟨f191, f125⟩

def f192 : Formula :=
  .and f13 f25

def sq137 : Sequent := ⟨f192, f125⟩

def tm73 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 2) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 2) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 2) 2)) (.const (-1217853940/374393))))))))))) (.sub (.const 1) (.const 1))))

def f193 : Formula :=
  .atom .le tm73 (.const 0)

def sq138 : Sequent := ⟨f192, f193⟩

def sq139 : Sequent := ⟨f192, f13⟩

def sq140 : Sequent := ⟨f192, f192⟩

def tm74 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 2) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 2) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 2) 2)) (.const (-1217853940/374393))))))))))) (.sub tm1 (.const 1))))

def f194 : Formula :=
  .atom .le tm74 (.const 0)

def sq141 : Sequent := ⟨f192, f194⟩

def sq142 : Sequent := ⟨f192, f25⟩

def tm75 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 2) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 2) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 2) 2)) (.const (-1217853940/374393))))))))))) (.sub (.var 3) (.const 1))))

def f195 : Formula :=
  .atom .le tm75 (.const 0)

def f196 : Formula :=
  .and f192 f193

def sq143 : Sequent := ⟨f196, f125⟩

def tm76 : Term :=
  (.add (.mul (.const 1000) tm73) (.const 0))

def f197 : Formula :=
  .and f13 f72

def sq144 : Sequent := ⟨f197, f125⟩

def f198 : Formula :=
  .and f13 f26

def sq145 : Sequent := ⟨f198, f125⟩

def tm77 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 2) 2)) (.const (-497948639335/999993))))))))))) (.sub (.const 1) (.const 1))))

def f199 : Formula :=
  .atom .le tm77 (.const 0)

def sq146 : Sequent := ⟨f198, f199⟩

def sq147 : Sequent := ⟨f198, f13⟩

def sq148 : Sequent := ⟨f198, f198⟩

def tm78 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 2) 2)) (.const (-497948639335/999993))))))))))) (.sub tm1 (.const 1))))

def f200 : Formula :=
  .atom .le tm78 (.const 0)

def sq149 : Sequent := ⟨f198, f200⟩

def sq150 : Sequent := ⟨f198, f26⟩

def tm79 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 2) 2)) (.const (-497948639335/999993))))))))))) (.sub (.var 3) (.const 1))))

def f201 : Formula :=
  .atom .le tm79 (.const 0)

def f202 : Formula :=
  .and f198 f199

def sq151 : Sequent := ⟨f202, f125⟩

def tm80 : Term :=
  (.add (.mul (.const 1000) tm77) (.const 0))

def f203 : Formula :=
  .and f13 f71

def sq152 : Sequent := ⟨f203, f125⟩

def f204 : Formula :=
  .and f13 f27

def sq153 : Sequent := ⟨f204, f125⟩

def tm81 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 2) 2)) (.const (109417491763/283391))))))))))) (.sub (.const 1) (.const 1))))

def f205 : Formula :=
  .atom .le tm81 (.const 0)

def sq154 : Sequent := ⟨f204, f205⟩

def sq155 : Sequent := ⟨f204, f13⟩

def sq156 : Sequent := ⟨f204, f204⟩

def tm82 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 2) 2)) (.const (109417491763/283391))))))))))) (.sub tm1 (.const 1))))

def f206 : Formula :=
  .atom .le tm82 (.const 0)

def sq157 : Sequent := ⟨f204, f206⟩

def sq158 : Sequent := ⟨f204, f27⟩

def tm83 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 2) 2)) (.const (109417491763/283391))))))))))) (.sub (.var 3) (.const 1))))

def f207 : Formula :=
  .atom .le tm83 (.const 0)

def f208 : Formula :=
  .and f204 f205

def sq159 : Sequent := ⟨f208, f125⟩

def tm84 : Term :=
  (.add (.mul (.const 1000) tm81) (.const 0))

def f209 : Formula :=
  .and f13 f70

def sq160 : Sequent := ⟨f209, f125⟩

def f210 : Formula :=
  .and f13 f28

def sq161 : Sequent := ⟨f210, f125⟩

def tm85 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 2) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 2) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 2) 2)) (.const (-219037863/39608))))))))))) (.sub (.const 1) (.const 1))))

def f211 : Formula :=
  .atom .le tm85 (.const 0)

def sq162 : Sequent := ⟨f210, f211⟩

def sq163 : Sequent := ⟨f210, f13⟩

def sq164 : Sequent := ⟨f210, f210⟩

def tm86 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 2) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 2) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 2) 2)) (.const (-219037863/39608))))))))))) (.sub tm1 (.const 1))))

def f212 : Formula :=
  .atom .le tm86 (.const 0)

def sq165 : Sequent := ⟨f210, f212⟩

def sq166 : Sequent := ⟨f210, f28⟩

def tm87 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 2) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 2) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 2) 2)) (.const (-219037863/39608))))))))))) (.sub (.var 3) (.const 1))))

def f213 : Formula :=
  .atom .le tm87 (.const 0)

def f214 : Formula :=
  .and f210 f211

def sq167 : Sequent := ⟨f214, f125⟩

def tm88 : Term :=
  (.add (.mul (.const 1000) tm85) (.const 0))

def f215 : Formula :=
  .and f13 f69

def sq168 : Sequent := ⟨f215, f125⟩

def f216 : Formula :=
  .and f13 f29

def sq169 : Sequent := ⟨f216, f125⟩

def tm89 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 2) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 2) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 2) 2)) (.const (-111292627/64735))))))))))) (.sub (.const 1) (.const 1))))

def f217 : Formula :=
  .atom .le tm89 (.const 0)

def sq170 : Sequent := ⟨f216, f217⟩

def sq171 : Sequent := ⟨f216, f13⟩

def sq172 : Sequent := ⟨f216, f216⟩

def tm90 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 2) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 2) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 2) 2)) (.const (-111292627/64735))))))))))) (.sub tm1 (.const 1))))

def f218 : Formula :=
  .atom .le tm90 (.const 0)

def sq173 : Sequent := ⟨f216, f218⟩

def sq174 : Sequent := ⟨f216, f29⟩

def tm91 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 2) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 2) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 2) 2)) (.const (-111292627/64735))))))))))) (.sub (.var 3) (.const 1))))

def f219 : Formula :=
  .atom .le tm91 (.const 0)

def f220 : Formula :=
  .and f216 f217

def sq175 : Sequent := ⟨f220, f125⟩

def tm92 : Term :=
  (.add (.mul (.const 1000) tm89) (.const 0))

def f221 : Formula :=
  .and f13 f68

def sq176 : Sequent := ⟨f221, f125⟩

def f222 : Formula :=
  .and f13 f30

def sq177 : Sequent := ⟨f222, f125⟩

def tm93 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 2) 2)) (.const (513148022210/919633))))))))))) (.sub (.const 1) (.const 1))))

def f223 : Formula :=
  .atom .le tm93 (.const 0)

def sq178 : Sequent := ⟨f222, f223⟩

def sq179 : Sequent := ⟨f222, f13⟩

def sq180 : Sequent := ⟨f222, f222⟩

def tm94 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 2) 2)) (.const (513148022210/919633))))))))))) (.sub tm1 (.const 1))))

def f224 : Formula :=
  .atom .le tm94 (.const 0)

def sq181 : Sequent := ⟨f222, f224⟩

def sq182 : Sequent := ⟨f222, f30⟩

def tm95 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 2) 2)) (.const (513148022210/919633))))))))))) (.sub (.var 3) (.const 1))))

def f225 : Formula :=
  .atom .le tm95 (.const 0)

def f226 : Formula :=
  .and f222 f223

def sq183 : Sequent := ⟨f226, f125⟩

def tm96 : Term :=
  (.add (.mul (.const 1000) tm93) (.const 0))

def f227 : Formula :=
  .and f13 f67

def sq184 : Sequent := ⟨f227, f125⟩

def f228 : Formula :=
  .and f13 f31

def sq185 : Sequent := ⟨f228, f125⟩

def tm97 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 2) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 2) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 2) 2)) (.const (-587540059/765919))))))))))) (.sub (.const 1) (.const 1))))

def f229 : Formula :=
  .atom .le tm97 (.const 0)

def sq186 : Sequent := ⟨f228, f229⟩

def sq187 : Sequent := ⟨f228, f13⟩

def sq188 : Sequent := ⟨f228, f228⟩

def tm98 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 2) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 2) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 2) 2)) (.const (-587540059/765919))))))))))) (.sub tm1 (.const 1))))

def f230 : Formula :=
  .atom .le tm98 (.const 0)

def sq189 : Sequent := ⟨f228, f230⟩

def sq190 : Sequent := ⟨f228, f31⟩

def tm99 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 2) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 2) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 2) 2)) (.const (-587540059/765919))))))))))) (.sub (.var 3) (.const 1))))

def f231 : Formula :=
  .atom .le tm99 (.const 0)

def f232 : Formula :=
  .and f228 f229

def sq191 : Sequent := ⟨f232, f125⟩

def tm100 : Term :=
  (.add (.mul (.const 1000) tm97) (.const 0))

def f233 : Formula :=
  .and f13 f66

def sq192 : Sequent := ⟨f233, f125⟩

def f234 : Formula :=
  .and f13 f32

def sq193 : Sequent := ⟨f234, f125⟩

def tm101 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 2) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 2) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 2) 2)) (.const (-592173234/574199))))))))))) (.sub (.const 1) (.const 1))))

def f235 : Formula :=
  .atom .le tm101 (.const 0)

def sq194 : Sequent := ⟨f234, f235⟩

def sq195 : Sequent := ⟨f234, f13⟩

def sq196 : Sequent := ⟨f234, f234⟩

def tm102 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 2) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 2) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 2) 2)) (.const (-592173234/574199))))))))))) (.sub tm1 (.const 1))))

def f236 : Formula :=
  .atom .le tm102 (.const 0)

def sq197 : Sequent := ⟨f234, f236⟩

def sq198 : Sequent := ⟨f234, f32⟩

def tm103 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 2) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 2) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 2) 2)) (.const (-592173234/574199))))))))))) (.sub (.var 3) (.const 1))))

def f237 : Formula :=
  .atom .le tm103 (.const 0)

def f238 : Formula :=
  .and f234 f235

def sq199 : Sequent := ⟨f238, f125⟩

def tm104 : Term :=
  (.add (.mul (.const 1000) tm101) (.const 0))

def f239 : Formula :=
  .and f13 f65

def sq200 : Sequent := ⟨f239, f125⟩

def f240 : Formula :=
  .and f13 f33

def sq201 : Sequent := ⟨f240, f125⟩

def tm105 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 2) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 2) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 2) 2)) (.const (332709852/494053))))))))))) (.sub (.const 1) (.const 1))))

def f241 : Formula :=
  .atom .le tm105 (.const 0)

def sq202 : Sequent := ⟨f240, f241⟩

def sq203 : Sequent := ⟨f240, f13⟩

def sq204 : Sequent := ⟨f240, f240⟩

def tm106 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 2) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 2) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 2) 2)) (.const (332709852/494053))))))))))) (.sub tm1 (.const 1))))

def f242 : Formula :=
  .atom .le tm106 (.const 0)

def sq205 : Sequent := ⟨f240, f242⟩

def sq206 : Sequent := ⟨f240, f33⟩

def tm107 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 2) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 2) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 2) 2)) (.const (332709852/494053))))))))))) (.sub (.var 3) (.const 1))))

def f243 : Formula :=
  .atom .le tm107 (.const 0)

def f244 : Formula :=
  .and f240 f241

def sq207 : Sequent := ⟨f244, f125⟩

def tm108 : Term :=
  (.add (.mul (.const 1000) tm105) (.const 0))

def f245 : Formula :=
  .and f13 f64

def sq208 : Sequent := ⟨f245, f125⟩

def f246 : Formula :=
  .and f13 f34

def sq209 : Sequent := ⟨f246, f125⟩

def tm109 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 2) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 2) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 2) 2)) (.const (138427371/316640))))))))))) (.sub (.const 1) (.const 1))))

def f247 : Formula :=
  .atom .le tm109 (.const 0)

def sq210 : Sequent := ⟨f246, f247⟩

def sq211 : Sequent := ⟨f246, f13⟩

def sq212 : Sequent := ⟨f246, f246⟩

def tm110 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 2) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 2) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 2) 2)) (.const (138427371/316640))))))))))) (.sub tm1 (.const 1))))

def f248 : Formula :=
  .atom .le tm110 (.const 0)

def sq213 : Sequent := ⟨f246, f248⟩

def sq214 : Sequent := ⟨f246, f34⟩

def tm111 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 2) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 2) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 2) 2)) (.const (138427371/316640))))))))))) (.sub (.var 3) (.const 1))))

def f249 : Formula :=
  .atom .le tm111 (.const 0)

def f250 : Formula :=
  .and f246 f247

def sq215 : Sequent := ⟨f250, f125⟩

def tm112 : Term :=
  (.add (.mul (.const 1000) tm109) (.const 0))

def f251 : Formula :=
  .and f13 f63

def sq216 : Sequent := ⟨f251, f125⟩

def f252 : Formula :=
  .and f13 f35

def sq217 : Sequent := ⟨f252, f125⟩

def tm113 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 2) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 2) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 2) 2)) (.const (-1126746000/347443))))))))))) (.sub (.const 1) (.const 1))))

def f253 : Formula :=
  .atom .le tm113 (.const 0)

def sq218 : Sequent := ⟨f252, f253⟩

def sq219 : Sequent := ⟨f252, f13⟩

def sq220 : Sequent := ⟨f252, f252⟩

def tm114 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 2) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 2) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 2) 2)) (.const (-1126746000/347443))))))))))) (.sub tm1 (.const 1))))

def f254 : Formula :=
  .atom .le tm114 (.const 0)

def sq221 : Sequent := ⟨f252, f254⟩

def sq222 : Sequent := ⟨f252, f35⟩

def tm115 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 2) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 2) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 2) 2)) (.const (-1126746000/347443))))))))))) (.sub (.var 3) (.const 1))))

def f255 : Formula :=
  .atom .le tm115 (.const 0)

def f256 : Formula :=
  .and f252 f253

def sq223 : Sequent := ⟨f256, f125⟩

def tm116 : Term :=
  (.add (.mul (.const 1000) tm113) (.const 0))

def f257 : Formula :=
  .and f13 f62

def sq224 : Sequent := ⟨f257, f125⟩

def f258 : Formula :=
  .and f13 f36

def sq225 : Sequent := ⟨f258, f125⟩

def tm117 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 2) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 2) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 2) 2)) (.const (292336317/533944))))))))))) (.sub (.const 1) (.const 1))))

def f259 : Formula :=
  .atom .le tm117 (.const 0)

def sq226 : Sequent := ⟨f258, f259⟩

def sq227 : Sequent := ⟨f258, f13⟩

def sq228 : Sequent := ⟨f258, f258⟩

def tm118 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 2) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 2) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 2) 2)) (.const (292336317/533944))))))))))) (.sub tm1 (.const 1))))

def f260 : Formula :=
  .atom .le tm118 (.const 0)

def sq229 : Sequent := ⟨f258, f260⟩

def sq230 : Sequent := ⟨f258, f36⟩

def tm119 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 2) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 2) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 2) 2)) (.const (292336317/533944))))))))))) (.sub (.var 3) (.const 1))))

def f261 : Formula :=
  .atom .le tm119 (.const 0)

def f262 : Formula :=
  .and f258 f259

def sq231 : Sequent := ⟨f262, f125⟩

def tm120 : Term :=
  (.add (.mul (.const 1000) tm117) (.const 0))

def f263 : Formula :=
  .and f13 f61

def sq232 : Sequent := ⟨f263, f125⟩

def f264 : Formula :=
  .and f13 f37

def sq233 : Sequent := ⟨f264, f125⟩

def tm121 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 2) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 2) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 2) 2)) (.const (-275632/241))))))))))) (.sub (.const 1) (.const 1))))

def f265 : Formula :=
  .atom .le tm121 (.const 0)

def sq234 : Sequent := ⟨f264, f265⟩

def sq235 : Sequent := ⟨f264, f13⟩

def sq236 : Sequent := ⟨f264, f264⟩

def tm122 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 2) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 2) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 2) 2)) (.const (-275632/241))))))))))) (.sub tm1 (.const 1))))

def f266 : Formula :=
  .atom .le tm122 (.const 0)

def sq237 : Sequent := ⟨f264, f266⟩

def sq238 : Sequent := ⟨f264, f37⟩

def tm123 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 2) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 2) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 2) 2)) (.const (-275632/241))))))))))) (.sub (.var 3) (.const 1))))

def f267 : Formula :=
  .atom .le tm123 (.const 0)

def f268 : Formula :=
  .and f264 f265

def sq239 : Sequent := ⟨f268, f125⟩

def tm124 : Term :=
  (.add (.mul (.const 1000) tm121) (.const 0))

def f269 : Formula :=
  .and f13 f60

def sq240 : Sequent := ⟨f269, f125⟩

def f270 : Formula :=
  .and f13 f38

def sq241 : Sequent := ⟨f270, f125⟩

def tm125 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 2) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 2) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 2) 2)) (.const (139581067/49924))))))))))) (.sub (.const 1) (.const 1))))

def f271 : Formula :=
  .atom .le tm125 (.const 0)

def sq242 : Sequent := ⟨f270, f271⟩

def sq243 : Sequent := ⟨f270, f13⟩

def sq244 : Sequent := ⟨f270, f270⟩

def tm126 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 2) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 2) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 2) 2)) (.const (139581067/49924))))))))))) (.sub tm1 (.const 1))))

def f272 : Formula :=
  .atom .le tm126 (.const 0)

def sq245 : Sequent := ⟨f270, f272⟩

def sq246 : Sequent := ⟨f270, f38⟩

def tm127 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 2) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 2) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 2) 2)) (.const (139581067/49924))))))))))) (.sub (.var 3) (.const 1))))

def f273 : Formula :=
  .atom .le tm127 (.const 0)

def f274 : Formula :=
  .and f270 f271

def sq247 : Sequent := ⟨f274, f125⟩

def tm128 : Term :=
  (.add (.mul (.const 1000) tm125) (.const 0))

def f275 : Formula :=
  .and f13 f59

def sq248 : Sequent := ⟨f275, f125⟩

def f276 : Formula :=
  .and f13 f39

def sq249 : Sequent := ⟨f276, f125⟩

def tm129 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 2) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 2) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 2) 2)) (.const (-57714997/273133))))))))))) (.sub (.const 1) (.const 1))))

def f277 : Formula :=
  .atom .le tm129 (.const 0)

def sq250 : Sequent := ⟨f276, f277⟩

def sq251 : Sequent := ⟨f276, f13⟩

def sq252 : Sequent := ⟨f276, f276⟩

def tm130 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 2) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 2) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 2) 2)) (.const (-57714997/273133))))))))))) (.sub tm1 (.const 1))))

def f278 : Formula :=
  .atom .le tm130 (.const 0)

def sq253 : Sequent := ⟨f276, f278⟩

def sq254 : Sequent := ⟨f276, f39⟩

def tm131 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 2) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 2) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 2) 2)) (.const (-57714997/273133))))))))))) (.sub (.var 3) (.const 1))))

def f279 : Formula :=
  .atom .le tm131 (.const 0)

def f280 : Formula :=
  .and f276 f277

def sq255 : Sequent := ⟨f280, f125⟩

def tm132 : Term :=
  (.add (.mul (.const 1000) tm129) (.const 0))

def f281 : Formula :=
  .and f13 f58

def sq256 : Sequent := ⟨f281, f125⟩

def f282 : Formula :=
  .and f13 f40

def sq257 : Sequent := ⟨f282, f125⟩

def tm133 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 2) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 2) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 2) 2)) (.const (384107719/929334))))))))))) (.sub (.const 1) (.const 1))))

def f283 : Formula :=
  .atom .le tm133 (.const 0)

def sq258 : Sequent := ⟨f282, f283⟩

def sq259 : Sequent := ⟨f282, f13⟩

def sq260 : Sequent := ⟨f282, f282⟩

def tm134 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 2) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 2) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 2) 2)) (.const (384107719/929334))))))))))) (.sub tm1 (.const 1))))

def f284 : Formula :=
  .atom .le tm134 (.const 0)

def sq261 : Sequent := ⟨f282, f284⟩

def sq262 : Sequent := ⟨f282, f40⟩

def tm135 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 2) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 2) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 2) 2)) (.const (384107719/929334))))))))))) (.sub (.var 3) (.const 1))))

def f285 : Formula :=
  .atom .le tm135 (.const 0)

def f286 : Formula :=
  .and f282 f283

def sq263 : Sequent := ⟨f286, f125⟩

def tm136 : Term :=
  (.add (.mul (.const 1000) tm133) (.const 0))

def f287 : Formula :=
  .and f13 f57

def sq264 : Sequent := ⟨f287, f125⟩

def f288 : Formula :=
  .and f13 f41

def sq265 : Sequent := ⟨f288, f125⟩

def tm137 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 2) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 2) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 2) 2)) (.const (-4049311051/930046))))))))))) (.sub (.const 1) (.const 1))))

def f289 : Formula :=
  .atom .le tm137 (.const 0)

def sq266 : Sequent := ⟨f288, f289⟩

def sq267 : Sequent := ⟨f288, f13⟩

def sq268 : Sequent := ⟨f288, f288⟩

def tm138 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 2) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 2) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 2) 2)) (.const (-4049311051/930046))))))))))) (.sub tm1 (.const 1))))

def f290 : Formula :=
  .atom .le tm138 (.const 0)

def sq269 : Sequent := ⟨f288, f290⟩

def sq270 : Sequent := ⟨f288, f41⟩

def tm139 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 2) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 2) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 2) 2)) (.const (-4049311051/930046))))))))))) (.sub (.var 3) (.const 1))))

def f291 : Formula :=
  .atom .le tm139 (.const 0)

def f292 : Formula :=
  .and f288 f289

def sq271 : Sequent := ⟨f292, f125⟩

def tm140 : Term :=
  (.add (.mul (.const 1000) tm137) (.const 0))

def f293 : Formula :=
  .and f13 f56

def sq272 : Sequent := ⟨f293, f125⟩

def f294 : Formula :=
  .and f13 f42

def sq273 : Sequent := ⟨f294, f125⟩

def tm141 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 2) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 2) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 2) 2)) (.const (189449415/537218))))))))))) (.sub (.const 1) (.const 1))))

def f295 : Formula :=
  .atom .le tm141 (.const 0)

def sq274 : Sequent := ⟨f294, f295⟩

def sq275 : Sequent := ⟨f294, f13⟩

def sq276 : Sequent := ⟨f294, f294⟩

def tm142 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 2) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 2) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 2) 2)) (.const (189449415/537218))))))))))) (.sub tm1 (.const 1))))

def f296 : Formula :=
  .atom .le tm142 (.const 0)

def sq277 : Sequent := ⟨f294, f296⟩

def sq278 : Sequent := ⟨f294, f42⟩

def tm143 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 2) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 2) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 2) 2)) (.const (189449415/537218))))))))))) (.sub (.var 3) (.const 1))))

def f297 : Formula :=
  .atom .le tm143 (.const 0)

def f298 : Formula :=
  .and f294 f295

def sq279 : Sequent := ⟨f298, f125⟩

def tm144 : Term :=
  (.add (.mul (.const 1000) tm141) (.const 0))

def f299 : Formula :=
  .and f13 f55

def sq280 : Sequent := ⟨f299, f125⟩

def f300 : Formula :=
  .and f13 f43

def sq281 : Sequent := ⟨f300, f125⟩

def tm145 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 2) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 2) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 2) 2)) (.const (-37780291/39382))))))))))) (.sub (.const 1) (.const 1))))

def f301 : Formula :=
  .atom .le tm145 (.const 0)

def sq282 : Sequent := ⟨f300, f301⟩

def sq283 : Sequent := ⟨f300, f13⟩

def sq284 : Sequent := ⟨f300, f300⟩

def tm146 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 2) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 2) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 2) 2)) (.const (-37780291/39382))))))))))) (.sub tm1 (.const 1))))

def f302 : Formula :=
  .atom .le tm146 (.const 0)

def sq285 : Sequent := ⟨f300, f302⟩

def sq286 : Sequent := ⟨f300, f43⟩

def tm147 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 2) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 2) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 2) 2)) (.const (-37780291/39382))))))))))) (.sub (.var 3) (.const 1))))

def f303 : Formula :=
  .atom .le tm147 (.const 0)

def f304 : Formula :=
  .and f300 f301

def sq287 : Sequent := ⟨f304, f125⟩

def tm148 : Term :=
  (.add (.mul (.const 1000) tm145) (.const 0))

def f305 : Formula :=
  .and f13 f54

def sq288 : Sequent := ⟨f305, f125⟩

def f306 : Formula :=
  .and f13 f44

def sq289 : Sequent := ⟨f306, f125⟩

def tm149 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 2) 2)) (.const (-466647799287/897298))))))))))) (.sub (.const 1) (.const 1))))

def f307 : Formula :=
  .atom .le tm149 (.const 0)

def sq290 : Sequent := ⟨f306, f307⟩

def sq291 : Sequent := ⟨f306, f13⟩

def sq292 : Sequent := ⟨f306, f306⟩

def tm150 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 2) 2)) (.const (-466647799287/897298))))))))))) (.sub tm1 (.const 1))))

def f308 : Formula :=
  .atom .le tm150 (.const 0)

def sq293 : Sequent := ⟨f306, f308⟩

def sq294 : Sequent := ⟨f306, f44⟩

def tm151 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 2) 2)) (.const (-466647799287/897298))))))))))) (.sub (.var 3) (.const 1))))

def f309 : Formula :=
  .atom .le tm151 (.const 0)

def f310 : Formula :=
  .and f306 f307

def sq295 : Sequent := ⟨f310, f125⟩

def tm152 : Term :=
  (.add (.mul (.const 1000) tm149) (.const 0))

def f311 : Formula :=
  .and f13 f53

def sq296 : Sequent := ⟨f311, f125⟩

def f312 : Formula :=
  .and f13 f45

def sq297 : Sequent := ⟨f312, f125⟩

def tm153 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 2) 2)) (.const (270563078873/702104))))))))))) (.sub (.const 1) (.const 1))))

def f313 : Formula :=
  .atom .le tm153 (.const 0)

def sq298 : Sequent := ⟨f312, f313⟩

def sq299 : Sequent := ⟨f312, f13⟩

def sq300 : Sequent := ⟨f312, f312⟩

def tm154 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 2) 2)) (.const (270563078873/702104))))))))))) (.sub tm1 (.const 1))))

def f314 : Formula :=
  .atom .le tm154 (.const 0)

def sq301 : Sequent := ⟨f312, f314⟩

def sq302 : Sequent := ⟨f312, f45⟩

def tm155 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 2) 2)) (.const (270563078873/702104))))))))))) (.sub (.var 3) (.const 1))))

def f315 : Formula :=
  .atom .le tm155 (.const 0)

def f316 : Formula :=
  .and f312 f313

def sq303 : Sequent := ⟨f316, f125⟩

def tm156 : Term :=
  (.add (.mul (.const 1000) tm153) (.const 0))

def f317 : Formula :=
  .and f13 f52

def sq304 : Sequent := ⟨f317, f125⟩

def f318 : Formula :=
  .and f13 f46

def sq305 : Sequent := ⟨f318, f125⟩

def tm157 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 2) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 2) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 2) 2)) (.const (-12867726179/978289))))))))))) (.sub (.const 1) (.const 1))))

def f319 : Formula :=
  .atom .le tm157 (.const 0)

def sq306 : Sequent := ⟨f318, f319⟩

def sq307 : Sequent := ⟨f318, f13⟩

def sq308 : Sequent := ⟨f318, f318⟩

def tm158 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 2) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 2) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 2) 2)) (.const (-12867726179/978289))))))))))) (.sub tm1 (.const 1))))

def f320 : Formula :=
  .atom .le tm158 (.const 0)

def sq309 : Sequent := ⟨f318, f320⟩

def sq310 : Sequent := ⟨f318, f46⟩

def tm159 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 2) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 2) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 2) 2)) (.const (-12867726179/978289))))))))))) (.sub (.var 3) (.const 1))))

def f321 : Formula :=
  .atom .le tm159 (.const 0)

def f322 : Formula :=
  .and f318 f319

def sq311 : Sequent := ⟨f322, f125⟩

def tm160 : Term :=
  (.add (.mul (.const 1000) tm157) (.const 0))

def f323 : Formula :=
  .and f13 f51

def sq312 : Sequent := ⟨f323, f125⟩

def f324 : Formula :=
  .and f13 f47

def sq313 : Sequent := ⟨f324, f125⟩

def tm161 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 2) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 2) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 2) 2)) (.const (3744383/435))))))))))) (.sub (.const 1) (.const 1))))

def f325 : Formula :=
  .atom .le tm161 (.const 0)

def sq314 : Sequent := ⟨f324, f325⟩

def sq315 : Sequent := ⟨f324, f13⟩

def sq316 : Sequent := ⟨f324, f324⟩

def tm162 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 2) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 2) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 2) 2)) (.const (3744383/435))))))))))) (.sub tm1 (.const 1))))

def f326 : Formula :=
  .atom .le tm162 (.const 0)

def sq317 : Sequent := ⟨f324, f326⟩

def sq318 : Sequent := ⟨f324, f47⟩

def tm163 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 2) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 2) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 2) 2)) (.const (3744383/435))))))))))) (.sub (.var 3) (.const 1))))

def f327 : Formula :=
  .atom .le tm163 (.const 0)

def f328 : Formula :=
  .and f324 f325

def sq319 : Sequent := ⟨f328, f125⟩

def tm164 : Term :=
  (.add (.mul (.const 1000) tm161) (.const 0))

def f329 : Formula :=
  .and f13 f50

def sq320 : Sequent := ⟨f329, f125⟩

def f330 : Formula :=
  .and f13 f48

def sq321 : Sequent := ⟨f330, f125⟩

def tm165 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 2) 2)) (.const (-225258249609/586834))))))))))) (.sub (.const 1) (.const 1))))

def f331 : Formula :=
  .atom .le tm165 (.const 0)

def sq322 : Sequent := ⟨f330, f331⟩

def sq323 : Sequent := ⟨f330, f13⟩

def sq324 : Sequent := ⟨f330, f330⟩

def tm166 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 2) 2)) (.const (-225258249609/586834))))))))))) (.sub tm1 (.const 1))))

def f332 : Formula :=
  .atom .le tm166 (.const 0)

def sq325 : Sequent := ⟨f330, f332⟩

def sq326 : Sequent := ⟨f330, f48⟩

def tm167 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 2) 2)) (.const (-225258249609/586834))))))))))) (.sub (.var 3) (.const 1))))

def f333 : Formula :=
  .atom .le tm167 (.const 0)

def f334 : Formula :=
  .and f330 f331

def sq327 : Sequent := ⟨f334, f125⟩

def tm168 : Term :=
  (.add (.mul (.const 1000) tm165) (.const 0))

def f335 : Formula :=
  .and f13 f49

def sq328 : Sequent := ⟨f335, f125⟩

def tm169 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 2) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 2) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 2) 2)) (.const (-3575003239/942719))))))))))) (.sub (.const 1) (.const 1))))

def f336 : Formula :=
  .atom .le tm169 (.const 0)

def sq329 : Sequent := ⟨f335, f336⟩

def sq330 : Sequent := ⟨f335, f13⟩

def sq331 : Sequent := ⟨f335, f335⟩

def tm170 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 2) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 2) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 2) 2)) (.const (-3575003239/942719))))))))))) (.sub tm1 (.const 1))))

def f337 : Formula :=
  .atom .le tm170 (.const 0)

def sq332 : Sequent := ⟨f335, f337⟩

def sq333 : Sequent := ⟨f335, f49⟩

def tm171 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 2) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 2) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 2) 2)) (.const (-3575003239/942719))))))))))) (.sub (.var 3) (.const 1))))

def f338 : Formula :=
  .atom .le tm171 (.const 0)

def f339 : Formula :=
  .and f335 f336

def sq334 : Sequent := ⟨f339, f125⟩

def tm172 : Term :=
  (.add (.mul (.const 1000) tm169) (.const 0))

def tm173 : Term :=
  (.add (.mul (.const 10) tm3) (.add (.mul (.const 1) tm28) (.const 0)))

def pf0 : ProofObject Hnet sq5 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf1 : ProofObject Hnet sq4 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq5 pf0 f1 rfl rfl))

def pf2 : ProofObject Hnet sq5 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf3 : ProofObject Hnet sq7 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq5 pf2 f0 rfl rfl))

def pf4 : ProofObject Hnet sq6 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq7) (regionProof := pf3)
    (termX := (.var 0)) (simplex := sx0) (S := ex0)
    (degree := 5) (polynomial := tm5) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex0) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf5 : ProofObject Hnet sq3 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq4 pf1 sq6 pf4
    1 tm0 (.const 1) f94
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf6 : ProofObject Hnet sq8 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm7
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf7 : ProofObject Hnet sq2 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f91
    sq3 pf5 sq8 pf6
    rfl rfl rfl rfl))

def pf8 : ProofObject Hnet sq13 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf9 : ProofObject Hnet sq12 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq13 pf8 f2 rfl rfl))

def pf10 : ProofObject Hnet sq13 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf11 : ProofObject Hnet sq15 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq13 pf10 f0 rfl rfl))

def pf12 : ProofObject Hnet sq14 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq15) (regionProof := pf11)
    (termX := (.var 0)) (simplex := sx1) (S := ex1)
    (degree := 5) (polynomial := tm9) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex1) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf13 : ProofObject Hnet sq11 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq12 pf9 sq14 pf12
    1 tm0 (.const 1) f100
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf14 : ProofObject Hnet sq16 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm11
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf15 : ProofObject Hnet sq10 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f98
    sq11 pf13 sq16 pf14
    rfl rfl rfl rfl))

def pf16 : ProofObject Hnet sq21 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf17 : ProofObject Hnet sq20 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq21 pf16 f3 rfl rfl))

def pf18 : ProofObject Hnet sq21 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf19 : ProofObject Hnet sq23 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq21 pf18 f0 rfl rfl))

def pf20 : ProofObject Hnet sq22 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq23) (regionProof := pf19)
    (termX := (.var 0)) (simplex := sx2) (S := ex2)
    (degree := 5) (polynomial := tm13) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex2) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf21 : ProofObject Hnet sq19 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq20 pf17 sq22 pf20
    1 tm0 (.const 1) f106
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf22 : ProofObject Hnet sq24 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm15
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf23 : ProofObject Hnet sq18 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f104
    sq19 pf21 sq24 pf22
    rfl rfl rfl rfl))

def pf24 : ProofObject Hnet sq29 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf25 : ProofObject Hnet sq28 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq29 pf24 f4 rfl rfl))

def pf26 : ProofObject Hnet sq29 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf27 : ProofObject Hnet sq31 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq29 pf26 f0 rfl rfl))

def pf28 : ProofObject Hnet sq30 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq31) (regionProof := pf27)
    (termX := (.var 0)) (simplex := sx3) (S := ex3)
    (degree := 5) (polynomial := tm17) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex3) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf29 : ProofObject Hnet sq27 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq28 pf25 sq30 pf28
    1 tm0 (.const 1) f112
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf30 : ProofObject Hnet sq32 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm19
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf31 : ProofObject Hnet sq26 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f110
    sq27 pf29 sq32 pf30
    rfl rfl rfl rfl))

def pf32 : ProofObject Hnet sq37 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf33 : ProofObject Hnet sq36 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq37 pf32 f5 rfl rfl))

def pf34 : ProofObject Hnet sq37 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf35 : ProofObject Hnet sq39 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq37 pf34 f0 rfl rfl))

def pf36 : ProofObject Hnet sq38 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq39) (regionProof := pf35)
    (termX := (.var 0)) (simplex := sx4) (S := ex4)
    (degree := 5) (polynomial := tm21) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex4) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf37 : ProofObject Hnet sq35 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq36 pf33 sq38 pf36
    1 tm0 (.const 1) f118
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf38 : ProofObject Hnet sq40 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm23
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf39 : ProofObject Hnet sq34 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f116
    sq35 pf37 sq40 pf38
    rfl rfl rfl rfl))

def pf40 : ProofObject Hnet sq44 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf41 : ProofObject Hnet sq43 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq44 pf40 f6 rfl rfl))

def pf42 : ProofObject Hnet sq44 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf43 : ProofObject Hnet sq46 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq44 pf42 f0 rfl rfl))

def pf44 : ProofObject Hnet sq45 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq46) (regionProof := pf43)
    (termX := (.var 0)) (simplex := sx5) (S := ex5)
    (degree := 5) (polynomial := tm25) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex5) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf45 : ProofObject Hnet sq42 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq43 pf41 sq45 pf44
    1 tm0 (.const 1) f123
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf46 : ProofObject Hnet sq47 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm27
    tm3
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf47 : ProofObject Hnet sq41 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f121
    sq42 pf45 sq47 pf46
    rfl rfl rfl rfl))

theorem v0 : (sq34).semanticallyValid Hnet := (pf39).sound

theorem v1 : (sq41).semanticallyValid Hnet := (pf47).sound

def st0 : OrECtxStep where
  seq := sq33
  leftPremise := sq34
  rightPremise := sq41
  path := .right (.here)
  d₁ := f5
  d₂ := f6
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v2 : (sq33).semanticallyValid Hnet :=
  sound_orECtx st0 v0 v1

theorem v3 : (sq26).semanticallyValid Hnet := (pf31).sound

def st1 : OrECtxStep where
  seq := sq25
  leftPremise := sq26
  rightPremise := sq33
  path := .right (.here)
  d₁ := f4
  d₂ := f7
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v4 : (sq25).semanticallyValid Hnet :=
  sound_orECtx st1 v3 v2

theorem v5 : (sq18).semanticallyValid Hnet := (pf23).sound

def st2 : OrECtxStep where
  seq := sq17
  leftPremise := sq18
  rightPremise := sq25
  path := .right (.here)
  d₁ := f3
  d₂ := f8
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v6 : (sq17).semanticallyValid Hnet :=
  sound_orECtx st2 v5 v4

theorem v7 : (sq10).semanticallyValid Hnet := (pf15).sound

def st3 : OrECtxStep where
  seq := sq9
  leftPremise := sq10
  rightPremise := sq17
  path := .right (.here)
  d₁ := f2
  d₂ := f9
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v8 : (sq9).semanticallyValid Hnet :=
  sound_orECtx st3 v7 v6

theorem v9 : (sq2).semanticallyValid Hnet := (pf7).sound

def st4 : OrECtxStep where
  seq := sq1
  leftPremise := sq2
  rightPremise := sq9
  path := .right (.here)
  d₁ := f1
  d₂ := f10
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v10 : (sq1).semanticallyValid Hnet :=
  sound_orECtx st4 v9 v8

def pf48 : ProofObject Hnet sq52 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf49 : ProofObject Hnet sq51 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq52 pf48 f14 rfl rfl))

def pf50 : ProofObject Hnet sq52 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf51 : ProofObject Hnet sq54 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq52 pf50 f13 rfl rfl))

def pf52 : ProofObject Hnet sq53 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq54) (regionProof := pf51)
    (termX := (.var 2)) (simplex := sx6) (S := ex6)
    (degree := 5) (polynomial := tm30) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex6) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf53 : ProofObject Hnet sq50 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq51 pf49 sq53 pf52
    3 tm1 (.const 1) f129
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf54 : ProofObject Hnet sq55 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm32
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf55 : ProofObject Hnet sq49 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f127
    sq50 pf53 sq55 pf54
    rfl rfl rfl rfl))

def pf56 : ProofObject Hnet sq60 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf57 : ProofObject Hnet sq59 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq60 pf56 f15 rfl rfl))

def pf58 : ProofObject Hnet sq60 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf59 : ProofObject Hnet sq62 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq60 pf58 f13 rfl rfl))

def pf60 : ProofObject Hnet sq61 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq62) (regionProof := pf59)
    (termX := (.var 2)) (simplex := sx7) (S := ex7)
    (degree := 5) (polynomial := tm34) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex7) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf61 : ProofObject Hnet sq58 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq59 pf57 sq61 pf60
    3 tm1 (.const 1) f135
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf62 : ProofObject Hnet sq63 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm36
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf63 : ProofObject Hnet sq57 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f133
    sq58 pf61 sq63 pf62
    rfl rfl rfl rfl))

def pf64 : ProofObject Hnet sq68 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf65 : ProofObject Hnet sq67 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq68 pf64 f16 rfl rfl))

def pf66 : ProofObject Hnet sq68 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf67 : ProofObject Hnet sq70 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq68 pf66 f13 rfl rfl))

def pf68 : ProofObject Hnet sq69 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq70) (regionProof := pf67)
    (termX := (.var 2)) (simplex := sx8) (S := ex8)
    (degree := 5) (polynomial := tm38) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex8) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf69 : ProofObject Hnet sq66 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq67 pf65 sq69 pf68
    3 tm1 (.const 1) f141
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf70 : ProofObject Hnet sq71 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm40
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf71 : ProofObject Hnet sq65 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f139
    sq66 pf69 sq71 pf70
    rfl rfl rfl rfl))

def pf72 : ProofObject Hnet sq76 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf73 : ProofObject Hnet sq75 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq76 pf72 f17 rfl rfl))

def pf74 : ProofObject Hnet sq76 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf75 : ProofObject Hnet sq78 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq76 pf74 f13 rfl rfl))

def pf76 : ProofObject Hnet sq77 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq78) (regionProof := pf75)
    (termX := (.var 2)) (simplex := sx9) (S := ex9)
    (degree := 5) (polynomial := tm42) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex9) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf77 : ProofObject Hnet sq74 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq75 pf73 sq77 pf76
    3 tm1 (.const 1) f147
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf78 : ProofObject Hnet sq79 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm44
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf79 : ProofObject Hnet sq73 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f145
    sq74 pf77 sq79 pf78
    rfl rfl rfl rfl))

def pf80 : ProofObject Hnet sq84 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf81 : ProofObject Hnet sq83 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq84 pf80 f18 rfl rfl))

def pf82 : ProofObject Hnet sq84 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf83 : ProofObject Hnet sq86 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq84 pf82 f13 rfl rfl))

def pf84 : ProofObject Hnet sq85 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq86) (regionProof := pf83)
    (termX := (.var 2)) (simplex := sx10) (S := ex10)
    (degree := 5) (polynomial := tm46) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex10) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf85 : ProofObject Hnet sq82 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq83 pf81 sq85 pf84
    3 tm1 (.const 1) f153
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf86 : ProofObject Hnet sq87 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm48
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf87 : ProofObject Hnet sq81 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f151
    sq82 pf85 sq87 pf86
    rfl rfl rfl rfl))

def pf88 : ProofObject Hnet sq92 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf89 : ProofObject Hnet sq91 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq92 pf88 f19 rfl rfl))

def pf90 : ProofObject Hnet sq92 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf91 : ProofObject Hnet sq94 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq92 pf90 f13 rfl rfl))

def pf92 : ProofObject Hnet sq93 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq94) (regionProof := pf91)
    (termX := (.var 2)) (simplex := sx11) (S := ex11)
    (degree := 5) (polynomial := tm50) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex11) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf93 : ProofObject Hnet sq90 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq91 pf89 sq93 pf92
    3 tm1 (.const 1) f159
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf94 : ProofObject Hnet sq95 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm52
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf95 : ProofObject Hnet sq89 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f157
    sq90 pf93 sq95 pf94
    rfl rfl rfl rfl))

def pf96 : ProofObject Hnet sq100 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf97 : ProofObject Hnet sq99 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq100 pf96 f20 rfl rfl))

def pf98 : ProofObject Hnet sq100 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf99 : ProofObject Hnet sq102 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq100 pf98 f13 rfl rfl))

def pf100 : ProofObject Hnet sq101 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq102) (regionProof := pf99)
    (termX := (.var 2)) (simplex := sx12) (S := ex12)
    (degree := 5) (polynomial := tm54) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex12) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf101 : ProofObject Hnet sq98 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq99 pf97 sq101 pf100
    3 tm1 (.const 1) f165
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf102 : ProofObject Hnet sq103 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm56
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf103 : ProofObject Hnet sq97 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f163
    sq98 pf101 sq103 pf102
    rfl rfl rfl rfl))

def pf104 : ProofObject Hnet sq108 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf105 : ProofObject Hnet sq107 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq108 pf104 f21 rfl rfl))

def pf106 : ProofObject Hnet sq108 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf107 : ProofObject Hnet sq110 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq108 pf106 f13 rfl rfl))

def pf108 : ProofObject Hnet sq109 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq110) (regionProof := pf107)
    (termX := (.var 2)) (simplex := sx13) (S := ex13)
    (degree := 5) (polynomial := tm58) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex13) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf109 : ProofObject Hnet sq106 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq107 pf105 sq109 pf108
    3 tm1 (.const 1) f171
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf110 : ProofObject Hnet sq111 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm60
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf111 : ProofObject Hnet sq105 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f169
    sq106 pf109 sq111 pf110
    rfl rfl rfl rfl))

def pf112 : ProofObject Hnet sq116 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf113 : ProofObject Hnet sq115 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq116 pf112 f22 rfl rfl))

def pf114 : ProofObject Hnet sq116 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf115 : ProofObject Hnet sq118 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq116 pf114 f13 rfl rfl))

def pf116 : ProofObject Hnet sq117 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq118) (regionProof := pf115)
    (termX := (.var 2)) (simplex := sx14) (S := ex14)
    (degree := 5) (polynomial := tm62) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex14) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf117 : ProofObject Hnet sq114 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq115 pf113 sq117 pf116
    3 tm1 (.const 1) f177
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf118 : ProofObject Hnet sq119 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm64
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf119 : ProofObject Hnet sq113 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f175
    sq114 pf117 sq119 pf118
    rfl rfl rfl rfl))

def pf120 : ProofObject Hnet sq124 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf121 : ProofObject Hnet sq123 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq124 pf120 f23 rfl rfl))

def pf122 : ProofObject Hnet sq124 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf123 : ProofObject Hnet sq126 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq124 pf122 f13 rfl rfl))

def pf124 : ProofObject Hnet sq125 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq126) (regionProof := pf123)
    (termX := (.var 2)) (simplex := sx15) (S := ex15)
    (degree := 5) (polynomial := tm66) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex15) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf125 : ProofObject Hnet sq122 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq123 pf121 sq125 pf124
    3 tm1 (.const 1) f183
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf126 : ProofObject Hnet sq127 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm68
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf127 : ProofObject Hnet sq121 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f181
    sq122 pf125 sq127 pf126
    rfl rfl rfl rfl))

def pf128 : ProofObject Hnet sq132 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf129 : ProofObject Hnet sq131 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq132 pf128 f24 rfl rfl))

def pf130 : ProofObject Hnet sq132 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf131 : ProofObject Hnet sq134 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq132 pf130 f13 rfl rfl))

def pf132 : ProofObject Hnet sq133 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq134) (regionProof := pf131)
    (termX := (.var 2)) (simplex := sx16) (S := ex16)
    (degree := 5) (polynomial := tm70) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex16) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf133 : ProofObject Hnet sq130 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq131 pf129 sq133 pf132
    3 tm1 (.const 1) f189
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf134 : ProofObject Hnet sq135 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm72
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf135 : ProofObject Hnet sq129 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f187
    sq130 pf133 sq135 pf134
    rfl rfl rfl rfl))

def pf136 : ProofObject Hnet sq140 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf137 : ProofObject Hnet sq139 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq140 pf136 f25 rfl rfl))

def pf138 : ProofObject Hnet sq140 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf139 : ProofObject Hnet sq142 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq140 pf138 f13 rfl rfl))

def pf140 : ProofObject Hnet sq141 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq142) (regionProof := pf139)
    (termX := (.var 2)) (simplex := sx17) (S := ex17)
    (degree := 5) (polynomial := tm74) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex17) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf141 : ProofObject Hnet sq138 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq139 pf137 sq141 pf140
    3 tm1 (.const 1) f195
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf142 : ProofObject Hnet sq143 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm76
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf143 : ProofObject Hnet sq137 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f193
    sq138 pf141 sq143 pf142
    rfl rfl rfl rfl))

def pf144 : ProofObject Hnet sq148 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf145 : ProofObject Hnet sq147 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq148 pf144 f26 rfl rfl))

def pf146 : ProofObject Hnet sq148 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf147 : ProofObject Hnet sq150 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq148 pf146 f13 rfl rfl))

def pf148 : ProofObject Hnet sq149 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq150) (regionProof := pf147)
    (termX := (.var 2)) (simplex := sx18) (S := ex18)
    (degree := 5) (polynomial := tm78) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex18) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf149 : ProofObject Hnet sq146 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq147 pf145 sq149 pf148
    3 tm1 (.const 1) f201
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf150 : ProofObject Hnet sq151 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm80
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf151 : ProofObject Hnet sq145 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f199
    sq146 pf149 sq151 pf150
    rfl rfl rfl rfl))

def pf152 : ProofObject Hnet sq156 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf153 : ProofObject Hnet sq155 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq156 pf152 f27 rfl rfl))

def pf154 : ProofObject Hnet sq156 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf155 : ProofObject Hnet sq158 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq156 pf154 f13 rfl rfl))

def pf156 : ProofObject Hnet sq157 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq158) (regionProof := pf155)
    (termX := (.var 2)) (simplex := sx19) (S := ex19)
    (degree := 5) (polynomial := tm82) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex19) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf157 : ProofObject Hnet sq154 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq155 pf153 sq157 pf156
    3 tm1 (.const 1) f207
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf158 : ProofObject Hnet sq159 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm84
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf159 : ProofObject Hnet sq153 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f205
    sq154 pf157 sq159 pf158
    rfl rfl rfl rfl))

def pf160 : ProofObject Hnet sq164 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf161 : ProofObject Hnet sq163 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq164 pf160 f28 rfl rfl))

def pf162 : ProofObject Hnet sq164 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf163 : ProofObject Hnet sq166 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq164 pf162 f13 rfl rfl))

def pf164 : ProofObject Hnet sq165 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq166) (regionProof := pf163)
    (termX := (.var 2)) (simplex := sx20) (S := ex20)
    (degree := 8) (polynomial := tm86) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex20) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf165 : ProofObject Hnet sq162 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq163 pf161 sq165 pf164
    3 tm1 (.const 1) f213
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf166 : ProofObject Hnet sq167 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm88
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf167 : ProofObject Hnet sq161 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f211
    sq162 pf165 sq167 pf166
    rfl rfl rfl rfl))

def pf168 : ProofObject Hnet sq172 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf169 : ProofObject Hnet sq171 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq172 pf168 f29 rfl rfl))

def pf170 : ProofObject Hnet sq172 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf171 : ProofObject Hnet sq174 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq172 pf170 f13 rfl rfl))

def pf172 : ProofObject Hnet sq173 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq174) (regionProof := pf171)
    (termX := (.var 2)) (simplex := sx21) (S := ex21)
    (degree := 5) (polynomial := tm90) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex21) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf173 : ProofObject Hnet sq170 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq171 pf169 sq173 pf172
    3 tm1 (.const 1) f219
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf174 : ProofObject Hnet sq175 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm92
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf175 : ProofObject Hnet sq169 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f217
    sq170 pf173 sq175 pf174
    rfl rfl rfl rfl))

def pf176 : ProofObject Hnet sq180 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf177 : ProofObject Hnet sq179 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq180 pf176 f30 rfl rfl))

def pf178 : ProofObject Hnet sq180 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf179 : ProofObject Hnet sq182 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq180 pf178 f13 rfl rfl))

def pf180 : ProofObject Hnet sq181 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq182) (regionProof := pf179)
    (termX := (.var 2)) (simplex := sx22) (S := ex22)
    (degree := 5) (polynomial := tm94) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex22) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf181 : ProofObject Hnet sq178 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq179 pf177 sq181 pf180
    3 tm1 (.const 1) f225
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf182 : ProofObject Hnet sq183 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm96
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf183 : ProofObject Hnet sq177 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f223
    sq178 pf181 sq183 pf182
    rfl rfl rfl rfl))

def pf184 : ProofObject Hnet sq188 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf185 : ProofObject Hnet sq187 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq188 pf184 f31 rfl rfl))

def pf186 : ProofObject Hnet sq188 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf187 : ProofObject Hnet sq190 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq188 pf186 f13 rfl rfl))

def pf188 : ProofObject Hnet sq189 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq190) (regionProof := pf187)
    (termX := (.var 2)) (simplex := sx23) (S := ex23)
    (degree := 5) (polynomial := tm98) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex23) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf189 : ProofObject Hnet sq186 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq187 pf185 sq189 pf188
    3 tm1 (.const 1) f231
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf190 : ProofObject Hnet sq191 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm100
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf191 : ProofObject Hnet sq185 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f229
    sq186 pf189 sq191 pf190
    rfl rfl rfl rfl))

def pf192 : ProofObject Hnet sq196 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf193 : ProofObject Hnet sq195 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq196 pf192 f32 rfl rfl))

def pf194 : ProofObject Hnet sq196 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf195 : ProofObject Hnet sq198 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq196 pf194 f13 rfl rfl))

def pf196 : ProofObject Hnet sq197 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq198) (regionProof := pf195)
    (termX := (.var 2)) (simplex := sx24) (S := ex24)
    (degree := 5) (polynomial := tm102) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex24) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf197 : ProofObject Hnet sq194 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq195 pf193 sq197 pf196
    3 tm1 (.const 1) f237
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf198 : ProofObject Hnet sq199 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm104
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf199 : ProofObject Hnet sq193 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f235
    sq194 pf197 sq199 pf198
    rfl rfl rfl rfl))

def pf200 : ProofObject Hnet sq204 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf201 : ProofObject Hnet sq203 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq204 pf200 f33 rfl rfl))

def pf202 : ProofObject Hnet sq204 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf203 : ProofObject Hnet sq206 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq204 pf202 f13 rfl rfl))

def pf204 : ProofObject Hnet sq205 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq206) (regionProof := pf203)
    (termX := (.var 2)) (simplex := sx25) (S := ex25)
    (degree := 5) (polynomial := tm106) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex25) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf205 : ProofObject Hnet sq202 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq203 pf201 sq205 pf204
    3 tm1 (.const 1) f243
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf206 : ProofObject Hnet sq207 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm108
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf207 : ProofObject Hnet sq201 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f241
    sq202 pf205 sq207 pf206
    rfl rfl rfl rfl))

def pf208 : ProofObject Hnet sq212 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf209 : ProofObject Hnet sq211 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq212 pf208 f34 rfl rfl))

def pf210 : ProofObject Hnet sq212 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf211 : ProofObject Hnet sq214 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq212 pf210 f13 rfl rfl))

def pf212 : ProofObject Hnet sq213 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq214) (regionProof := pf211)
    (termX := (.var 2)) (simplex := sx26) (S := ex26)
    (degree := 5) (polynomial := tm110) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex26) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf213 : ProofObject Hnet sq210 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq211 pf209 sq213 pf212
    3 tm1 (.const 1) f249
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf214 : ProofObject Hnet sq215 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm112
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf215 : ProofObject Hnet sq209 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f247
    sq210 pf213 sq215 pf214
    rfl rfl rfl rfl))

def pf216 : ProofObject Hnet sq220 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf217 : ProofObject Hnet sq219 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq220 pf216 f35 rfl rfl))

def pf218 : ProofObject Hnet sq220 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf219 : ProofObject Hnet sq222 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq220 pf218 f13 rfl rfl))

def pf220 : ProofObject Hnet sq221 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq222) (regionProof := pf219)
    (termX := (.var 2)) (simplex := sx27) (S := ex27)
    (degree := 8) (polynomial := tm114) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex27) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf221 : ProofObject Hnet sq218 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq219 pf217 sq221 pf220
    3 tm1 (.const 1) f255
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf222 : ProofObject Hnet sq223 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm116
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf223 : ProofObject Hnet sq217 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f253
    sq218 pf221 sq223 pf222
    rfl rfl rfl rfl))

def pf224 : ProofObject Hnet sq228 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf225 : ProofObject Hnet sq227 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq228 pf224 f36 rfl rfl))

def pf226 : ProofObject Hnet sq228 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf227 : ProofObject Hnet sq230 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq228 pf226 f13 rfl rfl))

def pf228 : ProofObject Hnet sq229 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq230) (regionProof := pf227)
    (termX := (.var 2)) (simplex := sx28) (S := ex28)
    (degree := 5) (polynomial := tm118) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex28) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf229 : ProofObject Hnet sq226 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq227 pf225 sq229 pf228
    3 tm1 (.const 1) f261
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf230 : ProofObject Hnet sq231 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm120
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf231 : ProofObject Hnet sq225 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f259
    sq226 pf229 sq231 pf230
    rfl rfl rfl rfl))

def pf232 : ProofObject Hnet sq236 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf233 : ProofObject Hnet sq235 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq236 pf232 f37 rfl rfl))

def pf234 : ProofObject Hnet sq236 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf235 : ProofObject Hnet sq238 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq236 pf234 f13 rfl rfl))

def pf236 : ProofObject Hnet sq237 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq238) (regionProof := pf235)
    (termX := (.var 2)) (simplex := sx29) (S := ex29)
    (degree := 5) (polynomial := tm122) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex29) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf237 : ProofObject Hnet sq234 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq235 pf233 sq237 pf236
    3 tm1 (.const 1) f267
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf238 : ProofObject Hnet sq239 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm124
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf239 : ProofObject Hnet sq233 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f265
    sq234 pf237 sq239 pf238
    rfl rfl rfl rfl))

def pf240 : ProofObject Hnet sq244 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf241 : ProofObject Hnet sq243 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq244 pf240 f38 rfl rfl))

def pf242 : ProofObject Hnet sq244 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf243 : ProofObject Hnet sq246 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq244 pf242 f13 rfl rfl))

def pf244 : ProofObject Hnet sq245 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq246) (regionProof := pf243)
    (termX := (.var 2)) (simplex := sx30) (S := ex30)
    (degree := 5) (polynomial := tm126) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex30) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf245 : ProofObject Hnet sq242 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq243 pf241 sq245 pf244
    3 tm1 (.const 1) f273
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf246 : ProofObject Hnet sq247 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm128
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf247 : ProofObject Hnet sq241 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f271
    sq242 pf245 sq247 pf246
    rfl rfl rfl rfl))

def pf248 : ProofObject Hnet sq252 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf249 : ProofObject Hnet sq251 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq252 pf248 f39 rfl rfl))

def pf250 : ProofObject Hnet sq252 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf251 : ProofObject Hnet sq254 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq252 pf250 f13 rfl rfl))

def pf252 : ProofObject Hnet sq253 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq254) (regionProof := pf251)
    (termX := (.var 2)) (simplex := sx31) (S := ex31)
    (degree := 5) (polynomial := tm130) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex31) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf253 : ProofObject Hnet sq250 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq251 pf249 sq253 pf252
    3 tm1 (.const 1) f279
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf254 : ProofObject Hnet sq255 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm132
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf255 : ProofObject Hnet sq249 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f277
    sq250 pf253 sq255 pf254
    rfl rfl rfl rfl))

def pf256 : ProofObject Hnet sq260 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf257 : ProofObject Hnet sq259 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq260 pf256 f40 rfl rfl))

def pf258 : ProofObject Hnet sq260 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf259 : ProofObject Hnet sq262 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq260 pf258 f13 rfl rfl))

def pf260 : ProofObject Hnet sq261 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq262) (regionProof := pf259)
    (termX := (.var 2)) (simplex := sx32) (S := ex32)
    (degree := 5) (polynomial := tm134) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex32) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf261 : ProofObject Hnet sq258 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq259 pf257 sq261 pf260
    3 tm1 (.const 1) f285
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf262 : ProofObject Hnet sq263 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm136
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf263 : ProofObject Hnet sq257 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f283
    sq258 pf261 sq263 pf262
    rfl rfl rfl rfl))

def pf264 : ProofObject Hnet sq268 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf265 : ProofObject Hnet sq267 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq268 pf264 f41 rfl rfl))

def pf266 : ProofObject Hnet sq268 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf267 : ProofObject Hnet sq270 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq268 pf266 f13 rfl rfl))

def pf268 : ProofObject Hnet sq269 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq270) (regionProof := pf267)
    (termX := (.var 2)) (simplex := sx33) (S := ex33)
    (degree := 5) (polynomial := tm138) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex33) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf269 : ProofObject Hnet sq266 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq267 pf265 sq269 pf268
    3 tm1 (.const 1) f291
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf270 : ProofObject Hnet sq271 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm140
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf271 : ProofObject Hnet sq265 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f289
    sq266 pf269 sq271 pf270
    rfl rfl rfl rfl))

def pf272 : ProofObject Hnet sq276 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf273 : ProofObject Hnet sq275 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq276 pf272 f42 rfl rfl))

def pf274 : ProofObject Hnet sq276 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf275 : ProofObject Hnet sq278 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq276 pf274 f13 rfl rfl))

def pf276 : ProofObject Hnet sq277 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq278) (regionProof := pf275)
    (termX := (.var 2)) (simplex := sx34) (S := ex34)
    (degree := 5) (polynomial := tm142) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex34) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf277 : ProofObject Hnet sq274 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq275 pf273 sq277 pf276
    3 tm1 (.const 1) f297
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf278 : ProofObject Hnet sq279 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm144
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf279 : ProofObject Hnet sq273 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f295
    sq274 pf277 sq279 pf278
    rfl rfl rfl rfl))

def pf280 : ProofObject Hnet sq284 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf281 : ProofObject Hnet sq283 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq284 pf280 f43 rfl rfl))

def pf282 : ProofObject Hnet sq284 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf283 : ProofObject Hnet sq286 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq284 pf282 f13 rfl rfl))

def pf284 : ProofObject Hnet sq285 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq286) (regionProof := pf283)
    (termX := (.var 2)) (simplex := sx35) (S := ex35)
    (degree := 5) (polynomial := tm146) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex35) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf285 : ProofObject Hnet sq282 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq283 pf281 sq285 pf284
    3 tm1 (.const 1) f303
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf286 : ProofObject Hnet sq287 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm148
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf287 : ProofObject Hnet sq281 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f301
    sq282 pf285 sq287 pf286
    rfl rfl rfl rfl))

def pf288 : ProofObject Hnet sq292 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf289 : ProofObject Hnet sq291 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq292 pf288 f44 rfl rfl))

def pf290 : ProofObject Hnet sq292 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf291 : ProofObject Hnet sq294 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq292 pf290 f13 rfl rfl))

def pf292 : ProofObject Hnet sq293 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq294) (regionProof := pf291)
    (termX := (.var 2)) (simplex := sx36) (S := ex36)
    (degree := 5) (polynomial := tm150) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex36) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf293 : ProofObject Hnet sq290 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq291 pf289 sq293 pf292
    3 tm1 (.const 1) f309
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf294 : ProofObject Hnet sq295 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm152
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf295 : ProofObject Hnet sq289 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f307
    sq290 pf293 sq295 pf294
    rfl rfl rfl rfl))

def pf296 : ProofObject Hnet sq300 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf297 : ProofObject Hnet sq299 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq300 pf296 f45 rfl rfl))

def pf298 : ProofObject Hnet sq300 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf299 : ProofObject Hnet sq302 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq300 pf298 f13 rfl rfl))

def pf300 : ProofObject Hnet sq301 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq302) (regionProof := pf299)
    (termX := (.var 2)) (simplex := sx37) (S := ex37)
    (degree := 5) (polynomial := tm154) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex37) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf301 : ProofObject Hnet sq298 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq299 pf297 sq301 pf300
    3 tm1 (.const 1) f315
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf302 : ProofObject Hnet sq303 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm156
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf303 : ProofObject Hnet sq297 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f313
    sq298 pf301 sq303 pf302
    rfl rfl rfl rfl))

def pf304 : ProofObject Hnet sq308 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf305 : ProofObject Hnet sq307 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq308 pf304 f46 rfl rfl))

def pf306 : ProofObject Hnet sq308 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf307 : ProofObject Hnet sq310 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq308 pf306 f13 rfl rfl))

def pf308 : ProofObject Hnet sq309 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq310) (regionProof := pf307)
    (termX := (.var 2)) (simplex := sx38) (S := ex38)
    (degree := 5) (polynomial := tm158) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex38) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf309 : ProofObject Hnet sq306 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq307 pf305 sq309 pf308
    3 tm1 (.const 1) f321
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf310 : ProofObject Hnet sq311 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm160
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf311 : ProofObject Hnet sq305 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f319
    sq306 pf309 sq311 pf310
    rfl rfl rfl rfl))

def pf312 : ProofObject Hnet sq316 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf313 : ProofObject Hnet sq315 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq316 pf312 f47 rfl rfl))

def pf314 : ProofObject Hnet sq316 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf315 : ProofObject Hnet sq318 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq316 pf314 f13 rfl rfl))

def pf316 : ProofObject Hnet sq317 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq318) (regionProof := pf315)
    (termX := (.var 2)) (simplex := sx39) (S := ex39)
    (degree := 5) (polynomial := tm162) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex39) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf317 : ProofObject Hnet sq314 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq315 pf313 sq317 pf316
    3 tm1 (.const 1) f327
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf318 : ProofObject Hnet sq319 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm164
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf319 : ProofObject Hnet sq313 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f325
    sq314 pf317 sq319 pf318
    rfl rfl rfl rfl))

def pf320 : ProofObject Hnet sq324 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf321 : ProofObject Hnet sq323 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq324 pf320 f48 rfl rfl))

def pf322 : ProofObject Hnet sq324 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf323 : ProofObject Hnet sq326 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq324 pf322 f13 rfl rfl))

def pf324 : ProofObject Hnet sq325 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq326) (regionProof := pf323)
    (termX := (.var 2)) (simplex := sx40) (S := ex40)
    (degree := 5) (polynomial := tm166) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex40) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf325 : ProofObject Hnet sq322 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq323 pf321 sq325 pf324
    3 tm1 (.const 1) f333
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf326 : ProofObject Hnet sq327 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm168
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf327 : ProofObject Hnet sq321 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f331
    sq322 pf325 sq327 pf326
    rfl rfl rfl rfl))

def pf328 : ProofObject Hnet sq331 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf329 : ProofObject Hnet sq330 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq331 pf328 f49 rfl rfl))

def pf330 : ProofObject Hnet sq331 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf331 : ProofObject Hnet sq333 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq331 pf330 f13 rfl rfl))

def pf332 : ProofObject Hnet sq332 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq333) (regionProof := pf331)
    (termX := (.var 2)) (simplex := sx41) (S := ex41)
    (degree := 5) (polynomial := tm170) (predicate := f93)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex41) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf333 : ProofObject Hnet sq329 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq330 pf329 sq332 pf332
    3 tm1 (.const 1) f338
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf334 : ProofObject Hnet sq334 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm172
    tm28
    91
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf335 : ProofObject Hnet sq328 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f336
    sq329 pf333 sq334 pf334
    rfl rfl rfl rfl))

theorem v11 : (sq321).semanticallyValid Hnet := (pf327).sound

theorem v12 : (sq328).semanticallyValid Hnet := (pf335).sound

def st5 : OrECtxStep where
  seq := sq320
  leftPremise := sq321
  rightPremise := sq328
  path := .right (.here)
  d₁ := f48
  d₂ := f49
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v13 : (sq320).semanticallyValid Hnet :=
  sound_orECtx st5 v11 v12

theorem v14 : (sq313).semanticallyValid Hnet := (pf319).sound

def st6 : OrECtxStep where
  seq := sq312
  leftPremise := sq313
  rightPremise := sq320
  path := .right (.here)
  d₁ := f47
  d₂ := f50
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v15 : (sq312).semanticallyValid Hnet :=
  sound_orECtx st6 v14 v13

theorem v16 : (sq305).semanticallyValid Hnet := (pf311).sound

def st7 : OrECtxStep where
  seq := sq304
  leftPremise := sq305
  rightPremise := sq312
  path := .right (.here)
  d₁ := f46
  d₂ := f51
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v17 : (sq304).semanticallyValid Hnet :=
  sound_orECtx st7 v16 v15

theorem v18 : (sq297).semanticallyValid Hnet := (pf303).sound

def st8 : OrECtxStep where
  seq := sq296
  leftPremise := sq297
  rightPremise := sq304
  path := .right (.here)
  d₁ := f45
  d₂ := f52
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v19 : (sq296).semanticallyValid Hnet :=
  sound_orECtx st8 v18 v17

theorem v20 : (sq289).semanticallyValid Hnet := (pf295).sound

def st9 : OrECtxStep where
  seq := sq288
  leftPremise := sq289
  rightPremise := sq296
  path := .right (.here)
  d₁ := f44
  d₂ := f53
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v21 : (sq288).semanticallyValid Hnet :=
  sound_orECtx st9 v20 v19

theorem v22 : (sq281).semanticallyValid Hnet := (pf287).sound

def st10 : OrECtxStep where
  seq := sq280
  leftPremise := sq281
  rightPremise := sq288
  path := .right (.here)
  d₁ := f43
  d₂ := f54
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v23 : (sq280).semanticallyValid Hnet :=
  sound_orECtx st10 v22 v21

theorem v24 : (sq273).semanticallyValid Hnet := (pf279).sound

def st11 : OrECtxStep where
  seq := sq272
  leftPremise := sq273
  rightPremise := sq280
  path := .right (.here)
  d₁ := f42
  d₂ := f55
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v25 : (sq272).semanticallyValid Hnet :=
  sound_orECtx st11 v24 v23

theorem v26 : (sq265).semanticallyValid Hnet := (pf271).sound

def st12 : OrECtxStep where
  seq := sq264
  leftPremise := sq265
  rightPremise := sq272
  path := .right (.here)
  d₁ := f41
  d₂ := f56
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v27 : (sq264).semanticallyValid Hnet :=
  sound_orECtx st12 v26 v25

theorem v28 : (sq257).semanticallyValid Hnet := (pf263).sound

def st13 : OrECtxStep where
  seq := sq256
  leftPremise := sq257
  rightPremise := sq264
  path := .right (.here)
  d₁ := f40
  d₂ := f57
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v29 : (sq256).semanticallyValid Hnet :=
  sound_orECtx st13 v28 v27

theorem v30 : (sq249).semanticallyValid Hnet := (pf255).sound

def st14 : OrECtxStep where
  seq := sq248
  leftPremise := sq249
  rightPremise := sq256
  path := .right (.here)
  d₁ := f39
  d₂ := f58
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v31 : (sq248).semanticallyValid Hnet :=
  sound_orECtx st14 v30 v29

theorem v32 : (sq241).semanticallyValid Hnet := (pf247).sound

def st15 : OrECtxStep where
  seq := sq240
  leftPremise := sq241
  rightPremise := sq248
  path := .right (.here)
  d₁ := f38
  d₂ := f59
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v33 : (sq240).semanticallyValid Hnet :=
  sound_orECtx st15 v32 v31

theorem v34 : (sq233).semanticallyValid Hnet := (pf239).sound

def st16 : OrECtxStep where
  seq := sq232
  leftPremise := sq233
  rightPremise := sq240
  path := .right (.here)
  d₁ := f37
  d₂ := f60
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v35 : (sq232).semanticallyValid Hnet :=
  sound_orECtx st16 v34 v33

theorem v36 : (sq225).semanticallyValid Hnet := (pf231).sound

def st17 : OrECtxStep where
  seq := sq224
  leftPremise := sq225
  rightPremise := sq232
  path := .right (.here)
  d₁ := f36
  d₂ := f61
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v37 : (sq224).semanticallyValid Hnet :=
  sound_orECtx st17 v36 v35

theorem v38 : (sq217).semanticallyValid Hnet := (pf223).sound

def st18 : OrECtxStep where
  seq := sq216
  leftPremise := sq217
  rightPremise := sq224
  path := .right (.here)
  d₁ := f35
  d₂ := f62
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v39 : (sq216).semanticallyValid Hnet :=
  sound_orECtx st18 v38 v37

theorem v40 : (sq209).semanticallyValid Hnet := (pf215).sound

def st19 : OrECtxStep where
  seq := sq208
  leftPremise := sq209
  rightPremise := sq216
  path := .right (.here)
  d₁ := f34
  d₂ := f63
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v41 : (sq208).semanticallyValid Hnet :=
  sound_orECtx st19 v40 v39

theorem v42 : (sq201).semanticallyValid Hnet := (pf207).sound

def st20 : OrECtxStep where
  seq := sq200
  leftPremise := sq201
  rightPremise := sq208
  path := .right (.here)
  d₁ := f33
  d₂ := f64
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v43 : (sq200).semanticallyValid Hnet :=
  sound_orECtx st20 v42 v41

theorem v44 : (sq193).semanticallyValid Hnet := (pf199).sound

def st21 : OrECtxStep where
  seq := sq192
  leftPremise := sq193
  rightPremise := sq200
  path := .right (.here)
  d₁ := f32
  d₂ := f65
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v45 : (sq192).semanticallyValid Hnet :=
  sound_orECtx st21 v44 v43

theorem v46 : (sq185).semanticallyValid Hnet := (pf191).sound

def st22 : OrECtxStep where
  seq := sq184
  leftPremise := sq185
  rightPremise := sq192
  path := .right (.here)
  d₁ := f31
  d₂ := f66
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v47 : (sq184).semanticallyValid Hnet :=
  sound_orECtx st22 v46 v45

theorem v48 : (sq177).semanticallyValid Hnet := (pf183).sound

def st23 : OrECtxStep where
  seq := sq176
  leftPremise := sq177
  rightPremise := sq184
  path := .right (.here)
  d₁ := f30
  d₂ := f67
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v49 : (sq176).semanticallyValid Hnet :=
  sound_orECtx st23 v48 v47

theorem v50 : (sq169).semanticallyValid Hnet := (pf175).sound

def st24 : OrECtxStep where
  seq := sq168
  leftPremise := sq169
  rightPremise := sq176
  path := .right (.here)
  d₁ := f29
  d₂ := f68
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v51 : (sq168).semanticallyValid Hnet :=
  sound_orECtx st24 v50 v49

theorem v52 : (sq161).semanticallyValid Hnet := (pf167).sound

def st25 : OrECtxStep where
  seq := sq160
  leftPremise := sq161
  rightPremise := sq168
  path := .right (.here)
  d₁ := f28
  d₂ := f69
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v53 : (sq160).semanticallyValid Hnet :=
  sound_orECtx st25 v52 v51

theorem v54 : (sq153).semanticallyValid Hnet := (pf159).sound

def st26 : OrECtxStep where
  seq := sq152
  leftPremise := sq153
  rightPremise := sq160
  path := .right (.here)
  d₁ := f27
  d₂ := f70
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v55 : (sq152).semanticallyValid Hnet :=
  sound_orECtx st26 v54 v53

theorem v56 : (sq145).semanticallyValid Hnet := (pf151).sound

def st27 : OrECtxStep where
  seq := sq144
  leftPremise := sq145
  rightPremise := sq152
  path := .right (.here)
  d₁ := f26
  d₂ := f71
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v57 : (sq144).semanticallyValid Hnet :=
  sound_orECtx st27 v56 v55

theorem v58 : (sq137).semanticallyValid Hnet := (pf143).sound

def st28 : OrECtxStep where
  seq := sq136
  leftPremise := sq137
  rightPremise := sq144
  path := .right (.here)
  d₁ := f25
  d₂ := f72
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v59 : (sq136).semanticallyValid Hnet :=
  sound_orECtx st28 v58 v57

theorem v60 : (sq129).semanticallyValid Hnet := (pf135).sound

def st29 : OrECtxStep where
  seq := sq128
  leftPremise := sq129
  rightPremise := sq136
  path := .right (.here)
  d₁ := f24
  d₂ := f73
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v61 : (sq128).semanticallyValid Hnet :=
  sound_orECtx st29 v60 v59

theorem v62 : (sq121).semanticallyValid Hnet := (pf127).sound

def st30 : OrECtxStep where
  seq := sq120
  leftPremise := sq121
  rightPremise := sq128
  path := .right (.here)
  d₁ := f23
  d₂ := f74
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v63 : (sq120).semanticallyValid Hnet :=
  sound_orECtx st30 v62 v61

theorem v64 : (sq113).semanticallyValid Hnet := (pf119).sound

def st31 : OrECtxStep where
  seq := sq112
  leftPremise := sq113
  rightPremise := sq120
  path := .right (.here)
  d₁ := f22
  d₂ := f75
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v65 : (sq112).semanticallyValid Hnet :=
  sound_orECtx st31 v64 v63

theorem v66 : (sq105).semanticallyValid Hnet := (pf111).sound

def st32 : OrECtxStep where
  seq := sq104
  leftPremise := sq105
  rightPremise := sq112
  path := .right (.here)
  d₁ := f21
  d₂ := f76
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v67 : (sq104).semanticallyValid Hnet :=
  sound_orECtx st32 v66 v65

theorem v68 : (sq97).semanticallyValid Hnet := (pf103).sound

def st33 : OrECtxStep where
  seq := sq96
  leftPremise := sq97
  rightPremise := sq104
  path := .right (.here)
  d₁ := f20
  d₂ := f77
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v69 : (sq96).semanticallyValid Hnet :=
  sound_orECtx st33 v68 v67

theorem v70 : (sq89).semanticallyValid Hnet := (pf95).sound

def st34 : OrECtxStep where
  seq := sq88
  leftPremise := sq89
  rightPremise := sq96
  path := .right (.here)
  d₁ := f19
  d₂ := f78
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v71 : (sq88).semanticallyValid Hnet :=
  sound_orECtx st34 v70 v69

theorem v72 : (sq81).semanticallyValid Hnet := (pf87).sound

def st35 : OrECtxStep where
  seq := sq80
  leftPremise := sq81
  rightPremise := sq88
  path := .right (.here)
  d₁ := f18
  d₂ := f79
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v73 : (sq80).semanticallyValid Hnet :=
  sound_orECtx st35 v72 v71

theorem v74 : (sq73).semanticallyValid Hnet := (pf79).sound

def st36 : OrECtxStep where
  seq := sq72
  leftPremise := sq73
  rightPremise := sq80
  path := .right (.here)
  d₁ := f17
  d₂ := f80
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v75 : (sq72).semanticallyValid Hnet :=
  sound_orECtx st36 v74 v73

theorem v76 : (sq65).semanticallyValid Hnet := (pf71).sound

def st37 : OrECtxStep where
  seq := sq64
  leftPremise := sq65
  rightPremise := sq72
  path := .right (.here)
  d₁ := f16
  d₂ := f81
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v77 : (sq64).semanticallyValid Hnet :=
  sound_orECtx st37 v76 v75

theorem v78 : (sq57).semanticallyValid Hnet := (pf63).sound

def st38 : OrECtxStep where
  seq := sq56
  leftPremise := sq57
  rightPremise := sq64
  path := .right (.here)
  d₁ := f15
  d₂ := f82
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v79 : (sq56).semanticallyValid Hnet :=
  sound_orECtx st38 v78 v77

theorem v80 : (sq49).semanticallyValid Hnet := (pf55).sound

def st39 : OrECtxStep where
  seq := sq48
  leftPremise := sq49
  rightPremise := sq56
  path := .right (.here)
  d₁ := f14
  d₂ := f83
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v81 : (sq48).semanticallyValid Hnet :=
  sound_orECtx st39 v80 v79

def st40 : SyzygyStep Hnet where
  seq := sq0
  components := [sq1, sq48]
  combination := tm173
  conclusion := tm2
  preContains := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals unfold premiseContains
    all_goals decide +kernel
  conclShape := ⟨[], by decide +kernel⟩
  conclFin := by decide +kernel
  wiresPos := by decide +kernel
  compPostWiresPos := by decide +kernel
  valid := by decide +kernel
  postForm := Or.inl rfl

theorem v82 : (sq0).semanticallyValid Hnet :=
  sound_syzygy st40 (by

    have hlit : ∀ c ∈ [sq1, sq48], c.semanticallyValid Hnet := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact v10
      · exact v81
    exact hlit)

theorem DpCompositeSyzygy_valid : (sq0).semanticallyValid Hnet := v82

#print axioms DpCompositeSyzygy_valid

end PPLC.Handshake.DpCompositeSyzygy
