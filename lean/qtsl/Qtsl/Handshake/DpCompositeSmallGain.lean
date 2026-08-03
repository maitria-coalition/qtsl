import Qtsl.Soundness
import Qtsl.Decide
import Qtsl.Admissible

/-!
# Composite small-gain certificate (generated)

Generated from certificate bytes by the untrusted export tool — a wrong
translation is refused by Lean, never silently accepted. Do not edit by
hand. The small-gain modulus carried by the wire payload is recorded as
provenance only; range checking is reference-checker-side.
-/

namespace PPLC.Handshake.DpCompositeSmallGain

open PPLC

set_option maxRecDepth 4096

set_option maxHeartbeats 40000000

def cx0coords : List (List Rat) :=
  [[(-27/200), (9/10), (3/10)],
   [(-3/50), (9/10), (3/10)],
   [(-3/50), 1, (3/10)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/10)],
   [(-3/50), (9/10), (3/10)],
   [(-3/50), (9/10), (3/5)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/10)],
   [(-27/200), 1, (3/10)],
   [(-3/50), 1, (3/10)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/10)],
   [(-27/200), 1, (3/10)],
   [(-27/200), 1, (3/5)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/10)],
   [(-27/200), (9/10), (3/5)],
   [(-3/50), (9/10), (3/5)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/10)],
   [(-27/200), (9/10), (3/5)],
   [(-27/200), 1, (3/5)],
   [(-3/50), 1, (3/5)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-3/50), (9/10), (3/20)],
   [(-3/50), 1, (3/20)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-3/50), (9/10), (3/20)],
   [(-3/50), (9/10), (3/10)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-27/200), 1, (3/20)],
   [(-3/50), 1, (3/20)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-27/200), 1, (3/20)],
   [(-27/200), 1, (3/10)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-27/200), (9/10), (3/10)],
   [(-3/50), (9/10), (3/10)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/20)],
   [(-27/200), (9/10), (3/10)],
   [(-27/200), 1, (3/10)],
   [(-3/50), 1, (3/10)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-3/50), (9/10), (3/40)],
   [(-3/50), 1, (3/40)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-3/50), (9/10), (3/40)],
   [(-3/50), (9/10), (3/20)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-27/200), 1, (3/40)],
   [(-3/50), 1, (3/40)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-27/200), 1, (3/40)],
   [(-27/200), 1, (3/20)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-27/200), (9/10), (3/20)],
   [(-3/50), (9/10), (3/20)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), (3/40)],
   [(-27/200), (9/10), (3/20)],
   [(-27/200), 1, (3/20)],
   [(-3/50), 1, (3/20)]]

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
  [[(-27/200), (9/10), 0],
   [(-3/50), (9/10), 0],
   [(-3/50), 1, 0],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (9/10), 0],
   [(-3/50), (9/10), 0],
   [(-3/50), (9/10), (3/40)],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (9/10), 0],
   [(-27/200), 1, 0],
   [(-3/50), 1, 0],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (9/10), 0],
   [(-27/200), 1, 0],
   [(-27/200), 1, (3/40)],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (9/10), 0],
   [(-27/200), (9/10), (3/40)],
   [(-3/50), (9/10), (3/40)],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (9/10), 0],
   [(-27/200), (9/10), (3/40)],
   [(-27/200), 1, (3/40)],
   [(-3/50), 1, (3/40)]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-3/50), (19/20), (-3/40)],
   [(-3/50), 1, (-3/40)],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-3/50), (19/20), (-3/40)],
   [(-3/50), (19/20), 0],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-27/200), 1, (-3/40)],
   [(-3/50), 1, (-3/40)],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-27/200), 1, (-3/40)],
   [(-27/200), 1, 0],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-27/200), (19/20), 0],
   [(-3/50), (19/20), 0],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (19/20), (-3/40)],
   [(-27/200), (19/20), 0],
   [(-27/200), 1, 0],
   [(-3/50), 1, 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-3/50), (9/10), (-3/40)],
   [(-3/50), (19/20), (-3/40)],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-3/50), (9/10), (-3/40)],
   [(-3/50), (9/10), 0],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-27/200), (19/20), (-3/40)],
   [(-3/50), (19/20), (-3/40)],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-27/200), (19/20), (-3/40)],
   [(-27/200), (19/20), 0],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-27/200), (9/10), 0],
   [(-3/50), (9/10), 0],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/40)],
   [(-27/200), (9/10), 0],
   [(-27/200), (19/20), 0],
   [(-3/50), (19/20), 0]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-3/50), (9/10), (-3/20)],
   [(-3/50), 1, (-3/20)],
   [(-3/50), 1, (-3/40)]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-3/50), (9/10), (-3/20)],
   [(-3/50), (9/10), (-3/40)],
   [(-3/50), 1, (-3/40)]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-27/200), 1, (-3/20)],
   [(-3/50), 1, (-3/20)],
   [(-3/50), 1, (-3/40)]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-27/200), 1, (-3/20)],
   [(-27/200), 1, (-3/40)],
   [(-3/50), 1, (-3/40)]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-27/200), (9/10), (-3/40)],
   [(-3/50), (9/10), (-3/40)],
   [(-3/50), 1, (-3/40)]]

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
  [[(-27/200), (9/10), (-3/20)],
   [(-27/200), (9/10), (-3/40)],
   [(-27/200), 1, (-3/40)],
   [(-3/50), 1, (-3/40)]]

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

def cx42coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-3/50), (9/10), (-3/10)],
   [(-3/50), 1, (-3/10)],
   [(-3/50), 1, (-3/20)]]

def cx42 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx42coords.getD v.val []).getD j.val 0
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

def cx43coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-3/50), (9/10), (-3/10)],
   [(-3/50), (9/10), (-3/20)],
   [(-3/50), 1, (-3/20)]]

def cx43 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx43coords.getD v.val []).getD j.val 0
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

def cx44coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-27/200), 1, (-3/10)],
   [(-3/50), 1, (-3/10)],
   [(-3/50), 1, (-3/20)]]

def cx44 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx44coords.getD v.val []).getD j.val 0
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

def cx45coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-27/200), 1, (-3/10)],
   [(-27/200), 1, (-3/20)],
   [(-3/50), 1, (-3/20)]]

def cx45 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx45coords.getD v.val []).getD j.val 0
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

def cx46coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-27/200), (9/10), (-3/20)],
   [(-3/50), (9/10), (-3/20)],
   [(-3/50), 1, (-3/20)]]

def cx46 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx46coords.getD v.val []).getD j.val 0
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

def cx47coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/10)],
   [(-27/200), (9/10), (-3/20)],
   [(-27/200), 1, (-3/20)],
   [(-3/50), 1, (-3/20)]]

def cx47 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx47coords.getD v.val []).getD j.val 0
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

def cx48coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-3/50), (9/10), (-3/5)],
   [(-3/50), 1, (-3/5)],
   [(-3/50), 1, (-3/10)]]

def cx48 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx48coords.getD v.val []).getD j.val 0
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

def cx49coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-3/50), (9/10), (-3/5)],
   [(-3/50), (9/10), (-3/10)],
   [(-3/50), 1, (-3/10)]]

def cx49 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx49coords.getD v.val []).getD j.val 0
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

def cx50coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-27/200), 1, (-3/5)],
   [(-3/50), 1, (-3/5)],
   [(-3/50), 1, (-3/10)]]

def cx50 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx50coords.getD v.val []).getD j.val 0
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

def cx51coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-27/200), 1, (-3/5)],
   [(-27/200), 1, (-3/10)],
   [(-3/50), 1, (-3/10)]]

def cx51 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx51coords.getD v.val []).getD j.val 0
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

def cx52coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-27/200), (9/10), (-3/10)],
   [(-3/50), (9/10), (-3/10)],
   [(-3/50), 1, (-3/10)]]

def cx52 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx52coords.getD v.val []).getD j.val 0
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

def cx53coords : List (List Rat) :=
  [[(-27/200), (9/10), (-3/5)],
   [(-27/200), (9/10), (-3/10)],
   [(-27/200), 1, (-3/10)],
   [(-3/50), 1, (-3/10)]]

def cx53 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx53coords.getD v.val []).getD j.val 0
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

def cx54coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(27/200), (9/10), 0],
   [(27/200), 1, 0],
   [(27/200), 1, (3/5)]]

def cx54 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx54coords.getD v.val []).getD j.val 0
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

def cx55coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(27/200), (9/10), 0],
   [(27/200), (9/10), (3/5)],
   [(27/200), 1, (3/5)]]

def cx55 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx55coords.getD v.val []).getD j.val 0
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

def cx56coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(3/50), 1, 0],
   [(27/200), 1, 0],
   [(27/200), 1, (3/5)]]

def cx56 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx56coords.getD v.val []).getD j.val 0
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

def cx57coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(3/50), 1, 0],
   [(3/50), 1, (3/5)],
   [(27/200), 1, (3/5)]]

def cx57 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx57coords.getD v.val []).getD j.val 0
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

def cx58coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(3/50), (9/10), (3/5)],
   [(27/200), (9/10), (3/5)],
   [(27/200), 1, (3/5)]]

def cx58 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx58coords.getD v.val []).getD j.val 0
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

def cx59coords : List (List Rat) :=
  [[(3/50), (9/10), 0],
   [(3/50), (9/10), (3/5)],
   [(3/50), 1, (3/5)],
   [(27/200), 1, (3/5)]]

def cx59 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx59coords.getD v.val []).getD j.val 0
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

def cx60coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(27/200), (9/10), (-3/40)],
   [(27/200), 1, (-3/40)],
   [(27/200), 1, 0]]

def cx60 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx60coords.getD v.val []).getD j.val 0
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

def cx61coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(27/200), (9/10), (-3/40)],
   [(27/200), (9/10), 0],
   [(27/200), 1, 0]]

def cx61 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx61coords.getD v.val []).getD j.val 0
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

def cx62coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(3/50), 1, (-3/40)],
   [(27/200), 1, (-3/40)],
   [(27/200), 1, 0]]

def cx62 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx62coords.getD v.val []).getD j.val 0
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

def cx63coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(3/50), 1, (-3/40)],
   [(3/50), 1, 0],
   [(27/200), 1, 0]]

def cx63 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx63coords.getD v.val []).getD j.val 0
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

def cx64coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(3/50), (9/10), 0],
   [(27/200), (9/10), 0],
   [(27/200), 1, 0]]

def cx64 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx64coords.getD v.val []).getD j.val 0
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

def cx65coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/40)],
   [(3/50), (9/10), 0],
   [(3/50), 1, 0],
   [(27/200), 1, 0]]

def cx65 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx65coords.getD v.val []).getD j.val 0
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

def cx66coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(27/200), (9/10), (-3/20)],
   [(27/200), 1, (-3/20)],
   [(27/200), 1, (-3/40)]]

def cx66 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx66coords.getD v.val []).getD j.val 0
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

def cx67coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(27/200), (9/10), (-3/20)],
   [(27/200), (9/10), (-3/40)],
   [(27/200), 1, (-3/40)]]

def cx67 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx67coords.getD v.val []).getD j.val 0
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

def cx68coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(3/50), 1, (-3/20)],
   [(27/200), 1, (-3/20)],
   [(27/200), 1, (-3/40)]]

def cx68 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx68coords.getD v.val []).getD j.val 0
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

def cx69coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(3/50), 1, (-3/20)],
   [(3/50), 1, (-3/40)],
   [(27/200), 1, (-3/40)]]

def cx69 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx69coords.getD v.val []).getD j.val 0
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

def cx70coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(3/50), (9/10), (-3/40)],
   [(27/200), (9/10), (-3/40)],
   [(27/200), 1, (-3/40)]]

def cx70 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx70coords.getD v.val []).getD j.val 0
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

def cx71coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/20)],
   [(3/50), (9/10), (-3/40)],
   [(3/50), 1, (-3/40)],
   [(27/200), 1, (-3/40)]]

def cx71 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx71coords.getD v.val []).getD j.val 0
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

def cx72coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(27/200), (9/10), (-3/10)],
   [(27/200), 1, (-3/10)],
   [(27/200), 1, (-3/20)]]

def cx72 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx72coords.getD v.val []).getD j.val 0
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

def cx73coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(27/200), (9/10), (-3/10)],
   [(27/200), (9/10), (-3/20)],
   [(27/200), 1, (-3/20)]]

def cx73 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx73coords.getD v.val []).getD j.val 0
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

def cx74coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(3/50), 1, (-3/10)],
   [(27/200), 1, (-3/10)],
   [(27/200), 1, (-3/20)]]

def cx74 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx74coords.getD v.val []).getD j.val 0
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

def cx75coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(3/50), 1, (-3/10)],
   [(3/50), 1, (-3/20)],
   [(27/200), 1, (-3/20)]]

def cx75 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx75coords.getD v.val []).getD j.val 0
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

def cx76coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(3/50), (9/10), (-3/20)],
   [(27/200), (9/10), (-3/20)],
   [(27/200), 1, (-3/20)]]

def cx76 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx76coords.getD v.val []).getD j.val 0
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

def cx77coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/10)],
   [(3/50), (9/10), (-3/20)],
   [(3/50), 1, (-3/20)],
   [(27/200), 1, (-3/20)]]

def cx77 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx77coords.getD v.val []).getD j.val 0
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

def cx78coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(27/200), (9/10), (-3/5)],
   [(27/200), 1, (-3/5)],
   [(27/200), 1, (-3/10)]]

def cx78 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx78coords.getD v.val []).getD j.val 0
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

def cx79coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(27/200), (9/10), (-3/5)],
   [(27/200), (9/10), (-3/10)],
   [(27/200), 1, (-3/10)]]

def cx79 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx79coords.getD v.val []).getD j.val 0
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

def cx80coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(3/50), 1, (-3/5)],
   [(27/200), 1, (-3/5)],
   [(27/200), 1, (-3/10)]]

def cx80 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx80coords.getD v.val []).getD j.val 0
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

def cx81coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(3/50), 1, (-3/5)],
   [(3/50), 1, (-3/10)],
   [(27/200), 1, (-3/10)]]

def cx81 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx81coords.getD v.val []).getD j.val 0
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

def cx82coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(3/50), (9/10), (-3/10)],
   [(27/200), (9/10), (-3/10)],
   [(27/200), 1, (-3/10)]]

def cx82 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx82coords.getD v.val []).getD j.val 0
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

def cx83coords : List (List Rat) :=
  [[(3/50), (9/10), (-3/5)],
   [(3/50), (9/10), (-3/10)],
   [(3/50), 1, (-3/10)],
   [(27/200), 1, (-3/10)]]

def cx83 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx83coords.getD v.val []).getD j.val 0
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

def cx84coords : List (List Rat) :=
  [[0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0],
   [(9/20), 1, (3/5)]]

def cx84 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx84coords.getD v.val []).getD j.val 0
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

def cx85coords : List (List Rat) :=
  [[0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), (9/10), (3/5)],
   [(9/20), 1, (3/5)]]

def cx85 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx85coords.getD v.val []).getD j.val 0
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

def cx86coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, 1, 0],
   [(9/20), 1, 0],
   [(9/20), 1, (3/5)]]

def cx86 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx86coords.getD v.val []).getD j.val 0
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

def cx87coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, 1, 0],
   [0, 1, (3/5)],
   [(9/20), 1, (3/5)]]

def cx87 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx87coords.getD v.val []).getD j.val 0
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

def cx88coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, (9/10), (3/5)],
   [(9/20), (9/10), (3/5)],
   [(9/20), 1, (3/5)]]

def cx88 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx88coords.getD v.val []).getD j.val 0
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

def cx89coords : List (List Rat) :=
  [[0, (9/10), 0],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)],
   [(9/20), 1, (3/5)]]

def cx89 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx89coords.getD v.val []).getD j.val 0
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

def cx90coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)],
   [0, 1, (3/5)]]

def cx90 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx90coords.getD v.val []).getD j.val 0
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

def cx91coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)]]

def cx91 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx91coords.getD v.val []).getD j.val 0
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

def cx92coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)],
   [0, 1, (3/5)]]

def cx92 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx92coords.getD v.val []).getD j.val 0
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

def cx93coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [(-9/20), 1, (3/5)],
   [0, 1, (3/5)]]

def cx93 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx93coords.getD v.val []).getD j.val 0
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

def cx94coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), (9/10), (3/5)],
   [0, (9/10), (3/5)],
   [0, 1, (3/5)]]

def cx94 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx94coords.getD v.val []).getD j.val 0
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

def cx95coords : List (List Rat) :=
  [[(-9/20), (9/10), (3/10)],
   [(-9/20), (9/10), (3/5)],
   [(-9/20), 1, (3/5)],
   [0, 1, (3/5)]]

def cx95 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx95coords.getD v.val []).getD j.val 0
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

def cx96coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, 1, 0],
   [0, 1, (3/10)]]

def cx96 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx96coords.getD v.val []).getD j.val 0
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

def cx97coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)]]

def cx97 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx97coords.getD v.val []).getD j.val 0
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

def cx98coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [0, 1, 0],
   [0, 1, (3/10)]]

def cx98 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx98coords.getD v.val []).getD j.val 0
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

def cx99coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)]]

def cx99 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx99coords.getD v.val []).getD j.val 0
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

def cx100coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), (9/10), (3/10)],
   [0, (9/10), (3/10)],
   [0, 1, (3/10)]]

def cx100 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx100coords.getD v.val []).getD j.val 0
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

def cx101coords : List (List Rat) :=
  [[(-9/20), (9/10), 0],
   [(-9/20), (9/10), (3/10)],
   [(-9/20), 1, (3/10)],
   [0, 1, (3/10)]]

def cx101 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx101coords.getD v.val []).getD j.val 0
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

def cx102coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)],
   [(9/20), 1, 0]]

def cx102 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx102coords.getD v.val []).getD j.val 0
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

def cx103coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0]]

def cx103 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx103coords.getD v.val []).getD j.val 0
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

def cx104coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)],
   [(9/20), 1, 0]]

def cx104 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx104coords.getD v.val []).getD j.val 0
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

def cx105coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [0, 1, 0],
   [(9/20), 1, 0]]

def cx105 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx105coords.getD v.val []).getD j.val 0
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

def cx106coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, (9/10), 0],
   [(9/20), (9/10), 0],
   [(9/20), 1, 0]]

def cx106 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx106coords.getD v.val []).getD j.val 0
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

def cx107coords : List (List Rat) :=
  [[0, (9/10), (-3/10)],
   [0, (9/10), 0],
   [0, 1, 0],
   [(9/20), 1, 0]]

def cx107 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx107coords.getD v.val []).getD j.val 0
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

def cx108coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [(9/20), (9/10), (-3/5)],
   [(9/20), 1, (-3/5)],
   [(9/20), 1, (-3/10)]]

def cx108 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx108coords.getD v.val []).getD j.val 0
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

def cx109coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [(9/20), (9/10), (-3/5)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx109 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx109coords.getD v.val []).getD j.val 0
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

def cx110coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [(9/20), 1, (-3/5)],
   [(9/20), 1, (-3/10)]]

def cx110 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx110coords.getD v.val []).getD j.val 0
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

def cx111coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx111 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx111coords.getD v.val []).getD j.val 0
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

def cx112coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, (9/10), (-3/10)],
   [(9/20), (9/10), (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx112 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx112coords.getD v.val []).getD j.val 0
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

def cx113coords : List (List Rat) :=
  [[0, (9/10), (-3/5)],
   [0, (9/10), (-3/10)],
   [0, 1, (-3/10)],
   [(9/20), 1, (-3/10)]]

def cx113 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx113coords.getD v.val []).getD j.val 0
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

def cx114coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [0, (9/10), (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, 0]]

def cx114 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx114coords.getD v.val []).getD j.val 0
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

def cx115coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [0, (9/10), (-3/5)],
   [0, (9/10), 0],
   [0, 1, 0]]

def cx115 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx115coords.getD v.val []).getD j.val 0
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

def cx116coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), 1, (-3/5)],
   [0, 1, (-3/5)],
   [0, 1, 0]]

def cx116 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx116coords.getD v.val []).getD j.val 0
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

def cx117coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), 1, (-3/5)],
   [(-9/20), 1, 0],
   [0, 1, 0]]

def cx117 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx117coords.getD v.val []).getD j.val 0
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

def cx118coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), (9/10), 0],
   [0, (9/10), 0],
   [0, 1, 0]]

def cx118 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx118coords.getD v.val []).getD j.val 0
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

def cx119coords : List (List Rat) :=
  [[(-9/20), (9/10), (-3/5)],
   [(-9/20), (9/10), 0],
   [(-9/20), 1, 0],
   [0, 1, 0]]

def cx119 : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => (cx119coords.getD v.val []).getD j.val 0
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
  (.add (.mul (.const 1) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.mul (.const 1) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))))

def f0 : Formula :=
  .atom .eq tm0 (.const 1)

def sx0 : Simplex :=
  ⟨cx0, fun _ => true, by decide +kernel⟩

def ex0 : ExtensionSet :=
  ⟨sx0, fun _ => false, by decide +kernel, by decide +kernel⟩

def f1 : Formula :=
  .inRegion (.var 2) sx0 ex0

def sx1 : Simplex :=
  ⟨cx1, fun _ => true, by decide +kernel⟩

def ex1 : ExtensionSet :=
  ⟨sx1, fun _ => false, by decide +kernel, by decide +kernel⟩

def f2 : Formula :=
  .inRegion (.var 2) sx1 ex1

def sx2 : Simplex :=
  ⟨cx2, fun _ => true, by decide +kernel⟩

def ex2 : ExtensionSet :=
  ⟨sx2, fun _ => false, by decide +kernel, by decide +kernel⟩

def f3 : Formula :=
  .inRegion (.var 2) sx2 ex2

def sx3 : Simplex :=
  ⟨cx3, fun _ => true, by decide +kernel⟩

def ex3 : ExtensionSet :=
  ⟨sx3, fun _ => false, by decide +kernel, by decide +kernel⟩

def f4 : Formula :=
  .inRegion (.var 2) sx3 ex3

def sx4 : Simplex :=
  ⟨cx4, fun _ => true, by decide +kernel⟩

def ex4 : ExtensionSet :=
  ⟨sx4, fun _ => false, by decide +kernel, by decide +kernel⟩

def f5 : Formula :=
  .inRegion (.var 2) sx4 ex4

def sx5 : Simplex :=
  ⟨cx5, fun _ => true, by decide +kernel⟩

def ex5 : ExtensionSet :=
  ⟨sx5, fun _ => false, by decide +kernel, by decide +kernel⟩

def f6 : Formula :=
  .inRegion (.var 2) sx5 ex5

def sx6 : Simplex :=
  ⟨cx6, fun _ => true, by decide +kernel⟩

def ex6 : ExtensionSet :=
  ⟨sx6, fun _ => false, by decide +kernel, by decide +kernel⟩

def f7 : Formula :=
  .inRegion (.var 2) sx6 ex6

def sx7 : Simplex :=
  ⟨cx7, fun _ => true, by decide +kernel⟩

def ex7 : ExtensionSet :=
  ⟨sx7, fun _ => false, by decide +kernel, by decide +kernel⟩

def f8 : Formula :=
  .inRegion (.var 2) sx7 ex7

def sx8 : Simplex :=
  ⟨cx8, fun _ => true, by decide +kernel⟩

def ex8 : ExtensionSet :=
  ⟨sx8, fun _ => false, by decide +kernel, by decide +kernel⟩

def f9 : Formula :=
  .inRegion (.var 2) sx8 ex8

def sx9 : Simplex :=
  ⟨cx9, fun _ => true, by decide +kernel⟩

def ex9 : ExtensionSet :=
  ⟨sx9, fun _ => false, by decide +kernel, by decide +kernel⟩

def f10 : Formula :=
  .inRegion (.var 2) sx9 ex9

def sx10 : Simplex :=
  ⟨cx10, fun _ => true, by decide +kernel⟩

def ex10 : ExtensionSet :=
  ⟨sx10, fun _ => false, by decide +kernel, by decide +kernel⟩

def f11 : Formula :=
  .inRegion (.var 2) sx10 ex10

def sx11 : Simplex :=
  ⟨cx11, fun _ => true, by decide +kernel⟩

def ex11 : ExtensionSet :=
  ⟨sx11, fun _ => false, by decide +kernel, by decide +kernel⟩

def f12 : Formula :=
  .inRegion (.var 2) sx11 ex11

def sx12 : Simplex :=
  ⟨cx12, fun _ => true, by decide +kernel⟩

def ex12 : ExtensionSet :=
  ⟨sx12, fun _ => false, by decide +kernel, by decide +kernel⟩

def f13 : Formula :=
  .inRegion (.var 2) sx12 ex12

def sx13 : Simplex :=
  ⟨cx13, fun _ => true, by decide +kernel⟩

def ex13 : ExtensionSet :=
  ⟨sx13, fun _ => false, by decide +kernel, by decide +kernel⟩

def f14 : Formula :=
  .inRegion (.var 2) sx13 ex13

def sx14 : Simplex :=
  ⟨cx14, fun _ => true, by decide +kernel⟩

def ex14 : ExtensionSet :=
  ⟨sx14, fun _ => false, by decide +kernel, by decide +kernel⟩

def f15 : Formula :=
  .inRegion (.var 2) sx14 ex14

def sx15 : Simplex :=
  ⟨cx15, fun _ => true, by decide +kernel⟩

def ex15 : ExtensionSet :=
  ⟨sx15, fun _ => false, by decide +kernel, by decide +kernel⟩

def f16 : Formula :=
  .inRegion (.var 2) sx15 ex15

def sx16 : Simplex :=
  ⟨cx16, fun _ => true, by decide +kernel⟩

def ex16 : ExtensionSet :=
  ⟨sx16, fun _ => false, by decide +kernel, by decide +kernel⟩

def f17 : Formula :=
  .inRegion (.var 2) sx16 ex16

def sx17 : Simplex :=
  ⟨cx17, fun _ => true, by decide +kernel⟩

def ex17 : ExtensionSet :=
  ⟨sx17, fun _ => false, by decide +kernel, by decide +kernel⟩

def f18 : Formula :=
  .inRegion (.var 2) sx17 ex17

def sx18 : Simplex :=
  ⟨cx18, fun _ => true, by decide +kernel⟩

def ex18 : ExtensionSet :=
  ⟨sx18, fun _ => false, by decide +kernel, by decide +kernel⟩

def f19 : Formula :=
  .inRegion (.var 2) sx18 ex18

def sx19 : Simplex :=
  ⟨cx19, fun _ => true, by decide +kernel⟩

def ex19 : ExtensionSet :=
  ⟨sx19, fun _ => false, by decide +kernel, by decide +kernel⟩

def f20 : Formula :=
  .inRegion (.var 2) sx19 ex19

def sx20 : Simplex :=
  ⟨cx20, fun _ => true, by decide +kernel⟩

def ex20 : ExtensionSet :=
  ⟨sx20, fun _ => false, by decide +kernel, by decide +kernel⟩

def f21 : Formula :=
  .inRegion (.var 2) sx20 ex20

def sx21 : Simplex :=
  ⟨cx21, fun _ => true, by decide +kernel⟩

def ex21 : ExtensionSet :=
  ⟨sx21, fun _ => false, by decide +kernel, by decide +kernel⟩

def f22 : Formula :=
  .inRegion (.var 2) sx21 ex21

def sx22 : Simplex :=
  ⟨cx22, fun _ => true, by decide +kernel⟩

def ex22 : ExtensionSet :=
  ⟨sx22, fun _ => false, by decide +kernel, by decide +kernel⟩

def f23 : Formula :=
  .inRegion (.var 2) sx22 ex22

def sx23 : Simplex :=
  ⟨cx23, fun _ => true, by decide +kernel⟩

def ex23 : ExtensionSet :=
  ⟨sx23, fun _ => false, by decide +kernel, by decide +kernel⟩

def f24 : Formula :=
  .inRegion (.var 2) sx23 ex23

def sx24 : Simplex :=
  ⟨cx24, fun _ => true, by decide +kernel⟩

def ex24 : ExtensionSet :=
  ⟨sx24, fun _ => false, by decide +kernel, by decide +kernel⟩

def f25 : Formula :=
  .inRegion (.var 2) sx24 ex24

def sx25 : Simplex :=
  ⟨cx25, fun _ => true, by decide +kernel⟩

def ex25 : ExtensionSet :=
  ⟨sx25, fun _ => false, by decide +kernel, by decide +kernel⟩

def f26 : Formula :=
  .inRegion (.var 2) sx25 ex25

def sx26 : Simplex :=
  ⟨cx26, fun _ => true, by decide +kernel⟩

def ex26 : ExtensionSet :=
  ⟨sx26, fun _ => false, by decide +kernel, by decide +kernel⟩

def f27 : Formula :=
  .inRegion (.var 2) sx26 ex26

def sx27 : Simplex :=
  ⟨cx27, fun _ => true, by decide +kernel⟩

def ex27 : ExtensionSet :=
  ⟨sx27, fun _ => false, by decide +kernel, by decide +kernel⟩

def f28 : Formula :=
  .inRegion (.var 2) sx27 ex27

def sx28 : Simplex :=
  ⟨cx28, fun _ => true, by decide +kernel⟩

def ex28 : ExtensionSet :=
  ⟨sx28, fun _ => false, by decide +kernel, by decide +kernel⟩

def f29 : Formula :=
  .inRegion (.var 2) sx28 ex28

def sx29 : Simplex :=
  ⟨cx29, fun _ => true, by decide +kernel⟩

def ex29 : ExtensionSet :=
  ⟨sx29, fun _ => false, by decide +kernel, by decide +kernel⟩

def f30 : Formula :=
  .inRegion (.var 2) sx29 ex29

def sx30 : Simplex :=
  ⟨cx30, fun _ => true, by decide +kernel⟩

def ex30 : ExtensionSet :=
  ⟨sx30, fun _ => false, by decide +kernel, by decide +kernel⟩

def f31 : Formula :=
  .inRegion (.var 2) sx30 ex30

def sx31 : Simplex :=
  ⟨cx31, fun _ => true, by decide +kernel⟩

def ex31 : ExtensionSet :=
  ⟨sx31, fun _ => false, by decide +kernel, by decide +kernel⟩

def f32 : Formula :=
  .inRegion (.var 2) sx31 ex31

def sx32 : Simplex :=
  ⟨cx32, fun _ => true, by decide +kernel⟩

def ex32 : ExtensionSet :=
  ⟨sx32, fun _ => false, by decide +kernel, by decide +kernel⟩

def f33 : Formula :=
  .inRegion (.var 2) sx32 ex32

def sx33 : Simplex :=
  ⟨cx33, fun _ => true, by decide +kernel⟩

def ex33 : ExtensionSet :=
  ⟨sx33, fun _ => false, by decide +kernel, by decide +kernel⟩

def f34 : Formula :=
  .inRegion (.var 2) sx33 ex33

def sx34 : Simplex :=
  ⟨cx34, fun _ => true, by decide +kernel⟩

def ex34 : ExtensionSet :=
  ⟨sx34, fun _ => false, by decide +kernel, by decide +kernel⟩

def f35 : Formula :=
  .inRegion (.var 2) sx34 ex34

def sx35 : Simplex :=
  ⟨cx35, fun _ => true, by decide +kernel⟩

def ex35 : ExtensionSet :=
  ⟨sx35, fun _ => false, by decide +kernel, by decide +kernel⟩

def f36 : Formula :=
  .inRegion (.var 2) sx35 ex35

def sx36 : Simplex :=
  ⟨cx36, fun _ => true, by decide +kernel⟩

def ex36 : ExtensionSet :=
  ⟨sx36, fun _ => false, by decide +kernel, by decide +kernel⟩

def f37 : Formula :=
  .inRegion (.var 2) sx36 ex36

def sx37 : Simplex :=
  ⟨cx37, fun _ => true, by decide +kernel⟩

def ex37 : ExtensionSet :=
  ⟨sx37, fun _ => false, by decide +kernel, by decide +kernel⟩

def f38 : Formula :=
  .inRegion (.var 2) sx37 ex37

def sx38 : Simplex :=
  ⟨cx38, fun _ => true, by decide +kernel⟩

def ex38 : ExtensionSet :=
  ⟨sx38, fun _ => false, by decide +kernel, by decide +kernel⟩

def f39 : Formula :=
  .inRegion (.var 2) sx38 ex38

def sx39 : Simplex :=
  ⟨cx39, fun _ => true, by decide +kernel⟩

def ex39 : ExtensionSet :=
  ⟨sx39, fun _ => false, by decide +kernel, by decide +kernel⟩

def f40 : Formula :=
  .inRegion (.var 2) sx39 ex39

def sx40 : Simplex :=
  ⟨cx40, fun _ => true, by decide +kernel⟩

def ex40 : ExtensionSet :=
  ⟨sx40, fun _ => false, by decide +kernel, by decide +kernel⟩

def f41 : Formula :=
  .inRegion (.var 2) sx40 ex40

def sx41 : Simplex :=
  ⟨cx41, fun _ => true, by decide +kernel⟩

def ex41 : ExtensionSet :=
  ⟨sx41, fun _ => false, by decide +kernel, by decide +kernel⟩

def f42 : Formula :=
  .inRegion (.var 2) sx41 ex41

def sx42 : Simplex :=
  ⟨cx42, fun _ => true, by decide +kernel⟩

def ex42 : ExtensionSet :=
  ⟨sx42, fun _ => false, by decide +kernel, by decide +kernel⟩

def f43 : Formula :=
  .inRegion (.var 2) sx42 ex42

def sx43 : Simplex :=
  ⟨cx43, fun _ => true, by decide +kernel⟩

def ex43 : ExtensionSet :=
  ⟨sx43, fun _ => false, by decide +kernel, by decide +kernel⟩

def f44 : Formula :=
  .inRegion (.var 2) sx43 ex43

def sx44 : Simplex :=
  ⟨cx44, fun _ => true, by decide +kernel⟩

def ex44 : ExtensionSet :=
  ⟨sx44, fun _ => false, by decide +kernel, by decide +kernel⟩

def f45 : Formula :=
  .inRegion (.var 2) sx44 ex44

def sx45 : Simplex :=
  ⟨cx45, fun _ => true, by decide +kernel⟩

def ex45 : ExtensionSet :=
  ⟨sx45, fun _ => false, by decide +kernel, by decide +kernel⟩

def f46 : Formula :=
  .inRegion (.var 2) sx45 ex45

def sx46 : Simplex :=
  ⟨cx46, fun _ => true, by decide +kernel⟩

def ex46 : ExtensionSet :=
  ⟨sx46, fun _ => false, by decide +kernel, by decide +kernel⟩

def f47 : Formula :=
  .inRegion (.var 2) sx46 ex46

def sx47 : Simplex :=
  ⟨cx47, fun _ => true, by decide +kernel⟩

def ex47 : ExtensionSet :=
  ⟨sx47, fun _ => false, by decide +kernel, by decide +kernel⟩

def f48 : Formula :=
  .inRegion (.var 2) sx47 ex47

def sx48 : Simplex :=
  ⟨cx48, fun _ => true, by decide +kernel⟩

def ex48 : ExtensionSet :=
  ⟨sx48, fun _ => false, by decide +kernel, by decide +kernel⟩

def f49 : Formula :=
  .inRegion (.var 2) sx48 ex48

def sx49 : Simplex :=
  ⟨cx49, fun _ => true, by decide +kernel⟩

def ex49 : ExtensionSet :=
  ⟨sx49, fun _ => false, by decide +kernel, by decide +kernel⟩

def f50 : Formula :=
  .inRegion (.var 2) sx49 ex49

def sx50 : Simplex :=
  ⟨cx50, fun _ => true, by decide +kernel⟩

def ex50 : ExtensionSet :=
  ⟨sx50, fun _ => false, by decide +kernel, by decide +kernel⟩

def f51 : Formula :=
  .inRegion (.var 2) sx50 ex50

def sx51 : Simplex :=
  ⟨cx51, fun _ => true, by decide +kernel⟩

def ex51 : ExtensionSet :=
  ⟨sx51, fun _ => false, by decide +kernel, by decide +kernel⟩

def f52 : Formula :=
  .inRegion (.var 2) sx51 ex51

def sx52 : Simplex :=
  ⟨cx52, fun _ => true, by decide +kernel⟩

def ex52 : ExtensionSet :=
  ⟨sx52, fun _ => false, by decide +kernel, by decide +kernel⟩

def f53 : Formula :=
  .inRegion (.var 2) sx52 ex52

def sx53 : Simplex :=
  ⟨cx53, fun _ => true, by decide +kernel⟩

def ex53 : ExtensionSet :=
  ⟨sx53, fun _ => false, by decide +kernel, by decide +kernel⟩

def f54 : Formula :=
  .inRegion (.var 2) sx53 ex53

def sx54 : Simplex :=
  ⟨cx54, fun _ => true, by decide +kernel⟩

def ex54 : ExtensionSet :=
  ⟨sx54, fun _ => false, by decide +kernel, by decide +kernel⟩

def f55 : Formula :=
  .inRegion (.var 2) sx54 ex54

def sx55 : Simplex :=
  ⟨cx55, fun _ => true, by decide +kernel⟩

def ex55 : ExtensionSet :=
  ⟨sx55, fun _ => false, by decide +kernel, by decide +kernel⟩

def f56 : Formula :=
  .inRegion (.var 2) sx55 ex55

def sx56 : Simplex :=
  ⟨cx56, fun _ => true, by decide +kernel⟩

def ex56 : ExtensionSet :=
  ⟨sx56, fun _ => false, by decide +kernel, by decide +kernel⟩

def f57 : Formula :=
  .inRegion (.var 2) sx56 ex56

def sx57 : Simplex :=
  ⟨cx57, fun _ => true, by decide +kernel⟩

def ex57 : ExtensionSet :=
  ⟨sx57, fun _ => false, by decide +kernel, by decide +kernel⟩

def f58 : Formula :=
  .inRegion (.var 2) sx57 ex57

def sx58 : Simplex :=
  ⟨cx58, fun _ => true, by decide +kernel⟩

def ex58 : ExtensionSet :=
  ⟨sx58, fun _ => false, by decide +kernel, by decide +kernel⟩

def f59 : Formula :=
  .inRegion (.var 2) sx58 ex58

def sx59 : Simplex :=
  ⟨cx59, fun _ => true, by decide +kernel⟩

def ex59 : ExtensionSet :=
  ⟨sx59, fun _ => false, by decide +kernel, by decide +kernel⟩

def f60 : Formula :=
  .inRegion (.var 2) sx59 ex59

def sx60 : Simplex :=
  ⟨cx60, fun _ => true, by decide +kernel⟩

def ex60 : ExtensionSet :=
  ⟨sx60, fun _ => false, by decide +kernel, by decide +kernel⟩

def f61 : Formula :=
  .inRegion (.var 2) sx60 ex60

def sx61 : Simplex :=
  ⟨cx61, fun _ => true, by decide +kernel⟩

def ex61 : ExtensionSet :=
  ⟨sx61, fun _ => false, by decide +kernel, by decide +kernel⟩

def f62 : Formula :=
  .inRegion (.var 2) sx61 ex61

def sx62 : Simplex :=
  ⟨cx62, fun _ => true, by decide +kernel⟩

def ex62 : ExtensionSet :=
  ⟨sx62, fun _ => false, by decide +kernel, by decide +kernel⟩

def f63 : Formula :=
  .inRegion (.var 2) sx62 ex62

def sx63 : Simplex :=
  ⟨cx63, fun _ => true, by decide +kernel⟩

def ex63 : ExtensionSet :=
  ⟨sx63, fun _ => false, by decide +kernel, by decide +kernel⟩

def f64 : Formula :=
  .inRegion (.var 2) sx63 ex63

def sx64 : Simplex :=
  ⟨cx64, fun _ => true, by decide +kernel⟩

def ex64 : ExtensionSet :=
  ⟨sx64, fun _ => false, by decide +kernel, by decide +kernel⟩

def f65 : Formula :=
  .inRegion (.var 2) sx64 ex64

def sx65 : Simplex :=
  ⟨cx65, fun _ => true, by decide +kernel⟩

def ex65 : ExtensionSet :=
  ⟨sx65, fun _ => false, by decide +kernel, by decide +kernel⟩

def f66 : Formula :=
  .inRegion (.var 2) sx65 ex65

def sx66 : Simplex :=
  ⟨cx66, fun _ => true, by decide +kernel⟩

def ex66 : ExtensionSet :=
  ⟨sx66, fun _ => false, by decide +kernel, by decide +kernel⟩

def f67 : Formula :=
  .inRegion (.var 2) sx66 ex66

def sx67 : Simplex :=
  ⟨cx67, fun _ => true, by decide +kernel⟩

def ex67 : ExtensionSet :=
  ⟨sx67, fun _ => false, by decide +kernel, by decide +kernel⟩

def f68 : Formula :=
  .inRegion (.var 2) sx67 ex67

def sx68 : Simplex :=
  ⟨cx68, fun _ => true, by decide +kernel⟩

def ex68 : ExtensionSet :=
  ⟨sx68, fun _ => false, by decide +kernel, by decide +kernel⟩

def f69 : Formula :=
  .inRegion (.var 2) sx68 ex68

def sx69 : Simplex :=
  ⟨cx69, fun _ => true, by decide +kernel⟩

def ex69 : ExtensionSet :=
  ⟨sx69, fun _ => false, by decide +kernel, by decide +kernel⟩

def f70 : Formula :=
  .inRegion (.var 2) sx69 ex69

def sx70 : Simplex :=
  ⟨cx70, fun _ => true, by decide +kernel⟩

def ex70 : ExtensionSet :=
  ⟨sx70, fun _ => false, by decide +kernel, by decide +kernel⟩

def f71 : Formula :=
  .inRegion (.var 2) sx70 ex70

def sx71 : Simplex :=
  ⟨cx71, fun _ => true, by decide +kernel⟩

def ex71 : ExtensionSet :=
  ⟨sx71, fun _ => false, by decide +kernel, by decide +kernel⟩

def f72 : Formula :=
  .inRegion (.var 2) sx71 ex71

def sx72 : Simplex :=
  ⟨cx72, fun _ => true, by decide +kernel⟩

def ex72 : ExtensionSet :=
  ⟨sx72, fun _ => false, by decide +kernel, by decide +kernel⟩

def f73 : Formula :=
  .inRegion (.var 2) sx72 ex72

def sx73 : Simplex :=
  ⟨cx73, fun _ => true, by decide +kernel⟩

def ex73 : ExtensionSet :=
  ⟨sx73, fun _ => false, by decide +kernel, by decide +kernel⟩

def f74 : Formula :=
  .inRegion (.var 2) sx73 ex73

def sx74 : Simplex :=
  ⟨cx74, fun _ => true, by decide +kernel⟩

def ex74 : ExtensionSet :=
  ⟨sx74, fun _ => false, by decide +kernel, by decide +kernel⟩

def f75 : Formula :=
  .inRegion (.var 2) sx74 ex74

def sx75 : Simplex :=
  ⟨cx75, fun _ => true, by decide +kernel⟩

def ex75 : ExtensionSet :=
  ⟨sx75, fun _ => false, by decide +kernel, by decide +kernel⟩

def f76 : Formula :=
  .inRegion (.var 2) sx75 ex75

def sx76 : Simplex :=
  ⟨cx76, fun _ => true, by decide +kernel⟩

def ex76 : ExtensionSet :=
  ⟨sx76, fun _ => false, by decide +kernel, by decide +kernel⟩

def f77 : Formula :=
  .inRegion (.var 2) sx76 ex76

def sx77 : Simplex :=
  ⟨cx77, fun _ => true, by decide +kernel⟩

def ex77 : ExtensionSet :=
  ⟨sx77, fun _ => false, by decide +kernel, by decide +kernel⟩

def f78 : Formula :=
  .inRegion (.var 2) sx77 ex77

def sx78 : Simplex :=
  ⟨cx78, fun _ => true, by decide +kernel⟩

def ex78 : ExtensionSet :=
  ⟨sx78, fun _ => false, by decide +kernel, by decide +kernel⟩

def f79 : Formula :=
  .inRegion (.var 2) sx78 ex78

def sx79 : Simplex :=
  ⟨cx79, fun _ => true, by decide +kernel⟩

def ex79 : ExtensionSet :=
  ⟨sx79, fun _ => false, by decide +kernel, by decide +kernel⟩

def f80 : Formula :=
  .inRegion (.var 2) sx79 ex79

def sx80 : Simplex :=
  ⟨cx80, fun _ => true, by decide +kernel⟩

def ex80 : ExtensionSet :=
  ⟨sx80, fun _ => false, by decide +kernel, by decide +kernel⟩

def f81 : Formula :=
  .inRegion (.var 2) sx80 ex80

def sx81 : Simplex :=
  ⟨cx81, fun _ => true, by decide +kernel⟩

def ex81 : ExtensionSet :=
  ⟨sx81, fun _ => false, by decide +kernel, by decide +kernel⟩

def f82 : Formula :=
  .inRegion (.var 2) sx81 ex81

def sx82 : Simplex :=
  ⟨cx82, fun _ => true, by decide +kernel⟩

def ex82 : ExtensionSet :=
  ⟨sx82, fun _ => false, by decide +kernel, by decide +kernel⟩

def f83 : Formula :=
  .inRegion (.var 2) sx82 ex82

def sx83 : Simplex :=
  ⟨cx83, fun _ => true, by decide +kernel⟩

def ex83 : ExtensionSet :=
  ⟨sx83, fun _ => false, by decide +kernel, by decide +kernel⟩

def f84 : Formula :=
  .inRegion (.var 2) sx83 ex83

def f85 : Formula :=
  .or f83 f84

def f86 : Formula :=
  .or f82 f85

def f87 : Formula :=
  .or f81 f86

def f88 : Formula :=
  .or f80 f87

def f89 : Formula :=
  .or f79 f88

def f90 : Formula :=
  .or f78 f89

def f91 : Formula :=
  .or f77 f90

def f92 : Formula :=
  .or f76 f91

def f93 : Formula :=
  .or f75 f92

def f94 : Formula :=
  .or f74 f93

def f95 : Formula :=
  .or f73 f94

def f96 : Formula :=
  .or f72 f95

def f97 : Formula :=
  .or f71 f96

def f98 : Formula :=
  .or f70 f97

def f99 : Formula :=
  .or f69 f98

def f100 : Formula :=
  .or f68 f99

def f101 : Formula :=
  .or f67 f100

def f102 : Formula :=
  .or f66 f101

def f103 : Formula :=
  .or f65 f102

def f104 : Formula :=
  .or f64 f103

def f105 : Formula :=
  .or f63 f104

def f106 : Formula :=
  .or f62 f105

def f107 : Formula :=
  .or f61 f106

def f108 : Formula :=
  .or f60 f107

def f109 : Formula :=
  .or f59 f108

def f110 : Formula :=
  .or f58 f109

def f111 : Formula :=
  .or f57 f110

def f112 : Formula :=
  .or f56 f111

def f113 : Formula :=
  .or f55 f112

def f114 : Formula :=
  .or f54 f113

def f115 : Formula :=
  .or f53 f114

def f116 : Formula :=
  .or f52 f115

def f117 : Formula :=
  .or f51 f116

def f118 : Formula :=
  .or f50 f117

def f119 : Formula :=
  .or f49 f118

def f120 : Formula :=
  .or f48 f119

def f121 : Formula :=
  .or f47 f120

def f122 : Formula :=
  .or f46 f121

def f123 : Formula :=
  .or f45 f122

def f124 : Formula :=
  .or f44 f123

def f125 : Formula :=
  .or f43 f124

def f126 : Formula :=
  .or f42 f125

def f127 : Formula :=
  .or f41 f126

def f128 : Formula :=
  .or f40 f127

def f129 : Formula :=
  .or f39 f128

def f130 : Formula :=
  .or f38 f129

def f131 : Formula :=
  .or f37 f130

def f132 : Formula :=
  .or f36 f131

def f133 : Formula :=
  .or f35 f132

def f134 : Formula :=
  .or f34 f133

def f135 : Formula :=
  .or f33 f134

def f136 : Formula :=
  .or f32 f135

def f137 : Formula :=
  .or f31 f136

def f138 : Formula :=
  .or f30 f137

def f139 : Formula :=
  .or f29 f138

def f140 : Formula :=
  .or f28 f139

def f141 : Formula :=
  .or f27 f140

def f142 : Formula :=
  .or f26 f141

def f143 : Formula :=
  .or f25 f142

def f144 : Formula :=
  .or f24 f143

def f145 : Formula :=
  .or f23 f144

def f146 : Formula :=
  .or f22 f145

def f147 : Formula :=
  .or f21 f146

def f148 : Formula :=
  .or f20 f147

def f149 : Formula :=
  .or f19 f148

def f150 : Formula :=
  .or f18 f149

def f151 : Formula :=
  .or f17 f150

def f152 : Formula :=
  .or f16 f151

def f153 : Formula :=
  .or f15 f152

def f154 : Formula :=
  .or f14 f153

def f155 : Formula :=
  .or f13 f154

def f156 : Formula :=
  .or f12 f155

def f157 : Formula :=
  .or f11 f156

def f158 : Formula :=
  .or f10 f157

def f159 : Formula :=
  .or f9 f158

def f160 : Formula :=
  .or f8 f159

def f161 : Formula :=
  .or f7 f160

def f162 : Formula :=
  .or f6 f161

def f163 : Formula :=
  .or f5 f162

def f164 : Formula :=
  .or f4 f163

def f165 : Formula :=
  .or f3 f164

def f166 : Formula :=
  .or f2 f165

def f167 : Formula :=
  .or f1 f166

def f168 : Formula :=
  .and f0 f167

def tm1 : Term :=
  (.add (.mul (.const 1) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.mul (.const 1) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))))

def f169 : Formula :=
  .atom .eq tm1 (.const 1)

def sx84 : Simplex :=
  ⟨cx84, fun _ => true, by decide +kernel⟩

def ex84 : ExtensionSet :=
  ⟨sx84, fun _ => false, by decide +kernel, by decide +kernel⟩

def f170 : Formula :=
  .inRegion (.var 0) sx84 ex84

def sx85 : Simplex :=
  ⟨cx85, fun _ => true, by decide +kernel⟩

def ex85 : ExtensionSet :=
  ⟨sx85, fun _ => false, by decide +kernel, by decide +kernel⟩

def f171 : Formula :=
  .inRegion (.var 0) sx85 ex85

def sx86 : Simplex :=
  ⟨cx86, fun _ => true, by decide +kernel⟩

def ex86 : ExtensionSet :=
  ⟨sx86, fun _ => false, by decide +kernel, by decide +kernel⟩

def f172 : Formula :=
  .inRegion (.var 0) sx86 ex86

def sx87 : Simplex :=
  ⟨cx87, fun _ => true, by decide +kernel⟩

def ex87 : ExtensionSet :=
  ⟨sx87, fun _ => false, by decide +kernel, by decide +kernel⟩

def f173 : Formula :=
  .inRegion (.var 0) sx87 ex87

def sx88 : Simplex :=
  ⟨cx88, fun _ => true, by decide +kernel⟩

def ex88 : ExtensionSet :=
  ⟨sx88, fun _ => false, by decide +kernel, by decide +kernel⟩

def f174 : Formula :=
  .inRegion (.var 0) sx88 ex88

def sx89 : Simplex :=
  ⟨cx89, fun _ => true, by decide +kernel⟩

def ex89 : ExtensionSet :=
  ⟨sx89, fun _ => false, by decide +kernel, by decide +kernel⟩

def f175 : Formula :=
  .inRegion (.var 0) sx89 ex89

def sx90 : Simplex :=
  ⟨cx90, fun _ => true, by decide +kernel⟩

def ex90 : ExtensionSet :=
  ⟨sx90, fun _ => false, by decide +kernel, by decide +kernel⟩

def f176 : Formula :=
  .inRegion (.var 0) sx90 ex90

def sx91 : Simplex :=
  ⟨cx91, fun _ => true, by decide +kernel⟩

def ex91 : ExtensionSet :=
  ⟨sx91, fun _ => false, by decide +kernel, by decide +kernel⟩

def f177 : Formula :=
  .inRegion (.var 0) sx91 ex91

def sx92 : Simplex :=
  ⟨cx92, fun _ => true, by decide +kernel⟩

def ex92 : ExtensionSet :=
  ⟨sx92, fun _ => false, by decide +kernel, by decide +kernel⟩

def f178 : Formula :=
  .inRegion (.var 0) sx92 ex92

def sx93 : Simplex :=
  ⟨cx93, fun _ => true, by decide +kernel⟩

def ex93 : ExtensionSet :=
  ⟨sx93, fun _ => false, by decide +kernel, by decide +kernel⟩

def f179 : Formula :=
  .inRegion (.var 0) sx93 ex93

def sx94 : Simplex :=
  ⟨cx94, fun _ => true, by decide +kernel⟩

def ex94 : ExtensionSet :=
  ⟨sx94, fun _ => false, by decide +kernel, by decide +kernel⟩

def f180 : Formula :=
  .inRegion (.var 0) sx94 ex94

def sx95 : Simplex :=
  ⟨cx95, fun _ => true, by decide +kernel⟩

def ex95 : ExtensionSet :=
  ⟨sx95, fun _ => false, by decide +kernel, by decide +kernel⟩

def f181 : Formula :=
  .inRegion (.var 0) sx95 ex95

def sx96 : Simplex :=
  ⟨cx96, fun _ => true, by decide +kernel⟩

def ex96 : ExtensionSet :=
  ⟨sx96, fun _ => false, by decide +kernel, by decide +kernel⟩

def f182 : Formula :=
  .inRegion (.var 0) sx96 ex96

def sx97 : Simplex :=
  ⟨cx97, fun _ => true, by decide +kernel⟩

def ex97 : ExtensionSet :=
  ⟨sx97, fun _ => false, by decide +kernel, by decide +kernel⟩

def f183 : Formula :=
  .inRegion (.var 0) sx97 ex97

def sx98 : Simplex :=
  ⟨cx98, fun _ => true, by decide +kernel⟩

def ex98 : ExtensionSet :=
  ⟨sx98, fun _ => false, by decide +kernel, by decide +kernel⟩

def f184 : Formula :=
  .inRegion (.var 0) sx98 ex98

def sx99 : Simplex :=
  ⟨cx99, fun _ => true, by decide +kernel⟩

def ex99 : ExtensionSet :=
  ⟨sx99, fun _ => false, by decide +kernel, by decide +kernel⟩

def f185 : Formula :=
  .inRegion (.var 0) sx99 ex99

def sx100 : Simplex :=
  ⟨cx100, fun _ => true, by decide +kernel⟩

def ex100 : ExtensionSet :=
  ⟨sx100, fun _ => false, by decide +kernel, by decide +kernel⟩

def f186 : Formula :=
  .inRegion (.var 0) sx100 ex100

def sx101 : Simplex :=
  ⟨cx101, fun _ => true, by decide +kernel⟩

def ex101 : ExtensionSet :=
  ⟨sx101, fun _ => false, by decide +kernel, by decide +kernel⟩

def f187 : Formula :=
  .inRegion (.var 0) sx101 ex101

def sx102 : Simplex :=
  ⟨cx102, fun _ => true, by decide +kernel⟩

def ex102 : ExtensionSet :=
  ⟨sx102, fun _ => false, by decide +kernel, by decide +kernel⟩

def f188 : Formula :=
  .inRegion (.var 0) sx102 ex102

def sx103 : Simplex :=
  ⟨cx103, fun _ => true, by decide +kernel⟩

def ex103 : ExtensionSet :=
  ⟨sx103, fun _ => false, by decide +kernel, by decide +kernel⟩

def f189 : Formula :=
  .inRegion (.var 0) sx103 ex103

def sx104 : Simplex :=
  ⟨cx104, fun _ => true, by decide +kernel⟩

def ex104 : ExtensionSet :=
  ⟨sx104, fun _ => false, by decide +kernel, by decide +kernel⟩

def f190 : Formula :=
  .inRegion (.var 0) sx104 ex104

def sx105 : Simplex :=
  ⟨cx105, fun _ => true, by decide +kernel⟩

def ex105 : ExtensionSet :=
  ⟨sx105, fun _ => false, by decide +kernel, by decide +kernel⟩

def f191 : Formula :=
  .inRegion (.var 0) sx105 ex105

def sx106 : Simplex :=
  ⟨cx106, fun _ => true, by decide +kernel⟩

def ex106 : ExtensionSet :=
  ⟨sx106, fun _ => false, by decide +kernel, by decide +kernel⟩

def f192 : Formula :=
  .inRegion (.var 0) sx106 ex106

def sx107 : Simplex :=
  ⟨cx107, fun _ => true, by decide +kernel⟩

def ex107 : ExtensionSet :=
  ⟨sx107, fun _ => false, by decide +kernel, by decide +kernel⟩

def f193 : Formula :=
  .inRegion (.var 0) sx107 ex107

def sx108 : Simplex :=
  ⟨cx108, fun _ => true, by decide +kernel⟩

def ex108 : ExtensionSet :=
  ⟨sx108, fun _ => false, by decide +kernel, by decide +kernel⟩

def f194 : Formula :=
  .inRegion (.var 0) sx108 ex108

def sx109 : Simplex :=
  ⟨cx109, fun _ => true, by decide +kernel⟩

def ex109 : ExtensionSet :=
  ⟨sx109, fun _ => false, by decide +kernel, by decide +kernel⟩

def f195 : Formula :=
  .inRegion (.var 0) sx109 ex109

def sx110 : Simplex :=
  ⟨cx110, fun _ => true, by decide +kernel⟩

def ex110 : ExtensionSet :=
  ⟨sx110, fun _ => false, by decide +kernel, by decide +kernel⟩

def f196 : Formula :=
  .inRegion (.var 0) sx110 ex110

def sx111 : Simplex :=
  ⟨cx111, fun _ => true, by decide +kernel⟩

def ex111 : ExtensionSet :=
  ⟨sx111, fun _ => false, by decide +kernel, by decide +kernel⟩

def f197 : Formula :=
  .inRegion (.var 0) sx111 ex111

def sx112 : Simplex :=
  ⟨cx112, fun _ => true, by decide +kernel⟩

def ex112 : ExtensionSet :=
  ⟨sx112, fun _ => false, by decide +kernel, by decide +kernel⟩

def f198 : Formula :=
  .inRegion (.var 0) sx112 ex112

def sx113 : Simplex :=
  ⟨cx113, fun _ => true, by decide +kernel⟩

def ex113 : ExtensionSet :=
  ⟨sx113, fun _ => false, by decide +kernel, by decide +kernel⟩

def f199 : Formula :=
  .inRegion (.var 0) sx113 ex113

def sx114 : Simplex :=
  ⟨cx114, fun _ => true, by decide +kernel⟩

def ex114 : ExtensionSet :=
  ⟨sx114, fun _ => false, by decide +kernel, by decide +kernel⟩

def f200 : Formula :=
  .inRegion (.var 0) sx114 ex114

def sx115 : Simplex :=
  ⟨cx115, fun _ => true, by decide +kernel⟩

def ex115 : ExtensionSet :=
  ⟨sx115, fun _ => false, by decide +kernel, by decide +kernel⟩

def f201 : Formula :=
  .inRegion (.var 0) sx115 ex115

def sx116 : Simplex :=
  ⟨cx116, fun _ => true, by decide +kernel⟩

def ex116 : ExtensionSet :=
  ⟨sx116, fun _ => false, by decide +kernel, by decide +kernel⟩

def f202 : Formula :=
  .inRegion (.var 0) sx116 ex116

def sx117 : Simplex :=
  ⟨cx117, fun _ => true, by decide +kernel⟩

def ex117 : ExtensionSet :=
  ⟨sx117, fun _ => false, by decide +kernel, by decide +kernel⟩

def f203 : Formula :=
  .inRegion (.var 0) sx117 ex117

def sx118 : Simplex :=
  ⟨cx118, fun _ => true, by decide +kernel⟩

def ex118 : ExtensionSet :=
  ⟨sx118, fun _ => false, by decide +kernel, by decide +kernel⟩

def f204 : Formula :=
  .inRegion (.var 0) sx118 ex118

def sx119 : Simplex :=
  ⟨cx119, fun _ => true, by decide +kernel⟩

def ex119 : ExtensionSet :=
  ⟨sx119, fun _ => false, by decide +kernel, by decide +kernel⟩

def f205 : Formula :=
  .inRegion (.var 0) sx119 ex119

def f206 : Formula :=
  .or f204 f205

def f207 : Formula :=
  .or f203 f206

def f208 : Formula :=
  .or f202 f207

def f209 : Formula :=
  .or f201 f208

def f210 : Formula :=
  .or f200 f209

def f211 : Formula :=
  .or f199 f210

def f212 : Formula :=
  .or f198 f211

def f213 : Formula :=
  .or f197 f212

def f214 : Formula :=
  .or f196 f213

def f215 : Formula :=
  .or f195 f214

def f216 : Formula :=
  .or f194 f215

def f217 : Formula :=
  .or f193 f216

def f218 : Formula :=
  .or f192 f217

def f219 : Formula :=
  .or f191 f218

def f220 : Formula :=
  .or f190 f219

def f221 : Formula :=
  .or f189 f220

def f222 : Formula :=
  .or f188 f221

def f223 : Formula :=
  .or f187 f222

def f224 : Formula :=
  .or f186 f223

def f225 : Formula :=
  .or f185 f224

def f226 : Formula :=
  .or f184 f225

def f227 : Formula :=
  .or f183 f226

def f228 : Formula :=
  .or f182 f227

def f229 : Formula :=
  .or f181 f228

def f230 : Formula :=
  .or f180 f229

def f231 : Formula :=
  .or f179 f230

def f232 : Formula :=
  .or f178 f231

def f233 : Formula :=
  .or f177 f232

def f234 : Formula :=
  .or f176 f233

def f235 : Formula :=
  .or f175 f234

def f236 : Formula :=
  .or f174 f235

def f237 : Formula :=
  .or f173 f236

def f238 : Formula :=
  .or f172 f237

def f239 : Formula :=
  .or f171 f238

def f240 : Formula :=
  .or f170 f239

def f241 : Formula :=
  .and f169 f240

def f242 : Formula :=
  .and f168 f241

def f243 : Formula :=
  .and f242 spH

def tm2 : Term :=
  (.add (.mul (.const 200) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const 200) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-400)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1000)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-400)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1000)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const 1)))))))))

def f244 : Formula :=
  .atom .le tm2 (.const 0)

def sq0 : Sequent := ⟨f243, f244⟩

def tm3 : Term :=
  (.add (.mul (.const 80) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-160)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-320)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-400)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const 1)))))

def f245 : Formula :=
  .atom .le tm3 (.const 0)

def sq1 : Sequent := ⟨f168, f245⟩

def f246 : Formula :=
  .and f0 f1

def sq2 : Sequent := ⟨f246, f245⟩

def tm4 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-11165412593/786045)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1975759061/812746)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (5187733522/543187)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (81943339/47197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4690589773/888228)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-3050/237)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12937601828/803917)) (.idx (.var 2) 0)) (.add (.mul (.const (-10202524905/854174)) (.idx (.var 2) 1)) (.add (.mul (.const (-1277642297/699581)) (.idx (.var 2) 2)) (.const (4159544053/618350))))))))))) (.sub (.const 1) (.const 1))))

def f247 : Formula :=
  .atom .le tm4 (.const 0)

def sq3 : Sequent := ⟨f246, f247⟩

def sq4 : Sequent := ⟨f246, f0⟩

def sq5 : Sequent := ⟨f246, f246⟩

def tm5 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-11165412593/786045)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1975759061/812746)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (5187733522/543187)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (81943339/47197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4690589773/888228)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-3050/237)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12937601828/803917)) (.idx (.var 2) 0)) (.add (.mul (.const (-10202524905/854174)) (.idx (.var 2) 1)) (.add (.mul (.const (-1277642297/699581)) (.idx (.var 2) 2)) (.const (4159544053/618350))))))))))) (.sub tm0 (.const 1))))

def f248 : Formula :=
  .atom .le tm5 (.const 0)

def sq6 : Sequent := ⟨f246, f248⟩

def sq7 : Sequent := ⟨f246, f1⟩

def f249 : Formula :=
  .atom .le (.var predicateHole) (.const 0)

def tm6 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-11165412593/786045)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1975759061/812746)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (5187733522/543187)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (81943339/47197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4690589773/888228)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-3050/237)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12937601828/803917)) (.idx (.var 2) 0)) (.add (.mul (.const (-10202524905/854174)) (.idx (.var 2) 1)) (.add (.mul (.const (-1277642297/699581)) (.idx (.var 2) 2)) (.const (4159544053/618350))))))))))) (.sub (.var 3) (.const 1))))

def f250 : Formula :=
  .atom .le tm6 (.const 0)

def f251 : Formula :=
  .and f246 f247

def sq8 : Sequent := ⟨f251, f245⟩

def tm7 : Term :=
  (.add (.mul (.const 200) tm4) (.const 0))

def f252 : Formula :=
  .and f0 f166

def sq9 : Sequent := ⟨f252, f245⟩

def f253 : Formula :=
  .and f0 f2

def sq10 : Sequent := ⟨f253, f245⟩

def tm8 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-68382054803/215869)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-85489669187/664850)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-454353261529/966468)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (560916268673/805988)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28944093895/365327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-760063598586/869875)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (201765736331/565872)) (.idx (.var 2) 2)) (.const (157344383350/401589))))))))))) (.sub (.const 1) (.const 1))))

def f254 : Formula :=
  .atom .le tm8 (.const 0)

def sq11 : Sequent := ⟨f253, f254⟩

def sq12 : Sequent := ⟨f253, f0⟩

def sq13 : Sequent := ⟨f253, f253⟩

def tm9 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-68382054803/215869)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-85489669187/664850)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-454353261529/966468)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (560916268673/805988)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28944093895/365327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-760063598586/869875)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (201765736331/565872)) (.idx (.var 2) 2)) (.const (157344383350/401589))))))))))) (.sub tm0 (.const 1))))

def f255 : Formula :=
  .atom .le tm9 (.const 0)

def sq14 : Sequent := ⟨f253, f255⟩

def sq15 : Sequent := ⟨f253, f2⟩

def tm10 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-68382054803/215869)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-85489669187/664850)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-454353261529/966468)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (560916268673/805988)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28944093895/365327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-760063598586/869875)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (201765736331/565872)) (.idx (.var 2) 2)) (.const (157344383350/401589))))))))))) (.sub (.var 3) (.const 1))))

def f256 : Formula :=
  .atom .le tm10 (.const 0)

def f257 : Formula :=
  .and f253 f254

def sq16 : Sequent := ⟨f257, f245⟩

def tm11 : Term :=
  (.add (.mul (.const 200) tm8) (.const 0))

def f258 : Formula :=
  .and f0 f165

def sq17 : Sequent := ⟨f258, f245⟩

def f259 : Formula :=
  .and f0 f3

def sq18 : Sequent := ⟨f259, f245⟩

def tm12 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62569997/546489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (593062110/807551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (36322369/544519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (490319864/970031)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (46964276/982985)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-216123751/537599)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18224693/187024)) (.idx (.var 2) 0)) (.add (.mul (.const (-85125553/334866)) (.idx (.var 2) 1)) (.add (.mul (.const (-82039591/698974)) (.idx (.var 2) 2)) (.const (108463629/857909))))))))))) (.sub (.const 1) (.const 1))))

def f260 : Formula :=
  .atom .le tm12 (.const 0)

def sq19 : Sequent := ⟨f259, f260⟩

def sq20 : Sequent := ⟨f259, f0⟩

def sq21 : Sequent := ⟨f259, f259⟩

def tm13 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62569997/546489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (593062110/807551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (36322369/544519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (490319864/970031)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (46964276/982985)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-216123751/537599)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18224693/187024)) (.idx (.var 2) 0)) (.add (.mul (.const (-85125553/334866)) (.idx (.var 2) 1)) (.add (.mul (.const (-82039591/698974)) (.idx (.var 2) 2)) (.const (108463629/857909))))))))))) (.sub tm0 (.const 1))))

def f261 : Formula :=
  .atom .le tm13 (.const 0)

def sq22 : Sequent := ⟨f259, f261⟩

def sq23 : Sequent := ⟨f259, f3⟩

def tm14 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62569997/546489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (593062110/807551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (36322369/544519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (490319864/970031)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (46964276/982985)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-216123751/537599)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18224693/187024)) (.idx (.var 2) 0)) (.add (.mul (.const (-85125553/334866)) (.idx (.var 2) 1)) (.add (.mul (.const (-82039591/698974)) (.idx (.var 2) 2)) (.const (108463629/857909))))))))))) (.sub (.var 3) (.const 1))))

def f262 : Formula :=
  .atom .le tm14 (.const 0)

def f263 : Formula :=
  .and f259 f260

def sq24 : Sequent := ⟨f263, f245⟩

def tm15 : Term :=
  (.add (.mul (.const 200) tm12) (.const 0))

def f264 : Formula :=
  .and f0 f164

def sq25 : Sequent := ⟨f264, f245⟩

def f265 : Formula :=
  .and f0 f4

def sq26 : Sequent := ⟨f265, f245⟩

def tm16 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3826644261/974318)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (386562067/64036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-7025305865/284742)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-377832980/836161)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-973/208871)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/5813)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2780054341/620195)) (.idx (.var 2) 0)) (.add (.mul (.const (-149071639/377745)) (.idx (.var 2) 1)) (.add (.mul (.const (1101814968/870125)) (.idx (.var 2) 2)) (.const (-279144807/969524))))))))))) (.sub (.const 1) (.const 1))))

def f266 : Formula :=
  .atom .le tm16 (.const 0)

def sq27 : Sequent := ⟨f265, f266⟩

def sq28 : Sequent := ⟨f265, f0⟩

def sq29 : Sequent := ⟨f265, f265⟩

def tm17 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3826644261/974318)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (386562067/64036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-7025305865/284742)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-377832980/836161)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-973/208871)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/5813)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2780054341/620195)) (.idx (.var 2) 0)) (.add (.mul (.const (-149071639/377745)) (.idx (.var 2) 1)) (.add (.mul (.const (1101814968/870125)) (.idx (.var 2) 2)) (.const (-279144807/969524))))))))))) (.sub tm0 (.const 1))))

def f267 : Formula :=
  .atom .le tm17 (.const 0)

def sq30 : Sequent := ⟨f265, f267⟩

def sq31 : Sequent := ⟨f265, f4⟩

def tm18 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3826644261/974318)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (386562067/64036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-7025305865/284742)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-377832980/836161)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-973/208871)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/5813)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-2780054341/620195)) (.idx (.var 2) 0)) (.add (.mul (.const (-149071639/377745)) (.idx (.var 2) 1)) (.add (.mul (.const (1101814968/870125)) (.idx (.var 2) 2)) (.const (-279144807/969524))))))))))) (.sub (.var 3) (.const 1))))

def f268 : Formula :=
  .atom .le tm18 (.const 0)

def f269 : Formula :=
  .and f265 f266

def sq32 : Sequent := ⟨f269, f245⟩

def tm19 : Term :=
  (.add (.mul (.const 200) tm16) (.const 0))

def f270 : Formula :=
  .and f0 f163

def sq33 : Sequent := ⟨f270, f245⟩

def f271 : Formula :=
  .and f0 f5

def sq34 : Sequent := ⟨f271, f245⟩

def tm20 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77302188485/829624)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (924434696323/999737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-368621187396/899603)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (178362989641/277021)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-44824832765/482907)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-223116957341/379426)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (378031947429/655000)) (.idx (.var 2) 2)) (.const (136697292031/409406))))))))))) (.sub (.const 1) (.const 1))))

def f272 : Formula :=
  .atom .le tm20 (.const 0)

def sq35 : Sequent := ⟨f271, f272⟩

def sq36 : Sequent := ⟨f271, f0⟩

def sq37 : Sequent := ⟨f271, f271⟩

def tm21 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77302188485/829624)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (924434696323/999737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-368621187396/899603)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (178362989641/277021)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-44824832765/482907)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-223116957341/379426)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (378031947429/655000)) (.idx (.var 2) 2)) (.const (136697292031/409406))))))))))) (.sub tm0 (.const 1))))

def f273 : Formula :=
  .atom .le tm21 (.const 0)

def sq38 : Sequent := ⟨f271, f273⟩

def sq39 : Sequent := ⟨f271, f5⟩

def tm22 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77302188485/829624)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (924434696323/999737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-368621187396/899603)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (178362989641/277021)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-44824832765/482907)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-223116957341/379426)) (.idx (.var 2) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 1)) (.add (.mul (.const (378031947429/655000)) (.idx (.var 2) 2)) (.const (136697292031/409406))))))))))) (.sub (.var 3) (.const 1))))

def f274 : Formula :=
  .atom .le tm22 (.const 0)

def f275 : Formula :=
  .and f271 f272

def sq40 : Sequent := ⟨f275, f245⟩

def tm23 : Term :=
  (.add (.mul (.const 200) tm20) (.const 0))

def f276 : Formula :=
  .and f0 f162

def sq41 : Sequent := ⟨f276, f245⟩

def f277 : Formula :=
  .and f0 f6

def sq42 : Sequent := ⟨f277, f245⟩

def tm24 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6876587239/776581)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1591189256/519947)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-278799599/383996)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6608285930/604211)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6174980717/192868)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3242033651/472333)) (.idx (.var 2) 0)) (.add (.mul (.const (-31795368898/539275)) (.idx (.var 2) 1)) (.add (.mul (.const (9253186683/815671)) (.idx (.var 2) 2)) (.const (23024659168/863581))))))))))) (.sub (.const 1) (.const 1))))

def f278 : Formula :=
  .atom .le tm24 (.const 0)

def sq43 : Sequent := ⟨f277, f278⟩

def sq44 : Sequent := ⟨f277, f0⟩

def sq45 : Sequent := ⟨f277, f277⟩

def tm25 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6876587239/776581)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1591189256/519947)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-278799599/383996)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6608285930/604211)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6174980717/192868)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3242033651/472333)) (.idx (.var 2) 0)) (.add (.mul (.const (-31795368898/539275)) (.idx (.var 2) 1)) (.add (.mul (.const (9253186683/815671)) (.idx (.var 2) 2)) (.const (23024659168/863581))))))))))) (.sub tm0 (.const 1))))

def f279 : Formula :=
  .atom .le tm25 (.const 0)

def sq46 : Sequent := ⟨f277, f279⟩

def sq47 : Sequent := ⟨f277, f6⟩

def tm26 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6876587239/776581)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1591189256/519947)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-278799599/383996)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6608285930/604211)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6174980717/192868)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3242033651/472333)) (.idx (.var 2) 0)) (.add (.mul (.const (-31795368898/539275)) (.idx (.var 2) 1)) (.add (.mul (.const (9253186683/815671)) (.idx (.var 2) 2)) (.const (23024659168/863581))))))))))) (.sub (.var 3) (.const 1))))

def f280 : Formula :=
  .atom .le tm26 (.const 0)

def f281 : Formula :=
  .and f277 f278

def sq48 : Sequent := ⟨f281, f245⟩

def tm27 : Term :=
  (.add (.mul (.const 200) tm24) (.const 0))

def f282 : Formula :=
  .and f0 f161

def sq49 : Sequent := ⟨f282, f245⟩

def f283 : Formula :=
  .and f0 f7

def sq50 : Sequent := ⟨f283, f245⟩

def tm28 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (4327371341/386559)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-11160765811/129261)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8797315612/578399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (994993564/813023)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-975/821812)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24200/901)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-80328242/907801)) (.idx (.var 2) 0)) (.add (.mul (.const (222663349/456177)) (.idx (.var 2) 1)) (.add (.mul (.const (-179842081/28654)) (.idx (.var 2) 2)) (.const (180435422/841557))))))))))) (.sub (.const 1) (.const 1))))

def f284 : Formula :=
  .atom .le tm28 (.const 0)

def sq51 : Sequent := ⟨f283, f284⟩

def sq52 : Sequent := ⟨f283, f0⟩

def sq53 : Sequent := ⟨f283, f283⟩

def tm29 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (4327371341/386559)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-11160765811/129261)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8797315612/578399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (994993564/813023)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-975/821812)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24200/901)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-80328242/907801)) (.idx (.var 2) 0)) (.add (.mul (.const (222663349/456177)) (.idx (.var 2) 1)) (.add (.mul (.const (-179842081/28654)) (.idx (.var 2) 2)) (.const (180435422/841557))))))))))) (.sub tm0 (.const 1))))

def f285 : Formula :=
  .atom .le tm29 (.const 0)

def sq54 : Sequent := ⟨f283, f285⟩

def sq55 : Sequent := ⟨f283, f7⟩

def tm30 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (4327371341/386559)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-11160765811/129261)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8797315612/578399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (994993564/813023)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-975/821812)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24200/901)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-80328242/907801)) (.idx (.var 2) 0)) (.add (.mul (.const (222663349/456177)) (.idx (.var 2) 1)) (.add (.mul (.const (-179842081/28654)) (.idx (.var 2) 2)) (.const (180435422/841557))))))))))) (.sub (.var 3) (.const 1))))

def f286 : Formula :=
  .atom .le tm30 (.const 0)

def f287 : Formula :=
  .and f283 f284

def sq56 : Sequent := ⟨f287, f245⟩

def tm31 : Term :=
  (.add (.mul (.const 200) tm28) (.const 0))

def f288 : Formula :=
  .and f0 f160

def sq57 : Sequent := ⟨f288, f245⟩

def f289 : Formula :=
  .and f0 f8

def sq58 : Sequent := ⟨f289, f245⟩

def tm32 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-179504535737/553266)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (227400078049/991348)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-15040716506/585515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-28785680702/204433)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181297585061/804987)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5105084687/804180)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (165912822233/656861)) (.idx (.var 2) 0)) (.add (.mul (.const (-244353941819/570832)) (.idx (.var 2) 1)) (.add (.mul (.const (96123981966/605953)) (.idx (.var 2) 2)) (.const (675120221/3410))))))))))) (.sub (.const 1) (.const 1))))

def f290 : Formula :=
  .atom .le tm32 (.const 0)

def sq59 : Sequent := ⟨f289, f290⟩

def sq60 : Sequent := ⟨f289, f0⟩

def sq61 : Sequent := ⟨f289, f289⟩

def tm33 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-179504535737/553266)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (227400078049/991348)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-15040716506/585515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-28785680702/204433)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181297585061/804987)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5105084687/804180)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (165912822233/656861)) (.idx (.var 2) 0)) (.add (.mul (.const (-244353941819/570832)) (.idx (.var 2) 1)) (.add (.mul (.const (96123981966/605953)) (.idx (.var 2) 2)) (.const (675120221/3410))))))))))) (.sub tm0 (.const 1))))

def f291 : Formula :=
  .atom .le tm33 (.const 0)

def sq62 : Sequent := ⟨f289, f291⟩

def sq63 : Sequent := ⟨f289, f8⟩

def tm34 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-179504535737/553266)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (227400078049/991348)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-15040716506/585515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-28785680702/204433)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181297585061/804987)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5105084687/804180)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (165912822233/656861)) (.idx (.var 2) 0)) (.add (.mul (.const (-244353941819/570832)) (.idx (.var 2) 1)) (.add (.mul (.const (96123981966/605953)) (.idx (.var 2) 2)) (.const (675120221/3410))))))))))) (.sub (.var 3) (.const 1))))

def f292 : Formula :=
  .atom .le tm34 (.const 0)

def f293 : Formula :=
  .and f289 f290

def sq64 : Sequent := ⟨f293, f245⟩

def tm35 : Term :=
  (.add (.mul (.const 200) tm32) (.const 0))

def f294 : Formula :=
  .and f0 f159

def sq65 : Sequent := ⟨f294, f245⟩

def f295 : Formula :=
  .and f0 f9

def sq66 : Sequent := ⟨f295, f245⟩

def tm36 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-36690026/490989)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (372287876/976577)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-43075999/599957)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (103990093/863537)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (95215749/991594)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-322244952/777275)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-609737/82907)) (.idx (.var 2) 0)) (.add (.mul (.const (-135583739/671602)) (.idx (.var 2) 1)) (.add (.mul (.const (71851124/947563)) (.idx (.var 2) 2)) (.const (25429368/301013))))))))))) (.sub (.const 1) (.const 1))))

def f296 : Formula :=
  .atom .le tm36 (.const 0)

def sq67 : Sequent := ⟨f295, f296⟩

def sq68 : Sequent := ⟨f295, f0⟩

def sq69 : Sequent := ⟨f295, f295⟩

def tm37 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-36690026/490989)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (372287876/976577)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-43075999/599957)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (103990093/863537)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (95215749/991594)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-322244952/777275)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-609737/82907)) (.idx (.var 2) 0)) (.add (.mul (.const (-135583739/671602)) (.idx (.var 2) 1)) (.add (.mul (.const (71851124/947563)) (.idx (.var 2) 2)) (.const (25429368/301013))))))))))) (.sub tm0 (.const 1))))

def f297 : Formula :=
  .atom .le tm37 (.const 0)

def sq70 : Sequent := ⟨f295, f297⟩

def sq71 : Sequent := ⟨f295, f9⟩

def tm38 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-36690026/490989)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (372287876/976577)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-43075999/599957)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (103990093/863537)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (95215749/991594)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-322244952/777275)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-609737/82907)) (.idx (.var 2) 0)) (.add (.mul (.const (-135583739/671602)) (.idx (.var 2) 1)) (.add (.mul (.const (71851124/947563)) (.idx (.var 2) 2)) (.const (25429368/301013))))))))))) (.sub (.var 3) (.const 1))))

def f298 : Formula :=
  .atom .le tm38 (.const 0)

def f299 : Formula :=
  .and f295 f296

def sq72 : Sequent := ⟨f299, f245⟩

def tm39 : Term :=
  (.add (.mul (.const 200) tm36) (.const 0))

def f300 : Formula :=
  .and f0 f158

def sq73 : Sequent := ⟨f300, f245⟩

def f301 : Formula :=
  .and f0 f10

def sq74 : Sequent := ⟨f301, f245⟩

def tm40 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (55154253/882769)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2072802757/812154)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3756429173/722706)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-158178970/995423)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-485/416454)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14408723/990083)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1372247321/745893)) (.idx (.var 2) 0)) (.add (.mul (.const (11506710/356519)) (.idx (.var 2) 1)) (.add (.mul (.const (217098311/435678)) (.idx (.var 2) 2)) (.const (-123109784/697985))))))))))) (.sub (.const 1) (.const 1))))

def f302 : Formula :=
  .atom .le tm40 (.const 0)

def sq75 : Sequent := ⟨f301, f302⟩

def sq76 : Sequent := ⟨f301, f0⟩

def sq77 : Sequent := ⟨f301, f301⟩

def tm41 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (55154253/882769)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2072802757/812154)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3756429173/722706)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-158178970/995423)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-485/416454)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14408723/990083)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1372247321/745893)) (.idx (.var 2) 0)) (.add (.mul (.const (11506710/356519)) (.idx (.var 2) 1)) (.add (.mul (.const (217098311/435678)) (.idx (.var 2) 2)) (.const (-123109784/697985))))))))))) (.sub tm0 (.const 1))))

def f303 : Formula :=
  .atom .le tm41 (.const 0)

def sq78 : Sequent := ⟨f301, f303⟩

def sq79 : Sequent := ⟨f301, f10⟩

def tm42 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (55154253/882769)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2072802757/812154)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3756429173/722706)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-158178970/995423)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-485/416454)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14408723/990083)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1372247321/745893)) (.idx (.var 2) 0)) (.add (.mul (.const (11506710/356519)) (.idx (.var 2) 1)) (.add (.mul (.const (217098311/435678)) (.idx (.var 2) 2)) (.const (-123109784/697985))))))))))) (.sub (.var 3) (.const 1))))

def f304 : Formula :=
  .atom .le tm42 (.const 0)

def f305 : Formula :=
  .and f301 f302

def sq80 : Sequent := ⟨f305, f245⟩

def tm43 : Term :=
  (.add (.mul (.const 200) tm40) (.const 0))

def f306 : Formula :=
  .and f0 f157

def sq81 : Sequent := ⟨f306, f245⟩

def f307 : Formula :=
  .and f0 f11

def sq82 : Sequent := ⟨f307, f245⟩

def tm44 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-350575799611/545096)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-80669161475/353076)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (241229922970/519969)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143648843059/877496)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (37996533573/168710)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (2316527722/680683)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (447527991514/583177)) (.idx (.var 2) 0)) (.add (.mul (.const (-369260099359/685667)) (.idx (.var 2) 1)) (.add (.mul (.const (-151341969345/844541)) (.idx (.var 2) 2)) (.const (138463310189/433593))))))))))) (.sub (.const 1) (.const 1))))

def f308 : Formula :=
  .atom .le tm44 (.const 0)

def sq83 : Sequent := ⟨f307, f308⟩

def sq84 : Sequent := ⟨f307, f0⟩

def sq85 : Sequent := ⟨f307, f307⟩

def tm45 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-350575799611/545096)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-80669161475/353076)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (241229922970/519969)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143648843059/877496)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (37996533573/168710)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (2316527722/680683)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (447527991514/583177)) (.idx (.var 2) 0)) (.add (.mul (.const (-369260099359/685667)) (.idx (.var 2) 1)) (.add (.mul (.const (-151341969345/844541)) (.idx (.var 2) 2)) (.const (138463310189/433593))))))))))) (.sub tm0 (.const 1))))

def f309 : Formula :=
  .atom .le tm45 (.const 0)

def sq86 : Sequent := ⟨f307, f309⟩

def sq87 : Sequent := ⟨f307, f11⟩

def tm46 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-350575799611/545096)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-80669161475/353076)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (241229922970/519969)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (143648843059/877496)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (37996533573/168710)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (2316527722/680683)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (447527991514/583177)) (.idx (.var 2) 0)) (.add (.mul (.const (-369260099359/685667)) (.idx (.var 2) 1)) (.add (.mul (.const (-151341969345/844541)) (.idx (.var 2) 2)) (.const (138463310189/433593))))))))))) (.sub (.var 3) (.const 1))))

def f310 : Formula :=
  .atom .le tm46 (.const 0)

def f311 : Formula :=
  .and f307 f308

def sq88 : Sequent := ⟨f311, f245⟩

def tm47 : Term :=
  (.add (.mul (.const 200) tm44) (.const 0))

def f312 : Formula :=
  .and f0 f156

def sq89 : Sequent := ⟨f312, f245⟩

def f313 : Formula :=
  .and f0 f12

def sq90 : Sequent := ⟨f313, f245⟩

def tm48 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3990971/4146)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (355529162/553551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (7983743/212923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1432045696/269489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4827677269/609540)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (5409964/245493)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (586615327/753002)) (.idx (.var 2) 0)) (.add (.mul (.const (-8785147948/608025)) (.idx (.var 2) 1)) (.add (.mul (.const (1471532351/270671)) (.idx (.var 2) 2)) (.const (5501321105/847548))))))))))) (.sub (.const 1) (.const 1))))

def f314 : Formula :=
  .atom .le tm48 (.const 0)

def sq91 : Sequent := ⟨f313, f314⟩

def sq92 : Sequent := ⟨f313, f0⟩

def sq93 : Sequent := ⟨f313, f313⟩

def tm49 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3990971/4146)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (355529162/553551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (7983743/212923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1432045696/269489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4827677269/609540)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (5409964/245493)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (586615327/753002)) (.idx (.var 2) 0)) (.add (.mul (.const (-8785147948/608025)) (.idx (.var 2) 1)) (.add (.mul (.const (1471532351/270671)) (.idx (.var 2) 2)) (.const (5501321105/847548))))))))))) (.sub tm0 (.const 1))))

def f315 : Formula :=
  .atom .le tm49 (.const 0)

def sq94 : Sequent := ⟨f313, f315⟩

def sq95 : Sequent := ⟨f313, f12⟩

def tm50 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3990971/4146)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (355529162/553551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (7983743/212923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1432045696/269489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4827677269/609540)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (5409964/245493)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (586615327/753002)) (.idx (.var 2) 0)) (.add (.mul (.const (-8785147948/608025)) (.idx (.var 2) 1)) (.add (.mul (.const (1471532351/270671)) (.idx (.var 2) 2)) (.const (5501321105/847548))))))))))) (.sub (.var 3) (.const 1))))

def f316 : Formula :=
  .atom .le tm50 (.const 0)

def f317 : Formula :=
  .and f313 f314

def sq96 : Sequent := ⟨f317, f245⟩

def tm51 : Term :=
  (.add (.mul (.const 200) tm48) (.const 0))

def f318 : Formula :=
  .and f0 f155

def sq97 : Sequent := ⟨f318, f245⟩

def f319 : Formula :=
  .and f0 f13

def sq98 : Sequent := ⟨f319, f245⟩

def tm52 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (19936781679/977713)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 2000) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-26672240465/962991)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-800450/27)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-232/782197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18827473549/787707)) (.idx (.var 2) 0)) (.add (.mul (.const (2925414304/848697)) (.idx (.var 2) 1)) (.add (.mul (.const (7733075834/259295)) (.idx (.var 2) 2)) (.const (-1257259559/352964))))))))))) (.sub (.const 1) (.const 1))))

def f320 : Formula :=
  .atom .le tm52 (.const 0)

def sq99 : Sequent := ⟨f319, f320⟩

def sq100 : Sequent := ⟨f319, f0⟩

def sq101 : Sequent := ⟨f319, f319⟩

def tm53 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (19936781679/977713)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 2000) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-26672240465/962991)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-800450/27)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-232/782197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18827473549/787707)) (.idx (.var 2) 0)) (.add (.mul (.const (2925414304/848697)) (.idx (.var 2) 1)) (.add (.mul (.const (7733075834/259295)) (.idx (.var 2) 2)) (.const (-1257259559/352964))))))))))) (.sub tm0 (.const 1))))

def f321 : Formula :=
  .atom .le tm53 (.const 0)

def sq102 : Sequent := ⟨f319, f321⟩

def sq103 : Sequent := ⟨f319, f13⟩

def tm54 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (19936781679/977713)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 2000) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-26672240465/962991)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-800450/27)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-232/782197)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18827473549/787707)) (.idx (.var 2) 0)) (.add (.mul (.const (2925414304/848697)) (.idx (.var 2) 1)) (.add (.mul (.const (7733075834/259295)) (.idx (.var 2) 2)) (.const (-1257259559/352964))))))))))) (.sub (.var 3) (.const 1))))

def f322 : Formula :=
  .atom .le tm54 (.const 0)

def f323 : Formula :=
  .and f319 f320

def sq104 : Sequent := ⟨f323, f245⟩

def tm55 : Term :=
  (.add (.mul (.const 200) tm52) (.const 0))

def f324 : Formula :=
  .and f0 f154

def sq105 : Sequent := ⟨f324, f245⟩

def f325 : Formula :=
  .and f0 f14

def sq106 : Sequent := ⟨f325, f245⟩

def tm56 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62531980308/894377)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (49939872463/478353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-9181042375/890222)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32410263702/485911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (14866167037/298669)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (318492445/716608)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29493773850/556439)) (.idx (.var 2) 0)) (.add (.mul (.const (-67402436368/718353)) (.idx (.var 2) 1)) (.add (.mul (.const (31082153840/426071)) (.idx (.var 2) 2)) (.const (20934869905/486078))))))))))) (.sub (.const 1) (.const 1))))

def f326 : Formula :=
  .atom .le tm56 (.const 0)

def sq107 : Sequent := ⟨f325, f326⟩

def sq108 : Sequent := ⟨f325, f0⟩

def sq109 : Sequent := ⟨f325, f325⟩

def tm57 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62531980308/894377)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (49939872463/478353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-9181042375/890222)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32410263702/485911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (14866167037/298669)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (318492445/716608)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29493773850/556439)) (.idx (.var 2) 0)) (.add (.mul (.const (-67402436368/718353)) (.idx (.var 2) 1)) (.add (.mul (.const (31082153840/426071)) (.idx (.var 2) 2)) (.const (20934869905/486078))))))))))) (.sub tm0 (.const 1))))

def f327 : Formula :=
  .atom .le tm57 (.const 0)

def sq110 : Sequent := ⟨f325, f327⟩

def sq111 : Sequent := ⟨f325, f14⟩

def tm58 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-62531980308/894377)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (49939872463/478353)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-9181042375/890222)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32410263702/485911)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (14866167037/298669)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (318492445/716608)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29493773850/556439)) (.idx (.var 2) 0)) (.add (.mul (.const (-67402436368/718353)) (.idx (.var 2) 1)) (.add (.mul (.const (31082153840/426071)) (.idx (.var 2) 2)) (.const (20934869905/486078))))))))))) (.sub (.var 3) (.const 1))))

def f328 : Formula :=
  .atom .le tm58 (.const 0)

def f329 : Formula :=
  .and f325 f326

def sq112 : Sequent := ⟨f329, f245⟩

def tm59 : Term :=
  (.add (.mul (.const 200) tm56) (.const 0))

def f330 : Formula :=
  .and f0 f153

def sq113 : Sequent := ⟨f330, f245⟩

def f331 : Formula :=
  .and f0 f15

def sq114 : Sequent := ⟨f331, f245⟩

def tm60 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-92821428/906901)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (226746723/213089)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-47820235/550661)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-102544458/391415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (119698290/956143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-153002401/201293)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6998408/795655)) (.idx (.var 2) 0)) (.add (.mul (.const (-195680667/886777)) (.idx (.var 2) 1)) (.add (.mul (.const (440387416/892959)) (.idx (.var 2) 2)) (.const (538793/6669))))))))))) (.sub (.const 1) (.const 1))))

def f332 : Formula :=
  .atom .le tm60 (.const 0)

def sq115 : Sequent := ⟨f331, f332⟩

def sq116 : Sequent := ⟨f331, f0⟩

def sq117 : Sequent := ⟨f331, f331⟩

def tm61 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-92821428/906901)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (226746723/213089)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-47820235/550661)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-102544458/391415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (119698290/956143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-153002401/201293)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6998408/795655)) (.idx (.var 2) 0)) (.add (.mul (.const (-195680667/886777)) (.idx (.var 2) 1)) (.add (.mul (.const (440387416/892959)) (.idx (.var 2) 2)) (.const (538793/6669))))))))))) (.sub tm0 (.const 1))))

def f333 : Formula :=
  .atom .le tm61 (.const 0)

def sq118 : Sequent := ⟨f331, f333⟩

def sq119 : Sequent := ⟨f331, f15⟩

def tm62 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-92821428/906901)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (226746723/213089)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-47820235/550661)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-102544458/391415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (119698290/956143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-153002401/201293)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6998408/795655)) (.idx (.var 2) 0)) (.add (.mul (.const (-195680667/886777)) (.idx (.var 2) 1)) (.add (.mul (.const (440387416/892959)) (.idx (.var 2) 2)) (.const (538793/6669))))))))))) (.sub (.var 3) (.const 1))))

def f334 : Formula :=
  .atom .le tm62 (.const 0)

def f335 : Formula :=
  .and f331 f332

def sq120 : Sequent := ⟨f335, f245⟩

def tm63 : Term :=
  (.add (.mul (.const 200) tm60) (.const 0))

def f336 : Formula :=
  .and f0 f152

def sq121 : Sequent := ⟨f336, f245⟩

def f337 : Formula :=
  .and f0 f16

def sq122 : Sequent := ⟨f337, f245⟩

def tm64 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (30247926/699179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (670643653/925839)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-674895137/905871)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6198819/954686)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-185528/406251)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5474266/437389)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-278073451/949630)) (.idx (.var 2) 0)) (.add (.mul (.const (1887293/349731)) (.idx (.var 2) 1)) (.add (.mul (.const (76280055/733006)) (.idx (.var 2) 2)) (.const (-15110341/602482))))))))))) (.sub (.const 1) (.const 1))))

def f338 : Formula :=
  .atom .le tm64 (.const 0)

def sq123 : Sequent := ⟨f337, f338⟩

def sq124 : Sequent := ⟨f337, f0⟩

def sq125 : Sequent := ⟨f337, f337⟩

def tm65 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (30247926/699179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (670643653/925839)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-674895137/905871)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6198819/954686)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-185528/406251)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5474266/437389)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-278073451/949630)) (.idx (.var 2) 0)) (.add (.mul (.const (1887293/349731)) (.idx (.var 2) 1)) (.add (.mul (.const (76280055/733006)) (.idx (.var 2) 2)) (.const (-15110341/602482))))))))))) (.sub tm0 (.const 1))))

def f339 : Formula :=
  .atom .le tm65 (.const 0)

def sq126 : Sequent := ⟨f337, f339⟩

def sq127 : Sequent := ⟨f337, f16⟩

def tm66 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (30247926/699179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (670643653/925839)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-674895137/905871)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6198819/954686)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-185528/406251)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5474266/437389)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-278073451/949630)) (.idx (.var 2) 0)) (.add (.mul (.const (1887293/349731)) (.idx (.var 2) 1)) (.add (.mul (.const (76280055/733006)) (.idx (.var 2) 2)) (.const (-15110341/602482))))))))))) (.sub (.var 3) (.const 1))))

def f340 : Formula :=
  .atom .le tm66 (.const 0)

def f341 : Formula :=
  .and f337 f338

def sq128 : Sequent := ⟨f341, f245⟩

def tm67 : Term :=
  (.add (.mul (.const 200) tm64) (.const 0))

def f342 : Formula :=
  .and f0 f151

def sq129 : Sequent := ⟨f342, f245⟩

def f343 : Formula :=
  .and f0 f17

def sq130 : Sequent := ⟨f343, f245⟩

def tm68 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (5547829677/918808)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (189938502185/762371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-68088409601/791753)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-92633733706/762047)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (32479817948/756535)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-77630700884/908571)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-46186518421/859372)) (.idx (.var 2) 0)) (.add (.mul (.const (-60159737152/893295)) (.idx (.var 2) 1)) (.add (.mul (.const (27554084527/169814)) (.idx (.var 2) 2)) (.const (7447646741/373870))))))))))) (.sub (.const 1) (.const 1))))

def f344 : Formula :=
  .atom .le tm68 (.const 0)

def sq131 : Sequent := ⟨f343, f344⟩

def sq132 : Sequent := ⟨f343, f0⟩

def sq133 : Sequent := ⟨f343, f343⟩

def tm69 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (5547829677/918808)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (189938502185/762371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-68088409601/791753)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-92633733706/762047)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (32479817948/756535)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-77630700884/908571)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-46186518421/859372)) (.idx (.var 2) 0)) (.add (.mul (.const (-60159737152/893295)) (.idx (.var 2) 1)) (.add (.mul (.const (27554084527/169814)) (.idx (.var 2) 2)) (.const (7447646741/373870))))))))))) (.sub tm0 (.const 1))))

def f345 : Formula :=
  .atom .le tm69 (.const 0)

def sq134 : Sequent := ⟨f343, f345⟩

def sq135 : Sequent := ⟨f343, f17⟩

def tm70 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (5547829677/918808)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (189938502185/762371)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-68088409601/791753)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-92633733706/762047)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (32479817948/756535)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-77630700884/908571)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-46186518421/859372)) (.idx (.var 2) 0)) (.add (.mul (.const (-60159737152/893295)) (.idx (.var 2) 1)) (.add (.mul (.const (27554084527/169814)) (.idx (.var 2) 2)) (.const (7447646741/373870))))))))))) (.sub (.var 3) (.const 1))))

def f346 : Formula :=
  .atom .le tm70 (.const 0)

def f347 : Formula :=
  .and f343 f344

def sq136 : Sequent := ⟨f347, f245⟩

def tm71 : Term :=
  (.add (.mul (.const 200) tm68) (.const 0))

def f348 : Formula :=
  .and f0 f150

def sq137 : Sequent := ⟨f348, f245⟩

def f349 : Formula :=
  .and f0 f18

def sq138 : Sequent := ⟨f349, f245⟩

def tm72 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (32689153/222478)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1257466524/946997)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5206126/95843)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1942969343/864875)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2075789949/210845)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14626978853/915436)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-90740887/248065)) (.idx (.var 2) 0)) (.add (.mul (.const (-13518584450/695991)) (.idx (.var 2) 1)) (.add (.mul (.const (1304563110/180197)) (.idx (.var 2) 2)) (.const (9101846802/990613))))))))))) (.sub (.const 1) (.const 1))))

def f350 : Formula :=
  .atom .le tm72 (.const 0)

def sq139 : Sequent := ⟨f349, f350⟩

def sq140 : Sequent := ⟨f349, f0⟩

def sq141 : Sequent := ⟨f349, f349⟩

def tm73 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (32689153/222478)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1257466524/946997)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5206126/95843)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1942969343/864875)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2075789949/210845)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14626978853/915436)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-90740887/248065)) (.idx (.var 2) 0)) (.add (.mul (.const (-13518584450/695991)) (.idx (.var 2) 1)) (.add (.mul (.const (1304563110/180197)) (.idx (.var 2) 2)) (.const (9101846802/990613))))))))))) (.sub tm0 (.const 1))))

def f351 : Formula :=
  .atom .le tm73 (.const 0)

def sq142 : Sequent := ⟨f349, f351⟩

def sq143 : Sequent := ⟨f349, f18⟩

def tm74 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (32689153/222478)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1257466524/946997)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-5206126/95843)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1942969343/864875)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2075789949/210845)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-14626978853/915436)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-90740887/248065)) (.idx (.var 2) 0)) (.add (.mul (.const (-13518584450/695991)) (.idx (.var 2) 1)) (.add (.mul (.const (1304563110/180197)) (.idx (.var 2) 2)) (.const (9101846802/990613))))))))))) (.sub (.var 3) (.const 1))))

def f352 : Formula :=
  .atom .le tm74 (.const 0)

def f353 : Formula :=
  .and f349 f350

def sq144 : Sequent := ⟨f353, f245⟩

def tm75 : Term :=
  (.add (.mul (.const 200) tm72) (.const 0))

def f354 : Formula :=
  .and f0 f149

def sq145 : Sequent := ⟨f354, f245⟩

def f355 : Formula :=
  .and f0 f19

def sq146 : Sequent := ⟨f355, f245⟩

def tm76 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8431321958/308175)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10686554/783027)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19527628087/525519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13539353/903639)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-63578/690217)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1896826/973033)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19664193399/617074)) (.idx (.var 2) 0)) (.add (.mul (.const (1192876099/726770)) (.idx (.var 2) 1)) (.add (.mul (.const (-7977388/539137)) (.idx (.var 2) 2)) (.const (-1430932853/804812))))))))))) (.sub (.const 1) (.const 1))))

def f356 : Formula :=
  .atom .le tm76 (.const 0)

def sq147 : Sequent := ⟨f355, f356⟩

def sq148 : Sequent := ⟨f355, f0⟩

def sq149 : Sequent := ⟨f355, f355⟩

def tm77 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8431321958/308175)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10686554/783027)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19527628087/525519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13539353/903639)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-63578/690217)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1896826/973033)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19664193399/617074)) (.idx (.var 2) 0)) (.add (.mul (.const (1192876099/726770)) (.idx (.var 2) 1)) (.add (.mul (.const (-7977388/539137)) (.idx (.var 2) 2)) (.const (-1430932853/804812))))))))))) (.sub tm0 (.const 1))))

def f357 : Formula :=
  .atom .le tm77 (.const 0)

def sq150 : Sequent := ⟨f355, f357⟩

def sq151 : Sequent := ⟨f355, f19⟩

def tm78 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8431321958/308175)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10686554/783027)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19527628087/525519)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13539353/903639)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-63578/690217)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1896826/973033)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-19664193399/617074)) (.idx (.var 2) 0)) (.add (.mul (.const (1192876099/726770)) (.idx (.var 2) 1)) (.add (.mul (.const (-7977388/539137)) (.idx (.var 2) 2)) (.const (-1430932853/804812))))))))))) (.sub (.var 3) (.const 1))))

def f358 : Formula :=
  .atom .le tm78 (.const 0)

def f359 : Formula :=
  .and f355 f356

def sq152 : Sequent := ⟨f359, f245⟩

def tm79 : Term :=
  (.add (.mul (.const 200) tm76) (.const 0))

def f360 : Formula :=
  .and f0 f148

def sq153 : Sequent := ⟨f360, f245⟩

def f361 : Formula :=
  .and f0 f20

def sq154 : Sequent := ⟨f361, f245⟩

def tm80 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-23587662574/730379)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (25855184564/376197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3533332711/140729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-20927350204/705901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6241199043/283892)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (433462667/975291)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (15593259935/647203)) (.idx (.var 2) 0)) (.add (.mul (.const (-36834379646/842455)) (.idx (.var 2) 1)) (.add (.mul (.const (7909347134/234305)) (.idx (.var 2) 2)) (.const (17417594093/816382))))))))))) (.sub (.const 1) (.const 1))))

def f362 : Formula :=
  .atom .le tm80 (.const 0)

def sq155 : Sequent := ⟨f361, f362⟩

def sq156 : Sequent := ⟨f361, f0⟩

def sq157 : Sequent := ⟨f361, f361⟩

def tm81 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-23587662574/730379)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (25855184564/376197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3533332711/140729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-20927350204/705901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6241199043/283892)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (433462667/975291)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (15593259935/647203)) (.idx (.var 2) 0)) (.add (.mul (.const (-36834379646/842455)) (.idx (.var 2) 1)) (.add (.mul (.const (7909347134/234305)) (.idx (.var 2) 2)) (.const (17417594093/816382))))))))))) (.sub tm0 (.const 1))))

def f363 : Formula :=
  .atom .le tm81 (.const 0)

def sq158 : Sequent := ⟨f361, f363⟩

def sq159 : Sequent := ⟨f361, f20⟩

def tm82 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-23587662574/730379)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (25855184564/376197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-3533332711/140729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-20927350204/705901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (6241199043/283892)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (433462667/975291)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (15593259935/647203)) (.idx (.var 2) 0)) (.add (.mul (.const (-36834379646/842455)) (.idx (.var 2) 1)) (.add (.mul (.const (7909347134/234305)) (.idx (.var 2) 2)) (.const (17417594093/816382))))))))))) (.sub (.var 3) (.const 1))))

def f364 : Formula :=
  .atom .le tm82 (.const 0)

def f365 : Formula :=
  .and f361 f362

def sq160 : Sequent := ⟨f365, f245⟩

def tm83 : Term :=
  (.add (.mul (.const 200) tm80) (.const 0))

def f366 : Formula :=
  .and f0 f147

def sq161 : Sequent := ⟨f366, f245⟩

def f367 : Formula :=
  .and f0 f21

def sq162 : Sequent := ⟨f367, f245⟩

def tm84 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77122743/987872)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (60120755/615886)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-167080687/869283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-19108601/331186)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (29440741/177267)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1450540/642739)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (16023601/733138)) (.idx (.var 2) 0)) (.add (.mul (.const (-294282997/943667)) (.idx (.var 2) 1)) (.add (.mul (.const (55317695/851699)) (.idx (.var 2) 2)) (.const (139716427/977094))))))))))) (.sub (.const 1) (.const 1))))

def f368 : Formula :=
  .atom .le tm84 (.const 0)

def sq163 : Sequent := ⟨f367, f368⟩

def sq164 : Sequent := ⟨f367, f0⟩

def sq165 : Sequent := ⟨f367, f367⟩

def tm85 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77122743/987872)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (60120755/615886)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-167080687/869283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-19108601/331186)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (29440741/177267)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1450540/642739)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (16023601/733138)) (.idx (.var 2) 0)) (.add (.mul (.const (-294282997/943667)) (.idx (.var 2) 1)) (.add (.mul (.const (55317695/851699)) (.idx (.var 2) 2)) (.const (139716427/977094))))))))))) (.sub tm0 (.const 1))))

def f369 : Formula :=
  .atom .le tm85 (.const 0)

def sq166 : Sequent := ⟨f367, f369⟩

def sq167 : Sequent := ⟨f367, f21⟩

def tm86 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-77122743/987872)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (60120755/615886)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-167080687/869283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-19108601/331186)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (29440741/177267)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1450540/642739)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (16023601/733138)) (.idx (.var 2) 0)) (.add (.mul (.const (-294282997/943667)) (.idx (.var 2) 1)) (.add (.mul (.const (55317695/851699)) (.idx (.var 2) 2)) (.const (139716427/977094))))))))))) (.sub (.var 3) (.const 1))))

def f370 : Formula :=
  .atom .le tm86 (.const 0)

def f371 : Formula :=
  .and f367 f368

def sq168 : Sequent := ⟨f371, f245⟩

def tm87 : Term :=
  (.add (.mul (.const 200) tm84) (.const 0))

def f372 : Formula :=
  .and f0 f146

def sq169 : Sequent := ⟨f372, f245⟩

def f373 : Formula :=
  .and f0 f22

def sq170 : Sequent := ⟨f373, f245⟩

def tm88 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-187559803/934543)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (408704197/397917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-546869426/900239)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-113658313/840825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (96550938/732595)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-74953847/359461)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12925773/991975)) (.idx (.var 2) 0)) (.add (.mul (.const (-155768556/584903)) (.idx (.var 2) 1)) (.add (.mul (.const (118899161/443805)) (.idx (.var 2) 2)) (.const (30222617/249178))))))))))) (.sub (.const 1) (.const 1))))

def f374 : Formula :=
  .atom .le tm88 (.const 0)

def sq171 : Sequent := ⟨f373, f374⟩

def sq172 : Sequent := ⟨f373, f0⟩

def sq173 : Sequent := ⟨f373, f373⟩

def tm89 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-187559803/934543)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (408704197/397917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-546869426/900239)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-113658313/840825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (96550938/732595)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-74953847/359461)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12925773/991975)) (.idx (.var 2) 0)) (.add (.mul (.const (-155768556/584903)) (.idx (.var 2) 1)) (.add (.mul (.const (118899161/443805)) (.idx (.var 2) 2)) (.const (30222617/249178))))))))))) (.sub tm0 (.const 1))))

def f375 : Formula :=
  .atom .le tm89 (.const 0)

def sq174 : Sequent := ⟨f373, f375⟩

def sq175 : Sequent := ⟨f373, f22⟩

def tm90 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-187559803/934543)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (408704197/397917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-546869426/900239)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-113658313/840825)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (96550938/732595)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-74953847/359461)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (12925773/991975)) (.idx (.var 2) 0)) (.add (.mul (.const (-155768556/584903)) (.idx (.var 2) 1)) (.add (.mul (.const (118899161/443805)) (.idx (.var 2) 2)) (.const (30222617/249178))))))))))) (.sub (.var 3) (.const 1))))

def f376 : Formula :=
  .atom .le tm90 (.const 0)

def f377 : Formula :=
  .and f373 f374

def sq176 : Sequent := ⟨f377, f245⟩

def tm91 : Term :=
  (.add (.mul (.const 200) tm88) (.const 0))

def f378 : Formula :=
  .and f0 f145

def sq177 : Sequent := ⟨f378, f245⟩

def f379 : Formula :=
  .and f0 f23

def sq178 : Sequent := ⟨f379, f245⟩

def tm92 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2934709257/149729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (11532613172/286523)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-36020510972/934207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-25346605006/854967)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (805927696/122359)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5579771/595015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-26549887126/973173)) (.idx (.var 2) 0)) (.add (.mul (.const (-9436617985/964342)) (.idx (.var 2) 1)) (.add (.mul (.const (26642029303/829555)) (.idx (.var 2) 2)) (.const (1126887394/392255))))))))))) (.sub (.const 1) (.const 1))))

def f380 : Formula :=
  .atom .le tm92 (.const 0)

def sq179 : Sequent := ⟨f379, f380⟩

def sq180 : Sequent := ⟨f379, f0⟩

def sq181 : Sequent := ⟨f379, f379⟩

def tm93 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2934709257/149729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (11532613172/286523)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-36020510972/934207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-25346605006/854967)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (805927696/122359)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5579771/595015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-26549887126/973173)) (.idx (.var 2) 0)) (.add (.mul (.const (-9436617985/964342)) (.idx (.var 2) 1)) (.add (.mul (.const (26642029303/829555)) (.idx (.var 2) 2)) (.const (1126887394/392255))))))))))) (.sub tm0 (.const 1))))

def f381 : Formula :=
  .atom .le tm93 (.const 0)

def sq182 : Sequent := ⟨f379, f381⟩

def sq183 : Sequent := ⟨f379, f23⟩

def tm94 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2934709257/149729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (11532613172/286523)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-36020510972/934207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-25346605006/854967)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (805927696/122359)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5579771/595015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-26549887126/973173)) (.idx (.var 2) 0)) (.add (.mul (.const (-9436617985/964342)) (.idx (.var 2) 1)) (.add (.mul (.const (26642029303/829555)) (.idx (.var 2) 2)) (.const (1126887394/392255))))))))))) (.sub (.var 3) (.const 1))))

def f382 : Formula :=
  .atom .le tm94 (.const 0)

def f383 : Formula :=
  .and f379 f380

def sq184 : Sequent := ⟨f383, f245⟩

def tm95 : Term :=
  (.add (.mul (.const 200) tm92) (.const 0))

def f384 : Formula :=
  .and f0 f144

def sq185 : Sequent := ⟨f384, f245⟩

def f385 : Formula :=
  .and f0 f24

def sq186 : Sequent := ⟨f385, f245⟩

def tm96 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (1072498623/872611)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-222450157/323534)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-95973927/834859)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6434598356/845689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (7372267831/590097)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-7310852790/566579)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-24303339/20027)) (.idx (.var 2) 0)) (.add (.mul (.const (-3477216809/142717)) (.idx (.var 2) 1)) (.add (.mul (.const (3727945191/390103)) (.idx (.var 2) 2)) (.const (1330611578/112803))))))))))) (.sub (.const 1) (.const 1))))

def f386 : Formula :=
  .atom .le tm96 (.const 0)

def sq187 : Sequent := ⟨f385, f386⟩

def sq188 : Sequent := ⟨f385, f0⟩

def sq189 : Sequent := ⟨f385, f385⟩

def tm97 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (1072498623/872611)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-222450157/323534)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-95973927/834859)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6434598356/845689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (7372267831/590097)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-7310852790/566579)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-24303339/20027)) (.idx (.var 2) 0)) (.add (.mul (.const (-3477216809/142717)) (.idx (.var 2) 1)) (.add (.mul (.const (3727945191/390103)) (.idx (.var 2) 2)) (.const (1330611578/112803))))))))))) (.sub tm0 (.const 1))))

def f387 : Formula :=
  .atom .le tm97 (.const 0)

def sq190 : Sequent := ⟨f385, f387⟩

def sq191 : Sequent := ⟨f385, f24⟩

def tm98 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (1072498623/872611)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-222450157/323534)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-95973927/834859)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-6434598356/845689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (7372267831/590097)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-7310852790/566579)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-24303339/20027)) (.idx (.var 2) 0)) (.add (.mul (.const (-3477216809/142717)) (.idx (.var 2) 1)) (.add (.mul (.const (3727945191/390103)) (.idx (.var 2) 2)) (.const (1330611578/112803))))))))))) (.sub (.var 3) (.const 1))))

def f388 : Formula :=
  .atom .le tm98 (.const 0)

def f389 : Formula :=
  .and f385 f386

def sq192 : Sequent := ⟨f389, f245⟩

def tm99 : Term :=
  (.add (.mul (.const 200) tm96) (.const 0))

def f390 : Formula :=
  .and f0 f143

def sq193 : Sequent := ⟨f390, f245⟩

def f391 : Formula :=
  .and f0 f25

def sq194 : Sequent := ⟨f391, f245⟩

def tm100 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2507690293/253657)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1506280576/258631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (16027755568/805359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1502289633/903902)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (362619249/243100)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (11679719032/955813)) (.idx (.var 2) 0)) (.add (.mul (.const (-370418327/104207)) (.idx (.var 2) 1)) (.add (.mul (.const (1345580471/673425)) (.idx (.var 2) 2)) (.const (1128666227/529562))))))))))) (.sub (.const 1) (.const 1))))

def f392 : Formula :=
  .atom .le tm100 (.const 0)

def sq195 : Sequent := ⟨f391, f392⟩

def sq196 : Sequent := ⟨f391, f0⟩

def sq197 : Sequent := ⟨f391, f391⟩

def tm101 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2507690293/253657)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1506280576/258631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (16027755568/805359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1502289633/903902)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (362619249/243100)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (11679719032/955813)) (.idx (.var 2) 0)) (.add (.mul (.const (-370418327/104207)) (.idx (.var 2) 1)) (.add (.mul (.const (1345580471/673425)) (.idx (.var 2) 2)) (.const (1128666227/529562))))))))))) (.sub tm0 (.const 1))))

def f393 : Formula :=
  .atom .le tm101 (.const 0)

def sq198 : Sequent := ⟨f391, f393⟩

def sq199 : Sequent := ⟨f391, f25⟩

def tm102 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2507690293/253657)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1506280576/258631)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (16027755568/805359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1502289633/903902)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (362619249/243100)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (11679719032/955813)) (.idx (.var 2) 0)) (.add (.mul (.const (-370418327/104207)) (.idx (.var 2) 1)) (.add (.mul (.const (1345580471/673425)) (.idx (.var 2) 2)) (.const (1128666227/529562))))))))))) (.sub (.var 3) (.const 1))))

def f394 : Formula :=
  .atom .le tm102 (.const 0)

def f395 : Formula :=
  .and f391 f392

def sq200 : Sequent := ⟨f395, f245⟩

def tm103 : Term :=
  (.add (.mul (.const 200) tm100) (.const 0))

def f396 : Formula :=
  .and f0 f142

def sq201 : Sequent := ⟨f396, f245⟩

def f397 : Formula :=
  .and f0 f26

def sq202 : Sequent := ⟨f397, f245⟩

def tm104 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1982291646/225469)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (28922746142/791077)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4684300621/677128)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4643688889/626898)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4211740351/819386)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3179555539/402049)) (.idx (.var 2) 0)) (.add (.mul (.const (-486790284/922805)) (.idx (.var 2) 1)) (.add (.mul (.const (-4993824905/955378)) (.idx (.var 2) 2)) (.const (220360892/441245)))))))))) (.sub (.const 1) (.const 1))))

def f398 : Formula :=
  .atom .le tm104 (.const 0)

def sq203 : Sequent := ⟨f397, f398⟩

def sq204 : Sequent := ⟨f397, f0⟩

def sq205 : Sequent := ⟨f397, f397⟩

def tm105 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1982291646/225469)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (28922746142/791077)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4684300621/677128)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4643688889/626898)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4211740351/819386)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3179555539/402049)) (.idx (.var 2) 0)) (.add (.mul (.const (-486790284/922805)) (.idx (.var 2) 1)) (.add (.mul (.const (-4993824905/955378)) (.idx (.var 2) 2)) (.const (220360892/441245)))))))))) (.sub tm0 (.const 1))))

def f399 : Formula :=
  .atom .le tm105 (.const 0)

def sq206 : Sequent := ⟨f397, f399⟩

def sq207 : Sequent := ⟨f397, f26⟩

def tm106 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1982291646/225469)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (28922746142/791077)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4684300621/677128)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4643688889/626898)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4211740351/819386)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3179555539/402049)) (.idx (.var 2) 0)) (.add (.mul (.const (-486790284/922805)) (.idx (.var 2) 1)) (.add (.mul (.const (-4993824905/955378)) (.idx (.var 2) 2)) (.const (220360892/441245)))))))))) (.sub (.var 3) (.const 1))))

def f400 : Formula :=
  .atom .le tm106 (.const 0)

def f401 : Formula :=
  .and f397 f398

def sq208 : Sequent := ⟨f401, f245⟩

def tm107 : Term :=
  (.add (.mul (.const 200) tm104) (.const 0))

def f402 : Formula :=
  .and f0 f141

def sq209 : Sequent := ⟨f402, f245⟩

def f403 : Formula :=
  .and f0 f27

def sq210 : Sequent := ⟨f403, f245⟩

def tm108 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4958510859/518810)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-114209812/383465)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109730475/938971)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3760133704/416199)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (969405709/736125)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24100/401)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1439605849/150983)) (.idx (.var 2) 0)) (.add (.mul (.const (-1698566435/543192)) (.idx (.var 2) 1)) (.add (.mul (.const (-4019262437/443350)) (.idx (.var 2) 2)) (.const (1746813632/966093))))))))))) (.sub (.const 1) (.const 1))))

def f404 : Formula :=
  .atom .le tm108 (.const 0)

def sq211 : Sequent := ⟨f403, f404⟩

def sq212 : Sequent := ⟨f403, f0⟩

def sq213 : Sequent := ⟨f403, f403⟩

def tm109 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4958510859/518810)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-114209812/383465)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109730475/938971)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3760133704/416199)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (969405709/736125)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24100/401)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1439605849/150983)) (.idx (.var 2) 0)) (.add (.mul (.const (-1698566435/543192)) (.idx (.var 2) 1)) (.add (.mul (.const (-4019262437/443350)) (.idx (.var 2) 2)) (.const (1746813632/966093))))))))))) (.sub tm0 (.const 1))))

def f405 : Formula :=
  .atom .le tm109 (.const 0)

def sq214 : Sequent := ⟨f403, f405⟩

def sq215 : Sequent := ⟨f403, f27⟩

def tm110 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4958510859/518810)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-114209812/383465)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109730475/938971)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3760133704/416199)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (969405709/736125)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-24100/401)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1439605849/150983)) (.idx (.var 2) 0)) (.add (.mul (.const (-1698566435/543192)) (.idx (.var 2) 1)) (.add (.mul (.const (-4019262437/443350)) (.idx (.var 2) 2)) (.const (1746813632/966093))))))))))) (.sub (.var 3) (.const 1))))

def f406 : Formula :=
  .atom .le tm110 (.const 0)

def f407 : Formula :=
  .and f403 f404

def sq216 : Sequent := ⟨f407, f245⟩

def tm111 : Term :=
  (.add (.mul (.const 200) tm108) (.const 0))

def f408 : Formula :=
  .and f0 f140

def sq217 : Sequent := ⟨f408, f245⟩

def f409 : Formula :=
  .and f0 f28

def sq218 : Sequent := ⟨f409, f245⟩

def tm112 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1226562698/958373)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1520876471/760255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-575098918/593923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-279012907/529872)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1299462591/986756)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-197698265/473356)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1001262608/902381)) (.idx (.var 2) 0)) (.add (.mul (.const (-2702358466/991107)) (.idx (.var 2) 1)) (.add (.mul (.const (614678163/859823)) (.idx (.var 2) 2)) (.const (705294537/502789))))))))))) (.sub (.const 1) (.const 1))))

def f410 : Formula :=
  .atom .le tm112 (.const 0)

def sq219 : Sequent := ⟨f409, f410⟩

def sq220 : Sequent := ⟨f409, f0⟩

def sq221 : Sequent := ⟨f409, f409⟩

def tm113 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1226562698/958373)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1520876471/760255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-575098918/593923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-279012907/529872)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1299462591/986756)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-197698265/473356)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1001262608/902381)) (.idx (.var 2) 0)) (.add (.mul (.const (-2702358466/991107)) (.idx (.var 2) 1)) (.add (.mul (.const (614678163/859823)) (.idx (.var 2) 2)) (.const (705294537/502789))))))))))) (.sub tm0 (.const 1))))

def f411 : Formula :=
  .atom .le tm113 (.const 0)

def sq222 : Sequent := ⟨f409, f411⟩

def sq223 : Sequent := ⟨f409, f28⟩

def tm114 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1226562698/958373)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1520876471/760255)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-575098918/593923)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-279012907/529872)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1299462591/986756)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-197698265/473356)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1001262608/902381)) (.idx (.var 2) 0)) (.add (.mul (.const (-2702358466/991107)) (.idx (.var 2) 1)) (.add (.mul (.const (614678163/859823)) (.idx (.var 2) 2)) (.const (705294537/502789))))))))))) (.sub (.var 3) (.const 1))))

def f412 : Formula :=
  .atom .le tm114 (.const 0)

def f413 : Formula :=
  .and f409 f410

def sq224 : Sequent := ⟨f413, f245⟩

def tm115 : Term :=
  (.add (.mul (.const 200) tm112) (.const 0))

def f414 : Formula :=
  .and f0 f139

def sq225 : Sequent := ⟨f414, f245⟩

def f415 : Formula :=
  .and f0 f29

def sq226 : Sequent := ⟨f415, f245⟩

def tm116 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-598651246/540513)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-55066526911/693207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (15092044641/787762)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (17546701968/661117)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (49367747258/737891)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2491362893/742980)) (.idx (.var 2) 0)) (.add (.mul (.const (-27275977/410451)) (.idx (.var 2) 1)) (.add (.mul (.const (-19031347915/607631)) (.idx (.var 2) 2)) (.const (16118901/121907)))))))))) (.sub (.const 1) (.const 1))))

def f416 : Formula :=
  .atom .le tm116 (.const 0)

def sq227 : Sequent := ⟨f415, f416⟩

def sq228 : Sequent := ⟨f415, f0⟩

def sq229 : Sequent := ⟨f415, f415⟩

def tm117 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-598651246/540513)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-55066526911/693207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (15092044641/787762)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (17546701968/661117)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (49367747258/737891)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2491362893/742980)) (.idx (.var 2) 0)) (.add (.mul (.const (-27275977/410451)) (.idx (.var 2) 1)) (.add (.mul (.const (-19031347915/607631)) (.idx (.var 2) 2)) (.const (16118901/121907)))))))))) (.sub tm0 (.const 1))))

def f417 : Formula :=
  .atom .le tm117 (.const 0)

def sq230 : Sequent := ⟨f415, f417⟩

def sq231 : Sequent := ⟨f415, f29⟩

def tm118 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-598651246/540513)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-55066526911/693207)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (15092044641/787762)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (17546701968/661117)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (49367747258/737891)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2491362893/742980)) (.idx (.var 2) 0)) (.add (.mul (.const (-27275977/410451)) (.idx (.var 2) 1)) (.add (.mul (.const (-19031347915/607631)) (.idx (.var 2) 2)) (.const (16118901/121907)))))))))) (.sub (.var 3) (.const 1))))

def f418 : Formula :=
  .atom .le tm118 (.const 0)

def f419 : Formula :=
  .and f415 f416

def sq232 : Sequent := ⟨f419, f245⟩

def tm119 : Term :=
  (.add (.mul (.const 200) tm116) (.const 0))

def f420 : Formula :=
  .and f0 f138

def sq233 : Sequent := ⟨f420, f245⟩

def f421 : Formula :=
  .and f0 f30

def sq234 : Sequent := ⟨f421, f245⟩

def tm120 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192414529/829491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-264294397/489852)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-143729285/786714)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (623801221/796333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (606393497/803223)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-18850669/556270)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105853379/596422)) (.idx (.var 2) 0)) (.add (.mul (.const (-682951837/463742)) (.idx (.var 2) 1)) (.add (.mul (.const (-442037542/533187)) (.idx (.var 2) 2)) (.const (649997192/909121))))))))))) (.sub (.const 1) (.const 1))))

def f422 : Formula :=
  .atom .le tm120 (.const 0)

def sq235 : Sequent := ⟨f421, f422⟩

def sq236 : Sequent := ⟨f421, f0⟩

def sq237 : Sequent := ⟨f421, f421⟩

def tm121 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192414529/829491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-264294397/489852)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-143729285/786714)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (623801221/796333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (606393497/803223)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-18850669/556270)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105853379/596422)) (.idx (.var 2) 0)) (.add (.mul (.const (-682951837/463742)) (.idx (.var 2) 1)) (.add (.mul (.const (-442037542/533187)) (.idx (.var 2) 2)) (.const (649997192/909121))))))))))) (.sub tm0 (.const 1))))

def f423 : Formula :=
  .atom .le tm121 (.const 0)

def sq238 : Sequent := ⟨f421, f423⟩

def sq239 : Sequent := ⟨f421, f30⟩

def tm122 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192414529/829491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-264294397/489852)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-143729285/786714)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (623801221/796333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (606393497/803223)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-18850669/556270)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (105853379/596422)) (.idx (.var 2) 0)) (.add (.mul (.const (-682951837/463742)) (.idx (.var 2) 1)) (.add (.mul (.const (-442037542/533187)) (.idx (.var 2) 2)) (.const (649997192/909121))))))))))) (.sub (.var 3) (.const 1))))

def f424 : Formula :=
  .atom .le tm122 (.const 0)

def f425 : Formula :=
  .and f421 f422

def sq240 : Sequent := ⟨f425, f245⟩

def tm123 : Term :=
  (.add (.mul (.const 200) tm120) (.const 0))

def f426 : Formula :=
  .and f0 f137

def sq241 : Sequent := ⟨f426, f245⟩

def f427 : Formula :=
  .and f0 f31

def sq242 : Sequent := ⟨f427, f245⟩

def tm124 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 2)) (.const 1048576)))))))))) (.sub (.const 1) (.const 1))))

def f428 : Formula :=
  .atom .le tm124 (.const 0)

def sq243 : Sequent := ⟨f427, f428⟩

def sq244 : Sequent := ⟨f427, f0⟩

def sq245 : Sequent := ⟨f427, f427⟩

def tm125 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 2)) (.const 1048576)))))))))) (.sub tm0 (.const 1))))

def f429 : Formula :=
  .atom .le tm125 (.const 0)

def sq246 : Sequent := ⟨f427, f429⟩

def sq247 : Sequent := ⟨f427, f31⟩

def tm126 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1048576)) (.idx (.var 2) 0)) (.add (.mul (.const 1048576) (.idx (.var 2) 1)) (.add (.mul (.const (-1048576)) (.idx (.var 2) 2)) (.const 1048576)))))))))) (.sub (.var 3) (.const 1))))

def f430 : Formula :=
  .atom .le tm126 (.const 0)

def f431 : Formula :=
  .and f427 f428

def sq248 : Sequent := ⟨f431, f245⟩

def tm127 : Term :=
  (.add (.mul (.const 200) tm124) (.const 0))

def f432 : Formula :=
  .and f0 f136

def sq249 : Sequent := ⟨f432, f245⟩

def f433 : Formula :=
  .and f0 f32

def sq250 : Sequent := ⟨f433, f245⟩

def sq251 : Sequent := ⟨f433, f428⟩

def sq252 : Sequent := ⟨f433, f0⟩

def sq253 : Sequent := ⟨f433, f433⟩

def sq254 : Sequent := ⟨f433, f429⟩

def sq255 : Sequent := ⟨f433, f32⟩

def f434 : Formula :=
  .and f433 f428

def sq256 : Sequent := ⟨f434, f245⟩

def f435 : Formula :=
  .and f0 f135

def sq257 : Sequent := ⟨f435, f245⟩

def f436 : Formula :=
  .and f0 f33

def sq258 : Sequent := ⟨f436, f245⟩

def sq259 : Sequent := ⟨f436, f428⟩

def sq260 : Sequent := ⟨f436, f0⟩

def sq261 : Sequent := ⟨f436, f436⟩

def sq262 : Sequent := ⟨f436, f429⟩

def sq263 : Sequent := ⟨f436, f33⟩

def f437 : Formula :=
  .and f436 f428

def sq264 : Sequent := ⟨f437, f245⟩

def f438 : Formula :=
  .and f0 f134

def sq265 : Sequent := ⟨f438, f245⟩

def f439 : Formula :=
  .and f0 f34

def sq266 : Sequent := ⟨f439, f245⟩

def sq267 : Sequent := ⟨f439, f428⟩

def sq268 : Sequent := ⟨f439, f0⟩

def sq269 : Sequent := ⟨f439, f439⟩

def sq270 : Sequent := ⟨f439, f429⟩

def sq271 : Sequent := ⟨f439, f34⟩

def f440 : Formula :=
  .and f439 f428

def sq272 : Sequent := ⟨f440, f245⟩

def f441 : Formula :=
  .and f0 f133

def sq273 : Sequent := ⟨f441, f245⟩

def f442 : Formula :=
  .and f0 f35

def sq274 : Sequent := ⟨f442, f245⟩

def sq275 : Sequent := ⟨f442, f428⟩

def sq276 : Sequent := ⟨f442, f0⟩

def sq277 : Sequent := ⟨f442, f442⟩

def sq278 : Sequent := ⟨f442, f429⟩

def sq279 : Sequent := ⟨f442, f35⟩

def f443 : Formula :=
  .and f442 f428

def sq280 : Sequent := ⟨f443, f245⟩

def f444 : Formula :=
  .and f0 f132

def sq281 : Sequent := ⟨f444, f245⟩

def f445 : Formula :=
  .and f0 f36

def sq282 : Sequent := ⟨f445, f245⟩

def sq283 : Sequent := ⟨f445, f428⟩

def sq284 : Sequent := ⟨f445, f0⟩

def sq285 : Sequent := ⟨f445, f445⟩

def sq286 : Sequent := ⟨f445, f429⟩

def sq287 : Sequent := ⟨f445, f36⟩

def f446 : Formula :=
  .and f445 f428

def sq288 : Sequent := ⟨f446, f245⟩

def f447 : Formula :=
  .and f0 f131

def sq289 : Sequent := ⟨f447, f245⟩

def f448 : Formula :=
  .and f0 f37

def sq290 : Sequent := ⟨f448, f245⟩

def tm128 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9033851688/211739)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-757094619/365527)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-48977394828/885067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1096577150/733171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (623147946/715135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-45924468757/927120)) (.idx (.var 2) 0)) (.add (.mul (.const (332493845/434341)) (.idx (.var 2) 1)) (.add (.mul (.const (300859597/221537)) (.idx (.var 2) 2)) (.const (-12518203/6754))))))))))) (.sub (.const 1) (.const 1))))

def f449 : Formula :=
  .atom .le tm128 (.const 0)

def sq291 : Sequent := ⟨f448, f449⟩

def sq292 : Sequent := ⟨f448, f0⟩

def sq293 : Sequent := ⟨f448, f448⟩

def tm129 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9033851688/211739)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-757094619/365527)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-48977394828/885067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1096577150/733171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (623147946/715135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-45924468757/927120)) (.idx (.var 2) 0)) (.add (.mul (.const (332493845/434341)) (.idx (.var 2) 1)) (.add (.mul (.const (300859597/221537)) (.idx (.var 2) 2)) (.const (-12518203/6754))))))))))) (.sub tm0 (.const 1))))

def f450 : Formula :=
  .atom .le tm129 (.const 0)

def sq294 : Sequent := ⟨f448, f450⟩

def sq295 : Sequent := ⟨f448, f37⟩

def tm130 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9033851688/211739)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-757094619/365527)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-48977394828/885067)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1096577150/733171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (623147946/715135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-45924468757/927120)) (.idx (.var 2) 0)) (.add (.mul (.const (332493845/434341)) (.idx (.var 2) 1)) (.add (.mul (.const (300859597/221537)) (.idx (.var 2) 2)) (.const (-12518203/6754))))))))))) (.sub (.var 3) (.const 1))))

def f451 : Formula :=
  .atom .le tm130 (.const 0)

def f452 : Formula :=
  .and f448 f449

def sq296 : Sequent := ⟨f452, f245⟩

def tm131 : Term :=
  (.add (.mul (.const 200) tm128) (.const 0))

def f453 : Formula :=
  .and f0 f130

def sq297 : Sequent := ⟨f453, f245⟩

def f454 : Formula :=
  .and f0 f38

def sq298 : Sequent := ⟨f454, f245⟩

def tm132 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4136996651/606790)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-131423746463/980165)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109214176249/572644)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (264424084/50003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-107/360755)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (42043531385/798168)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (4770124279/243649)) (.idx (.var 2) 0)) (.add (.mul (.const (-12429511/997804)) (.idx (.var 2) 1)) (.add (.mul (.const (-4824058442/875207)) (.idx (.var 2) 2)) (.const (240967410/631193))))))))))) (.sub (.const 1) (.const 1))))

def f455 : Formula :=
  .atom .le tm132 (.const 0)

def sq299 : Sequent := ⟨f454, f455⟩

def sq300 : Sequent := ⟨f454, f0⟩

def sq301 : Sequent := ⟨f454, f454⟩

def tm133 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4136996651/606790)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-131423746463/980165)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109214176249/572644)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (264424084/50003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-107/360755)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (42043531385/798168)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (4770124279/243649)) (.idx (.var 2) 0)) (.add (.mul (.const (-12429511/997804)) (.idx (.var 2) 1)) (.add (.mul (.const (-4824058442/875207)) (.idx (.var 2) 2)) (.const (240967410/631193))))))))))) (.sub tm0 (.const 1))))

def f456 : Formula :=
  .atom .le tm133 (.const 0)

def sq302 : Sequent := ⟨f454, f456⟩

def sq303 : Sequent := ⟨f454, f38⟩

def tm134 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4136996651/606790)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-131423746463/980165)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (109214176249/572644)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (264424084/50003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-107/360755)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (42043531385/798168)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (4770124279/243649)) (.idx (.var 2) 0)) (.add (.mul (.const (-12429511/997804)) (.idx (.var 2) 1)) (.add (.mul (.const (-4824058442/875207)) (.idx (.var 2) 2)) (.const (240967410/631193))))))))))) (.sub (.var 3) (.const 1))))

def f457 : Formula :=
  .atom .le tm134 (.const 0)

def f458 : Formula :=
  .and f454 f455

def sq304 : Sequent := ⟨f458, f245⟩

def tm135 : Term :=
  (.add (.mul (.const 200) tm132) (.const 0))

def f459 : Formula :=
  .and f0 f129

def sq305 : Sequent := ⟨f459, f245⟩

def f460 : Formula :=
  .and f0 f39

def sq306 : Sequent := ⟨f460, f245⟩

def tm136 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-17297863022/810515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-90160012/670099)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-789382159/595232)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13366471094/603421)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (91362280/557003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (78953262/899327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10106175494/479151)) (.idx (.var 2) 0)) (.add (.mul (.const (103016144/723225)) (.idx (.var 2) 1)) (.add (.mul (.const (-17857840888/805023)) (.idx (.var 2) 2)) (.const (-227424210/712519))))))))))) (.sub (.const 1) (.const 1))))

def f461 : Formula :=
  .atom .le tm136 (.const 0)

def sq307 : Sequent := ⟨f460, f461⟩

def sq308 : Sequent := ⟨f460, f0⟩

def sq309 : Sequent := ⟨f460, f460⟩

def tm137 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-17297863022/810515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-90160012/670099)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-789382159/595232)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13366471094/603421)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (91362280/557003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (78953262/899327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10106175494/479151)) (.idx (.var 2) 0)) (.add (.mul (.const (103016144/723225)) (.idx (.var 2) 1)) (.add (.mul (.const (-17857840888/805023)) (.idx (.var 2) 2)) (.const (-227424210/712519))))))))))) (.sub tm0 (.const 1))))

def f462 : Formula :=
  .atom .le tm137 (.const 0)

def sq310 : Sequent := ⟨f460, f462⟩

def sq311 : Sequent := ⟨f460, f39⟩

def tm138 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-17297863022/810515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-90160012/670099)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-789382159/595232)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13366471094/603421)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (91362280/557003)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (78953262/899327)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10106175494/479151)) (.idx (.var 2) 0)) (.add (.mul (.const (103016144/723225)) (.idx (.var 2) 1)) (.add (.mul (.const (-17857840888/805023)) (.idx (.var 2) 2)) (.const (-227424210/712519))))))))))) (.sub (.var 3) (.const 1))))

def f463 : Formula :=
  .atom .le tm138 (.const 0)

def f464 : Formula :=
  .and f460 f461

def sq312 : Sequent := ⟨f464, f245⟩

def tm139 : Term :=
  (.add (.mul (.const 200) tm136) (.const 0))

def f465 : Formula :=
  .and f0 f128

def sq313 : Sequent := ⟨f465, f245⟩

def f466 : Formula :=
  .and f0 f40

def sq314 : Sequent := ⟨f466, f245⟩

def tm140 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (41848510/246101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-294348826/307625)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (346559657/904055)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-203281103/560415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15583901/37418)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-111723408/588703)) (.idx (.var 2) 0)) (.add (.mul (.const (-13926036/17741)) (.idx (.var 2) 1)) (.add (.mul (.const (202577134/889927)) (.idx (.var 2) 2)) (.const (287062237/798767))))))))))) (.sub (.const 1) (.const 1))))

def f467 : Formula :=
  .atom .le tm140 (.const 0)

def sq315 : Sequent := ⟨f466, f467⟩

def sq316 : Sequent := ⟨f466, f0⟩

def sq317 : Sequent := ⟨f466, f466⟩

def tm141 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (41848510/246101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-294348826/307625)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (346559657/904055)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-203281103/560415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15583901/37418)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-111723408/588703)) (.idx (.var 2) 0)) (.add (.mul (.const (-13926036/17741)) (.idx (.var 2) 1)) (.add (.mul (.const (202577134/889927)) (.idx (.var 2) 2)) (.const (287062237/798767))))))))))) (.sub tm0 (.const 1))))

def f468 : Formula :=
  .atom .le tm141 (.const 0)

def sq318 : Sequent := ⟨f466, f468⟩

def sq319 : Sequent := ⟨f466, f40⟩

def tm142 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (41848510/246101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-294348826/307625)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (346559657/904055)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-203281103/560415)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (15583901/37418)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-111723408/588703)) (.idx (.var 2) 0)) (.add (.mul (.const (-13926036/17741)) (.idx (.var 2) 1)) (.add (.mul (.const (202577134/889927)) (.idx (.var 2) 2)) (.const (287062237/798767))))))))))) (.sub (.var 3) (.const 1))))

def f469 : Formula :=
  .atom .le tm142 (.const 0)

def f470 : Formula :=
  .and f466 f467

def sq320 : Sequent := ⟨f470, f245⟩

def tm143 : Term :=
  (.add (.mul (.const 200) tm140) (.const 0))

def f471 : Formula :=
  .and f0 f127

def sq321 : Sequent := ⟨f471, f245⟩

def f472 : Formula :=
  .and f0 f41

def sq322 : Sequent := ⟨f472, f245⟩

def tm144 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-542305236/759635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-118180995373/549392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (25441467789/499423)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (27664226749/329004)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-10/35491)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (31024204507/608998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4115294327/438892)) (.idx (.var 2) 0)) (.add (.mul (.const (6006945943/959036)) (.idx (.var 2) 1)) (.add (.mul (.const (-32035367281/358217)) (.idx (.var 2) 2)) (.const (-5893528445/870306))))))))))) (.sub (.const 1) (.const 1))))

def f473 : Formula :=
  .atom .le tm144 (.const 0)

def sq323 : Sequent := ⟨f472, f473⟩

def sq324 : Sequent := ⟨f472, f0⟩

def sq325 : Sequent := ⟨f472, f472⟩

def tm145 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-542305236/759635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-118180995373/549392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (25441467789/499423)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (27664226749/329004)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-10/35491)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (31024204507/608998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4115294327/438892)) (.idx (.var 2) 0)) (.add (.mul (.const (6006945943/959036)) (.idx (.var 2) 1)) (.add (.mul (.const (-32035367281/358217)) (.idx (.var 2) 2)) (.const (-5893528445/870306))))))))))) (.sub tm0 (.const 1))))

def f474 : Formula :=
  .atom .le tm145 (.const 0)

def sq326 : Sequent := ⟨f472, f474⟩

def sq327 : Sequent := ⟨f472, f41⟩

def tm146 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-542305236/759635)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-118180995373/549392)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (25441467789/499423)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (27664226749/329004)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-10/35491)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (31024204507/608998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4115294327/438892)) (.idx (.var 2) 0)) (.add (.mul (.const (6006945943/959036)) (.idx (.var 2) 1)) (.add (.mul (.const (-32035367281/358217)) (.idx (.var 2) 2)) (.const (-5893528445/870306))))))))))) (.sub (.var 3) (.const 1))))

def f475 : Formula :=
  .atom .le tm146 (.const 0)

def f476 : Formula :=
  .and f472 f473

def sq328 : Sequent := ⟨f476, f245⟩

def tm147 : Term :=
  (.add (.mul (.const 200) tm144) (.const 0))

def f477 : Formula :=
  .and f0 f126

def sq329 : Sequent := ⟨f477, f245⟩

def f478 : Formula :=
  .and f0 f42

def sq330 : Sequent := ⟨f478, f245⟩

def tm148 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (817081585/749549)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (361863434/300101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-132818599/590075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10189986590/244227)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-423245034/612143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-29676409816/512185)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-991989254/931403)) (.idx (.var 2) 0)) (.add (.mul (.const (1483689422/322063)) (.idx (.var 2) 1)) (.add (.mul (.const (-40756412028/808303)) (.idx (.var 2) 2)) (.const (-4059429397/956258))))))))))) (.sub (.const 1) (.const 1))))

def f479 : Formula :=
  .atom .le tm148 (.const 0)

def sq331 : Sequent := ⟨f478, f479⟩

def sq332 : Sequent := ⟨f478, f0⟩

def sq333 : Sequent := ⟨f478, f478⟩

def tm149 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (817081585/749549)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (361863434/300101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-132818599/590075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10189986590/244227)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-423245034/612143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-29676409816/512185)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-991989254/931403)) (.idx (.var 2) 0)) (.add (.mul (.const (1483689422/322063)) (.idx (.var 2) 1)) (.add (.mul (.const (-40756412028/808303)) (.idx (.var 2) 2)) (.const (-4059429397/956258))))))))))) (.sub tm0 (.const 1))))

def f480 : Formula :=
  .atom .le tm149 (.const 0)

def sq334 : Sequent := ⟨f478, f480⟩

def sq335 : Sequent := ⟨f478, f42⟩

def tm150 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (817081585/749549)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (361863434/300101)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-132818599/590075)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (10189986590/244227)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-423245034/612143)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-29676409816/512185)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-991989254/931403)) (.idx (.var 2) 0)) (.add (.mul (.const (1483689422/322063)) (.idx (.var 2) 1)) (.add (.mul (.const (-40756412028/808303)) (.idx (.var 2) 2)) (.const (-4059429397/956258))))))))))) (.sub (.var 3) (.const 1))))

def f481 : Formula :=
  .atom .le tm150 (.const 0)

def f482 : Formula :=
  .and f478 f479

def sq336 : Sequent := ⟨f482, f245⟩

def tm151 : Term :=
  (.add (.mul (.const 200) tm148) (.const 0))

def f483 : Formula :=
  .and f0 f125

def sq337 : Sequent := ⟨f483, f245⟩

def f484 : Formula :=
  .and f0 f43

def sq338 : Sequent := ⟨f484, f245⟩

def tm152 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (23153020139/385968)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-754849539/286718)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73820669162/994179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2487514839/871156)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2820892540/859601)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18597896753/268011)) (.idx (.var 2) 0)) (.add (.mul (.const (-161762759/51025)) (.idx (.var 2) 1)) (.add (.mul (.const (2226078893/829351)) (.idx (.var 2) 2)) (.const (-374215484/889331))))))))))) (.sub (.const 1) (.const 1))))

def f485 : Formula :=
  .atom .le tm152 (.const 0)

def sq339 : Sequent := ⟨f484, f485⟩

def sq340 : Sequent := ⟨f484, f0⟩

def sq341 : Sequent := ⟨f484, f484⟩

def tm153 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (23153020139/385968)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-754849539/286718)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73820669162/994179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2487514839/871156)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2820892540/859601)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18597896753/268011)) (.idx (.var 2) 0)) (.add (.mul (.const (-161762759/51025)) (.idx (.var 2) 1)) (.add (.mul (.const (2226078893/829351)) (.idx (.var 2) 2)) (.const (-374215484/889331))))))))))) (.sub tm0 (.const 1))))

def f486 : Formula :=
  .atom .le tm153 (.const 0)

def sq342 : Sequent := ⟨f484, f486⟩

def sq343 : Sequent := ⟨f484, f43⟩

def tm154 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (23153020139/385968)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-754849539/286718)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-73820669162/994179)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2487514839/871156)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (2820892540/859601)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-18597896753/268011)) (.idx (.var 2) 0)) (.add (.mul (.const (-161762759/51025)) (.idx (.var 2) 1)) (.add (.mul (.const (2226078893/829351)) (.idx (.var 2) 2)) (.const (-374215484/889331))))))))))) (.sub (.var 3) (.const 1))))

def f487 : Formula :=
  .atom .le tm154 (.const 0)

def f488 : Formula :=
  .and f484 f485

def sq344 : Sequent := ⟨f488, f245⟩

def tm155 : Term :=
  (.add (.mul (.const 200) tm152) (.const 0))

def f489 : Formula :=
  .and f0 f124

def sq345 : Sequent := ⟨f489, f245⟩

def f490 : Formula :=
  .and f0 f44

def sq346 : Sequent := ⟨f490, f245⟩

def tm156 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-9613254787/990245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10015559497/757080)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (4802809513/120425)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4163553241/851546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-569/479602)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1052793/558511)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3889034841/310624)) (.idx (.var 2) 0)) (.add (.mul (.const (69510127/460521)) (.idx (.var 2) 1)) (.add (.mul (.const (-4050647449/712921)) (.idx (.var 2) 2)) (.const (-26204036/208733))))))))))) (.sub (.const 1) (.const 1))))

def f491 : Formula :=
  .atom .le tm156 (.const 0)

def sq347 : Sequent := ⟨f490, f491⟩

def sq348 : Sequent := ⟨f490, f0⟩

def sq349 : Sequent := ⟨f490, f490⟩

def tm157 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-9613254787/990245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10015559497/757080)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (4802809513/120425)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4163553241/851546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-569/479602)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1052793/558511)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3889034841/310624)) (.idx (.var 2) 0)) (.add (.mul (.const (69510127/460521)) (.idx (.var 2) 1)) (.add (.mul (.const (-4050647449/712921)) (.idx (.var 2) 2)) (.const (-26204036/208733))))))))))) (.sub tm0 (.const 1))))

def f492 : Formula :=
  .atom .le tm157 (.const 0)

def sq350 : Sequent := ⟨f490, f492⟩

def sq351 : Sequent := ⟨f490, f44⟩

def tm158 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-9613254787/990245)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-10015559497/757080)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (4802809513/120425)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (4163553241/851546)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-569/479602)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1052793/558511)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3889034841/310624)) (.idx (.var 2) 0)) (.add (.mul (.const (69510127/460521)) (.idx (.var 2) 1)) (.add (.mul (.const (-4050647449/712921)) (.idx (.var 2) 2)) (.const (-26204036/208733))))))))))) (.sub (.var 3) (.const 1))))

def f493 : Formula :=
  .atom .le tm158 (.const 0)

def f494 : Formula :=
  .and f490 f491

def sq352 : Sequent := ⟨f494, f245⟩

def tm159 : Term :=
  (.add (.mul (.const 200) tm156) (.const 0))

def f495 : Formula :=
  .and f0 f123

def sq353 : Sequent := ⟨f495, f245⟩

def f496 : Formula :=
  .and f0 f45

def sq354 : Sequent := ⟨f496, f245⟩

def tm160 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2630071866/42005)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-940419969/602056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (108587651/203036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (31257403638/989647)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (516593311/615689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (28507487821/456546)) (.idx (.var 2) 0)) (.add (.mul (.const (-265535443/533928)) (.idx (.var 2) 1)) (.add (.mul (.const (-7884838487/248091)) (.idx (.var 2) 2)) (.const (-115298402/309891))))))))))) (.sub (.const 1) (.const 1))))

def f497 : Formula :=
  .atom .le tm160 (.const 0)

def sq355 : Sequent := ⟨f496, f497⟩

def sq356 : Sequent := ⟨f496, f0⟩

def sq357 : Sequent := ⟨f496, f496⟩

def tm161 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2630071866/42005)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-940419969/602056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (108587651/203036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (31257403638/989647)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (516593311/615689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (28507487821/456546)) (.idx (.var 2) 0)) (.add (.mul (.const (-265535443/533928)) (.idx (.var 2) 1)) (.add (.mul (.const (-7884838487/248091)) (.idx (.var 2) 2)) (.const (-115298402/309891))))))))))) (.sub tm0 (.const 1))))

def f498 : Formula :=
  .atom .le tm161 (.const 0)

def sq358 : Sequent := ⟨f496, f498⟩

def sq359 : Sequent := ⟨f496, f45⟩

def tm162 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2630071866/42005)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-940419969/602056)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (108587651/203036)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (31257403638/989647)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (516593311/615689)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (28507487821/456546)) (.idx (.var 2) 0)) (.add (.mul (.const (-265535443/533928)) (.idx (.var 2) 1)) (.add (.mul (.const (-7884838487/248091)) (.idx (.var 2) 2)) (.const (-115298402/309891))))))))))) (.sub (.var 3) (.const 1))))

def f499 : Formula :=
  .atom .le tm162 (.const 0)

def f500 : Formula :=
  .and f496 f497

def sq360 : Sequent := ⟨f500, f245⟩

def tm163 : Term :=
  (.add (.mul (.const 200) tm160) (.const 0))

def f501 : Formula :=
  .and f0 f122

def sq361 : Sequent := ⟨f501, f245⟩

def f502 : Formula :=
  .and f0 f46

def sq362 : Sequent := ⟨f502, f245⟩

def tm164 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (386928800/463797)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-944869889/916252)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (79551161/164387)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-188335259/289934)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (912530554/880959)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-544631690/589331)) (.idx (.var 2) 0)) (.add (.mul (.const (-1097485017/560996)) (.idx (.var 2) 1)) (.add (.mul (.const (361094880/715837)) (.idx (.var 2) 2)) (.const (818401251/911027))))))))))) (.sub (.const 1) (.const 1))))

def f503 : Formula :=
  .atom .le tm164 (.const 0)

def sq363 : Sequent := ⟨f502, f503⟩

def sq364 : Sequent := ⟨f502, f0⟩

def sq365 : Sequent := ⟨f502, f502⟩

def tm165 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (386928800/463797)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-944869889/916252)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (79551161/164387)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-188335259/289934)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (912530554/880959)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-544631690/589331)) (.idx (.var 2) 0)) (.add (.mul (.const (-1097485017/560996)) (.idx (.var 2) 1)) (.add (.mul (.const (361094880/715837)) (.idx (.var 2) 2)) (.const (818401251/911027))))))))))) (.sub tm0 (.const 1))))

def f504 : Formula :=
  .atom .le tm165 (.const 0)

def sq366 : Sequent := ⟨f502, f504⟩

def sq367 : Sequent := ⟨f502, f46⟩

def tm166 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (386928800/463797)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-944869889/916252)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (79551161/164387)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-188335259/289934)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (912530554/880959)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-544631690/589331)) (.idx (.var 2) 0)) (.add (.mul (.const (-1097485017/560996)) (.idx (.var 2) 1)) (.add (.mul (.const (361094880/715837)) (.idx (.var 2) 2)) (.const (818401251/911027))))))))))) (.sub (.var 3) (.const 1))))

def f505 : Formula :=
  .atom .le tm166 (.const 0)

def f506 : Formula :=
  .and f502 f503

def sq368 : Sequent := ⟨f506, f245⟩

def tm167 : Term :=
  (.add (.mul (.const 200) tm164) (.const 0))

def f507 : Formula :=
  .and f0 f121

def sq369 : Sequent := ⟨f507, f245⟩

def f508 : Formula :=
  .and f0 f47

def sq370 : Sequent := ⟨f508, f245⟩

def tm168 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-826744558/934241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-31626440629/153166)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (44646901099/708225)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (48657109579/458713)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1121/994654)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (15457271631/981202)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-8648806649/382526)) (.idx (.var 2) 0)) (.add (.mul (.const (14304134613/902021)) (.idx (.var 2) 1)) (.add (.mul (.const (-28904714628/253811)) (.idx (.var 2) 2)) (.const (-721595577/42046))))))))))) (.sub (.const 1) (.const 1))))

def f509 : Formula :=
  .atom .le tm168 (.const 0)

def sq371 : Sequent := ⟨f508, f509⟩

def sq372 : Sequent := ⟨f508, f0⟩

def sq373 : Sequent := ⟨f508, f508⟩

def tm169 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-826744558/934241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-31626440629/153166)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (44646901099/708225)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (48657109579/458713)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1121/994654)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (15457271631/981202)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-8648806649/382526)) (.idx (.var 2) 0)) (.add (.mul (.const (14304134613/902021)) (.idx (.var 2) 1)) (.add (.mul (.const (-28904714628/253811)) (.idx (.var 2) 2)) (.const (-721595577/42046))))))))))) (.sub tm0 (.const 1))))

def f510 : Formula :=
  .atom .le tm169 (.const 0)

def sq374 : Sequent := ⟨f508, f510⟩

def sq375 : Sequent := ⟨f508, f47⟩

def tm170 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-826744558/934241)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-31626440629/153166)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (44646901099/708225)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (48657109579/458713)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1121/994654)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (15457271631/981202)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-8648806649/382526)) (.idx (.var 2) 0)) (.add (.mul (.const (14304134613/902021)) (.idx (.var 2) 1)) (.add (.mul (.const (-28904714628/253811)) (.idx (.var 2) 2)) (.const (-721595577/42046))))))))))) (.sub (.var 3) (.const 1))))

def f511 : Formula :=
  .atom .le tm170 (.const 0)

def f512 : Formula :=
  .and f508 f509

def sq376 : Sequent := ⟨f512, f245⟩

def tm171 : Term :=
  (.add (.mul (.const 200) tm168) (.const 0))

def f513 : Formula :=
  .and f0 f120

def sq377 : Sequent := ⟨f513, f245⟩

def f514 : Formula :=
  .and f0 f48

def sq378 : Sequent := ⟨f514, f245⟩

def tm172 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (747885911/246283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-440606738/288851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-148709341/537491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34238741197/993586)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-936673212/441335)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-17716901303/762965)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-3137380985/938064)) (.idx (.var 2) 0)) (.add (.mul (.const (8465595487/879009)) (.idx (.var 2) 1)) (.add (.mul (.const (-14097404589/338357)) (.idx (.var 2) 2)) (.const (-1095561665/135748))))))))))) (.sub (.const 1) (.const 1))))

def f515 : Formula :=
  .atom .le tm172 (.const 0)

def sq379 : Sequent := ⟨f514, f515⟩

def sq380 : Sequent := ⟨f514, f0⟩

def sq381 : Sequent := ⟨f514, f514⟩

def tm173 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (747885911/246283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-440606738/288851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-148709341/537491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34238741197/993586)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-936673212/441335)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-17716901303/762965)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-3137380985/938064)) (.idx (.var 2) 0)) (.add (.mul (.const (8465595487/879009)) (.idx (.var 2) 1)) (.add (.mul (.const (-14097404589/338357)) (.idx (.var 2) 2)) (.const (-1095561665/135748))))))))))) (.sub tm0 (.const 1))))

def f516 : Formula :=
  .atom .le tm173 (.const 0)

def sq382 : Sequent := ⟨f514, f516⟩

def sq383 : Sequent := ⟨f514, f48⟩

def tm174 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (747885911/246283)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-440606738/288851)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-148709341/537491)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34238741197/993586)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-936673212/441335)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-17716901303/762965)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-3137380985/938064)) (.idx (.var 2) 0)) (.add (.mul (.const (8465595487/879009)) (.idx (.var 2) 1)) (.add (.mul (.const (-14097404589/338357)) (.idx (.var 2) 2)) (.const (-1095561665/135748))))))))))) (.sub (.var 3) (.const 1))))

def f517 : Formula :=
  .atom .le tm174 (.const 0)

def f518 : Formula :=
  .and f514 f515

def sq384 : Sequent := ⟨f518, f245⟩

def tm175 : Term :=
  (.add (.mul (.const 200) tm172) (.const 0))

def f519 : Formula :=
  .and f0 f119

def sq385 : Sequent := ⟨f519, f245⟩

def f520 : Formula :=
  .and f0 f49

def sq386 : Sequent := ⟨f520, f245⟩

def tm176 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-576164791997/922384)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (180852511360/868511)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-30928328/785171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5091163588/913225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (12179267522/957579)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (549258634715/799361)) (.idx (.var 2) 0)) (.add (.mul (.const (-45222939571/709484)) (.idx (.var 2) 1)) (.add (.mul (.const (13859975288/767629)) (.idx (.var 2) 2)) (.const (34515469362/630709))))))))))) (.sub (.const 1) (.const 1))))

def f521 : Formula :=
  .atom .le tm176 (.const 0)

def sq387 : Sequent := ⟨f520, f521⟩

def sq388 : Sequent := ⟨f520, f0⟩

def sq389 : Sequent := ⟨f520, f520⟩

def tm177 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-576164791997/922384)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (180852511360/868511)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-30928328/785171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5091163588/913225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (12179267522/957579)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (549258634715/799361)) (.idx (.var 2) 0)) (.add (.mul (.const (-45222939571/709484)) (.idx (.var 2) 1)) (.add (.mul (.const (13859975288/767629)) (.idx (.var 2) 2)) (.const (34515469362/630709))))))))))) (.sub tm0 (.const 1))))

def f522 : Formula :=
  .atom .le tm177 (.const 0)

def sq390 : Sequent := ⟨f520, f522⟩

def sq391 : Sequent := ⟨f520, f49⟩

def tm178 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-576164791997/922384)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (180852511360/868511)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-30928328/785171)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5091163588/913225)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (12179267522/957579)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (549258634715/799361)) (.idx (.var 2) 0)) (.add (.mul (.const (-45222939571/709484)) (.idx (.var 2) 1)) (.add (.mul (.const (13859975288/767629)) (.idx (.var 2) 2)) (.const (34515469362/630709))))))))))) (.sub (.var 3) (.const 1))))

def f523 : Formula :=
  .atom .le tm178 (.const 0)

def f524 : Formula :=
  .and f520 f521

def sq392 : Sequent := ⟨f524, f245⟩

def tm179 : Term :=
  (.add (.mul (.const 200) tm176) (.const 0))

def f525 : Formula :=
  .and f0 f118

def sq393 : Sequent := ⟨f525, f245⟩

def f526 : Formula :=
  .and f0 f50

def sq394 : Sequent := ⟨f526, f245⟩

def tm180 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192849305545/801691)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-158727432541/905802)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (58975206772/999455)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-276/58159)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (615419216/743853)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (295587771511/942072)) (.idx (.var 2) 0)) (.add (.mul (.const (1818229397/556197)) (.idx (.var 2) 1)) (.add (.mul (.const (-2347102363/33957)) (.idx (.var 2) 2)) (.const (-1119800260/429817))))))))))) (.sub (.const 1) (.const 1))))

def f527 : Formula :=
  .atom .le tm180 (.const 0)

def sq395 : Sequent := ⟨f526, f527⟩

def sq396 : Sequent := ⟨f526, f0⟩

def sq397 : Sequent := ⟨f526, f526⟩

def tm181 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192849305545/801691)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-158727432541/905802)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (58975206772/999455)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-276/58159)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (615419216/743853)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (295587771511/942072)) (.idx (.var 2) 0)) (.add (.mul (.const (1818229397/556197)) (.idx (.var 2) 1)) (.add (.mul (.const (-2347102363/33957)) (.idx (.var 2) 2)) (.const (-1119800260/429817))))))))))) (.sub tm0 (.const 1))))

def f528 : Formula :=
  .atom .le tm181 (.const 0)

def sq398 : Sequent := ⟨f526, f528⟩

def sq399 : Sequent := ⟨f526, f50⟩

def tm182 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-192849305545/801691)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-158727432541/905802)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const 1048576) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (58975206772/999455)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-276/58159)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (615419216/743853)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (295587771511/942072)) (.idx (.var 2) 0)) (.add (.mul (.const (1818229397/556197)) (.idx (.var 2) 1)) (.add (.mul (.const (-2347102363/33957)) (.idx (.var 2) 2)) (.const (-1119800260/429817))))))))))) (.sub (.var 3) (.const 1))))

def f529 : Formula :=
  .atom .le tm182 (.const 0)

def f530 : Formula :=
  .and f526 f527

def sq400 : Sequent := ⟨f530, f245⟩

def tm183 : Term :=
  (.add (.mul (.const 200) tm180) (.const 0))

def f531 : Formula :=
  .and f0 f117

def sq401 : Sequent := ⟨f531, f245⟩

def f532 : Formula :=
  .and f0 f51

def sq402 : Sequent := ⟨f532, f245⟩

def tm184 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-139638660141/639127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2853099778/939693)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (6789208471/950835)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (50886003085/937963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1931428396/577081)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (56243159/895623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29877481471/136514)) (.idx (.var 2) 0)) (.add (.mul (.const (-2637202703/879187)) (.idx (.var 2) 1)) (.add (.mul (.const (-45271103152/827987)) (.idx (.var 2) 2)) (.const (-150480936/349517))))))))))) (.sub (.const 1) (.const 1))))

def f533 : Formula :=
  .atom .le tm184 (.const 0)

def sq403 : Sequent := ⟨f532, f533⟩

def sq404 : Sequent := ⟨f532, f0⟩

def sq405 : Sequent := ⟨f532, f532⟩

def tm185 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-139638660141/639127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2853099778/939693)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (6789208471/950835)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (50886003085/937963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1931428396/577081)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (56243159/895623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29877481471/136514)) (.idx (.var 2) 0)) (.add (.mul (.const (-2637202703/879187)) (.idx (.var 2) 1)) (.add (.mul (.const (-45271103152/827987)) (.idx (.var 2) 2)) (.const (-150480936/349517))))))))))) (.sub tm0 (.const 1))))

def f534 : Formula :=
  .atom .le tm185 (.const 0)

def sq406 : Sequent := ⟨f532, f534⟩

def sq407 : Sequent := ⟨f532, f51⟩

def tm186 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-139638660141/639127)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2853099778/939693)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (6789208471/950835)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (50886003085/937963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1931428396/577081)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (56243159/895623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (29877481471/136514)) (.idx (.var 2) 0)) (.add (.mul (.const (-2637202703/879187)) (.idx (.var 2) 1)) (.add (.mul (.const (-45271103152/827987)) (.idx (.var 2) 2)) (.const (-150480936/349517))))))))))) (.sub (.var 3) (.const 1))))

def f535 : Formula :=
  .atom .le tm186 (.const 0)

def f536 : Formula :=
  .and f532 f533

def sq408 : Sequent := ⟨f536, f245⟩

def tm187 : Term :=
  (.add (.mul (.const 200) tm184) (.const 0))

def f537 : Formula :=
  .and f0 f116

def sq409 : Sequent := ⟨f537, f245⟩

def f538 : Formula :=
  .and f0 f52

def sq410 : Sequent := ⟨f538, f245⟩

def tm188 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (7633830409/974197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1014399565/336548)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98677493/121228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2216806973/952133)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (294764219/88071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (437676011/966873)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-7468040735/865258)) (.idx (.var 2) 0)) (.add (.mul (.const (-6260594588/979077)) (.idx (.var 2) 1)) (.add (.mul (.const (279208759/124435)) (.idx (.var 2) 2)) (.const (1879033919/629861))))))))))) (.sub (.const 1) (.const 1))))

def f539 : Formula :=
  .atom .le tm188 (.const 0)

def sq411 : Sequent := ⟨f538, f539⟩

def sq412 : Sequent := ⟨f538, f0⟩

def sq413 : Sequent := ⟨f538, f538⟩

def tm189 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (7633830409/974197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1014399565/336548)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98677493/121228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2216806973/952133)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (294764219/88071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (437676011/966873)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-7468040735/865258)) (.idx (.var 2) 0)) (.add (.mul (.const (-6260594588/979077)) (.idx (.var 2) 1)) (.add (.mul (.const (279208759/124435)) (.idx (.var 2) 2)) (.const (1879033919/629861))))))))))) (.sub tm0 (.const 1))))

def f540 : Formula :=
  .atom .le tm189 (.const 0)

def sq414 : Sequent := ⟨f538, f540⟩

def sq415 : Sequent := ⟨f538, f52⟩

def tm190 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (7633830409/974197)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1014399565/336548)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98677493/121228)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2216806973/952133)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (294764219/88071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (437676011/966873)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-7468040735/865258)) (.idx (.var 2) 0)) (.add (.mul (.const (-6260594588/979077)) (.idx (.var 2) 1)) (.add (.mul (.const (279208759/124435)) (.idx (.var 2) 2)) (.const (1879033919/629861))))))))))) (.sub (.var 3) (.const 1))))

def f541 : Formula :=
  .atom .le tm190 (.const 0)

def f542 : Formula :=
  .and f538 f539

def sq416 : Sequent := ⟨f542, f245⟩

def tm191 : Term :=
  (.add (.mul (.const 200) tm188) (.const 0))

def f543 : Formula :=
  .and f0 f115

def sq417 : Sequent := ⟨f543, f245⟩

def f544 : Formula :=
  .and f0 f53

def sq418 : Sequent := ⟨f544, f245⟩

def tm192 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-847180633/689155)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-34578548361/790964)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (40282564363/460885)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-594279458/208171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3955/833402)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1894369456/347311)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1049510942/691345)) (.idx (.var 2) 0)) (.add (.mul (.const (-907861196/976017)) (.idx (.var 2) 1)) (.add (.mul (.const (2224697407/689961)) (.idx (.var 2) 2)) (.const (449785542/524495))))))))))) (.sub (.const 1) (.const 1))))

def f545 : Formula :=
  .atom .le tm192 (.const 0)

def sq419 : Sequent := ⟨f544, f545⟩

def sq420 : Sequent := ⟨f544, f0⟩

def sq421 : Sequent := ⟨f544, f544⟩

def tm193 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-847180633/689155)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-34578548361/790964)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (40282564363/460885)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-594279458/208171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3955/833402)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1894369456/347311)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1049510942/691345)) (.idx (.var 2) 0)) (.add (.mul (.const (-907861196/976017)) (.idx (.var 2) 1)) (.add (.mul (.const (2224697407/689961)) (.idx (.var 2) 2)) (.const (449785542/524495))))))))))) (.sub tm0 (.const 1))))

def f546 : Formula :=
  .atom .le tm193 (.const 0)

def sq422 : Sequent := ⟨f544, f546⟩

def sq423 : Sequent := ⟨f544, f53⟩

def tm194 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-847180633/689155)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-34578548361/790964)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (40282564363/460885)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-594279458/208171)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-3955/833402)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1894369456/347311)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-1049510942/691345)) (.idx (.var 2) 0)) (.add (.mul (.const (-907861196/976017)) (.idx (.var 2) 1)) (.add (.mul (.const (2224697407/689961)) (.idx (.var 2) 2)) (.const (449785542/524495))))))))))) (.sub (.var 3) (.const 1))))

def f547 : Formula :=
  .atom .le tm194 (.const 0)

def f548 : Formula :=
  .and f544 f545

def sq424 : Sequent := ⟨f548, f245⟩

def tm195 : Term :=
  (.add (.mul (.const 200) tm192) (.const 0))

def f549 : Formula :=
  .and f0 f114

def sq425 : Sequent := ⟨f549, f245⟩

def f550 : Formula :=
  .and f0 f54

def sq426 : Sequent := ⟨f550, f245⟩

def tm196 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3357636156/858229)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1170416417/396484)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-110919047/291449)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12077757534/459977)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-248977713/91514)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5060273087/563598)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4110931631/838211)) (.idx (.var 2) 0)) (.add (.mul (.const (13218406524/971977)) (.idx (.var 2) 1)) (.add (.mul (.const (-22056034328/687071)) (.idx (.var 2) 2)) (.const (-1119581011/94645))))))))))) (.sub (.const 1) (.const 1))))

def f551 : Formula :=
  .atom .le tm196 (.const 0)

def sq427 : Sequent := ⟨f550, f551⟩

def sq428 : Sequent := ⟨f550, f0⟩

def sq429 : Sequent := ⟨f550, f550⟩

def tm197 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3357636156/858229)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1170416417/396484)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-110919047/291449)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12077757534/459977)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-248977713/91514)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5060273087/563598)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4110931631/838211)) (.idx (.var 2) 0)) (.add (.mul (.const (13218406524/971977)) (.idx (.var 2) 1)) (.add (.mul (.const (-22056034328/687071)) (.idx (.var 2) 2)) (.const (-1119581011/94645))))))))))) (.sub tm0 (.const 1))))

def f552 : Formula :=
  .atom .le tm197 (.const 0)

def sq430 : Sequent := ⟨f550, f552⟩

def sq431 : Sequent := ⟨f550, f54⟩

def tm198 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3357636156/858229)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1170416417/396484)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-110919047/291449)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12077757534/459977)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-248977713/91514)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-5060273087/563598)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-4110931631/838211)) (.idx (.var 2) 0)) (.add (.mul (.const (13218406524/971977)) (.idx (.var 2) 1)) (.add (.mul (.const (-22056034328/687071)) (.idx (.var 2) 2)) (.const (-1119581011/94645))))))))))) (.sub (.var 3) (.const 1))))

def f553 : Formula :=
  .atom .le tm198 (.const 0)

def f554 : Formula :=
  .and f550 f551

def sq432 : Sequent := ⟨f554, f245⟩

def tm199 : Term :=
  (.add (.mul (.const 200) tm196) (.const 0))

def f555 : Formula :=
  .and f0 f113

def sq433 : Sequent := ⟨f555, f245⟩

def f556 : Formula :=
  .and f0 f55

def sq434 : Sequent := ⟨f556, f245⟩

def tm200 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2114790220/992303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-448707158/467015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-231000337/964193)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34672082/927819)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (744878373/429835)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/6623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1279433243/576986)) (.idx (.var 2) 0)) (.add (.mul (.const (-2499024201/782404)) (.idx (.var 2) 1)) (.add (.mul (.const (8374471/85224)) (.idx (.var 2) 2)) (.const (184511899/126903))))))))))) (.sub (.const 1) (.const 1))))

def f557 : Formula :=
  .atom .le tm200 (.const 0)

def sq435 : Sequent := ⟨f556, f557⟩

def sq436 : Sequent := ⟨f556, f0⟩

def sq437 : Sequent := ⟨f556, f556⟩

def tm201 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2114790220/992303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-448707158/467015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-231000337/964193)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34672082/927819)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (744878373/429835)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/6623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1279433243/576986)) (.idx (.var 2) 0)) (.add (.mul (.const (-2499024201/782404)) (.idx (.var 2) 1)) (.add (.mul (.const (8374471/85224)) (.idx (.var 2) 2)) (.const (184511899/126903))))))))))) (.sub tm0 (.const 1))))

def f558 : Formula :=
  .atom .le tm201 (.const 0)

def sq438 : Sequent := ⟨f556, f558⟩

def sq439 : Sequent := ⟨f556, f55⟩

def tm202 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2114790220/992303)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-448707158/467015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-231000337/964193)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (34672082/927819)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (744878373/429835)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-193600/6623)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1279433243/576986)) (.idx (.var 2) 0)) (.add (.mul (.const (-2499024201/782404)) (.idx (.var 2) 1)) (.add (.mul (.const (8374471/85224)) (.idx (.var 2) 2)) (.const (184511899/126903))))))))))) (.sub (.var 3) (.const 1))))

def f559 : Formula :=
  .atom .le tm202 (.const 0)

def f560 : Formula :=
  .and f556 f557

def sq440 : Sequent := ⟨f560, f245⟩

def tm203 : Term :=
  (.add (.mul (.const 200) tm200) (.const 0))

def f561 : Formula :=
  .and f0 f112

def sq441 : Sequent := ⟨f561, f245⟩

def f562 : Formula :=
  .and f0 f56

def sq442 : Sequent := ⟨f562, f245⟩

def tm204 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8526140716/634215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1518575344/946369)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4921647355/880926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5244952979/428591)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (65500365493/932443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (53547369/609938)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6825321041/620029)) (.idx (.var 2) 0)) (.add (.mul (.const (-23445272076/172891)) (.idx (.var 2) 1)) (.add (.mul (.const (10613836447/851818)) (.idx (.var 2) 2)) (.const (61082609035/938218))))))))))) (.sub (.const 1) (.const 1))))

def f563 : Formula :=
  .atom .le tm204 (.const 0)

def sq443 : Sequent := ⟨f562, f563⟩

def sq444 : Sequent := ⟨f562, f0⟩

def sq445 : Sequent := ⟨f562, f562⟩

def tm205 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8526140716/634215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1518575344/946369)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4921647355/880926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5244952979/428591)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (65500365493/932443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (53547369/609938)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6825321041/620029)) (.idx (.var 2) 0)) (.add (.mul (.const (-23445272076/172891)) (.idx (.var 2) 1)) (.add (.mul (.const (10613836447/851818)) (.idx (.var 2) 2)) (.const (61082609035/938218))))))))))) (.sub tm0 (.const 1))))

def f564 : Formula :=
  .atom .le tm205 (.const 0)

def sq446 : Sequent := ⟨f562, f564⟩

def sq447 : Sequent := ⟨f562, f56⟩

def tm206 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (8526140716/634215)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-1518575344/946369)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-4921647355/880926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5244952979/428591)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (65500365493/932443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (53547369/609938)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-6825321041/620029)) (.idx (.var 2) 0)) (.add (.mul (.const (-23445272076/172891)) (.idx (.var 2) 1)) (.add (.mul (.const (10613836447/851818)) (.idx (.var 2) 2)) (.const (61082609035/938218))))))))))) (.sub (.var 3) (.const 1))))

def f565 : Formula :=
  .atom .le tm206 (.const 0)

def f566 : Formula :=
  .and f562 f563

def sq448 : Sequent := ⟨f566, f245⟩

def tm207 : Term :=
  (.add (.mul (.const 200) tm204) (.const 0))

def f567 : Formula :=
  .and f0 f111

def sq449 : Sequent := ⟨f567, f245⟩

def f568 : Formula :=
  .and f0 f57

def sq450 : Sequent := ⟨f568, f245⟩

def tm208 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9080336/19609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (149576837/444292)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-572180431/900912)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-85491228/963037)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-19692953/418969)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-84368741/246996)) (.idx (.var 2) 0)) (.add (.mul (.const (-8780665/316031)) (.idx (.var 2) 1)) (.add (.mul (.const (39333769/640393)) (.idx (.var 2) 2)) (.const (7599023/333566)))))))))) (.sub (.const 1) (.const 1))))

def f569 : Formula :=
  .atom .le tm208 (.const 0)

def sq451 : Sequent := ⟨f568, f569⟩

def sq452 : Sequent := ⟨f568, f0⟩

def sq453 : Sequent := ⟨f568, f568⟩

def tm209 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9080336/19609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (149576837/444292)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-572180431/900912)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-85491228/963037)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-19692953/418969)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-84368741/246996)) (.idx (.var 2) 0)) (.add (.mul (.const (-8780665/316031)) (.idx (.var 2) 1)) (.add (.mul (.const (39333769/640393)) (.idx (.var 2) 2)) (.const (7599023/333566)))))))))) (.sub tm0 (.const 1))))

def f570 : Formula :=
  .atom .le tm209 (.const 0)

def sq454 : Sequent := ⟨f568, f570⟩

def sq455 : Sequent := ⟨f568, f57⟩

def tm210 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (9080336/19609)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (149576837/444292)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-572180431/900912)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-85491228/963037)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-19692953/418969)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-84368741/246996)) (.idx (.var 2) 0)) (.add (.mul (.const (-8780665/316031)) (.idx (.var 2) 1)) (.add (.mul (.const (39333769/640393)) (.idx (.var 2) 2)) (.const (7599023/333566)))))))))) (.sub (.var 3) (.const 1))))

def f571 : Formula :=
  .atom .le tm210 (.const 0)

def f572 : Formula :=
  .and f568 f569

def sq456 : Sequent := ⟨f572, f245⟩

def tm211 : Term :=
  (.add (.mul (.const 200) tm208) (.const 0))

def f573 : Formula :=
  .and f0 f110

def sq457 : Sequent := ⟨f573, f245⟩

def f574 : Formula :=
  .and f0 f58

def sq458 : Sequent := ⟨f574, f245⟩

def tm212 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (14841614450/251501)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4273406807/957699)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19448599019/555514)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-3002637037/405356)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-32009034965/582729)) (.idx (.var 2) 0)) (.add (.mul (.const (-1429374566/403695)) (.idx (.var 2) 1)) (.add (.mul (.const (6255572869/874537)) (.idx (.var 2) 2)) (.const (1639279027/479068)))))))))) (.sub (.const 1) (.const 1))))

def f575 : Formula :=
  .atom .le tm212 (.const 0)

def sq459 : Sequent := ⟨f574, f575⟩

def sq460 : Sequent := ⟨f574, f0⟩

def sq461 : Sequent := ⟨f574, f574⟩

def tm213 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (14841614450/251501)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4273406807/957699)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19448599019/555514)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-3002637037/405356)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-32009034965/582729)) (.idx (.var 2) 0)) (.add (.mul (.const (-1429374566/403695)) (.idx (.var 2) 1)) (.add (.mul (.const (6255572869/874537)) (.idx (.var 2) 2)) (.const (1639279027/479068)))))))))) (.sub tm0 (.const 1))))

def f576 : Formula :=
  .atom .le tm213 (.const 0)

def sq462 : Sequent := ⟨f574, f576⟩

def sq463 : Sequent := ⟨f574, f58⟩

def tm214 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (14841614450/251501)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4273406807/957699)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-19448599019/555514)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-3002637037/405356)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1100/43)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-32009034965/582729)) (.idx (.var 2) 0)) (.add (.mul (.const (-1429374566/403695)) (.idx (.var 2) 1)) (.add (.mul (.const (6255572869/874537)) (.idx (.var 2) 2)) (.const (1639279027/479068)))))))))) (.sub (.var 3) (.const 1))))

def f577 : Formula :=
  .atom .le tm214 (.const 0)

def f578 : Formula :=
  .and f574 f575

def sq464 : Sequent := ⟨f578, f245⟩

def tm215 : Term :=
  (.add (.mul (.const 200) tm212) (.const 0))

def f579 : Formula :=
  .and f0 f109

def sq465 : Sequent := ⟨f579, f245⟩

def f580 : Formula :=
  .and f0 f59

def sq466 : Sequent := ⟨f580, f245⟩

def tm216 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-264507506/952461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20780264145/553072)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9409137509/62638)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1083448966/878273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-296549853/43457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1881114347/804392)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-15253247531/858402)) (.idx (.var 2) 0)) (.add (.mul (.const (9339734609/757775)) (.idx (.var 2) 1)) (.add (.mul (.const (1141384999/997996)) (.idx (.var 2) 2)) (.const (-3012731427/599926))))))))))) (.sub (.const 1) (.const 1))))

def f581 : Formula :=
  .atom .le tm216 (.const 0)

def sq467 : Sequent := ⟨f580, f581⟩

def sq468 : Sequent := ⟨f580, f0⟩

def sq469 : Sequent := ⟨f580, f580⟩

def tm217 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-264507506/952461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20780264145/553072)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9409137509/62638)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1083448966/878273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-296549853/43457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1881114347/804392)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-15253247531/858402)) (.idx (.var 2) 0)) (.add (.mul (.const (9339734609/757775)) (.idx (.var 2) 1)) (.add (.mul (.const (1141384999/997996)) (.idx (.var 2) 2)) (.const (-3012731427/599926))))))))))) (.sub tm0 (.const 1))))

def f582 : Formula :=
  .atom .le tm217 (.const 0)

def sq470 : Sequent := ⟨f580, f582⟩

def sq471 : Sequent := ⟨f580, f59⟩

def tm218 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-264507506/952461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-20780264145/553072)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (9409137509/62638)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1083448966/878273)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-296549853/43457)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1881114347/804392)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-15253247531/858402)) (.idx (.var 2) 0)) (.add (.mul (.const (9339734609/757775)) (.idx (.var 2) 1)) (.add (.mul (.const (1141384999/997996)) (.idx (.var 2) 2)) (.const (-3012731427/599926))))))))))) (.sub (.var 3) (.const 1))))

def f583 : Formula :=
  .atom .le tm218 (.const 0)

def f584 : Formula :=
  .and f580 f581

def sq472 : Sequent := ⟨f584, f245⟩

def tm219 : Term :=
  (.add (.mul (.const 200) tm216) (.const 0))

def f585 : Formula :=
  .and f0 f108

def sq473 : Sequent := ⟨f585, f245⟩

def f586 : Formula :=
  .and f0 f60

def sq474 : Sequent := ⟨f586, f245⟩

def tm220 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3141573899/243231)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (490405475/258156)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98893325/87029)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-175907907/11833)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (48192896906/557071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64988620/740261)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (9697938683/844900)) (.idx (.var 2) 0)) (.add (.mul (.const (-111656746704/684967)) (.idx (.var 2) 1)) (.add (.mul (.const (7196144851/492369)) (.idx (.var 2) 2)) (.const (42512254514/554679))))))))))) (.sub (.const 1) (.const 1))))

def f587 : Formula :=
  .atom .le tm220 (.const 0)

def sq475 : Sequent := ⟨f586, f587⟩

def sq476 : Sequent := ⟨f586, f0⟩

def sq477 : Sequent := ⟨f586, f586⟩

def tm221 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3141573899/243231)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (490405475/258156)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98893325/87029)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-175907907/11833)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (48192896906/557071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64988620/740261)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (9697938683/844900)) (.idx (.var 2) 0)) (.add (.mul (.const (-111656746704/684967)) (.idx (.var 2) 1)) (.add (.mul (.const (7196144851/492369)) (.idx (.var 2) 2)) (.const (42512254514/554679))))))))))) (.sub tm0 (.const 1))))

def f588 : Formula :=
  .atom .le tm221 (.const 0)

def sq478 : Sequent := ⟨f586, f588⟩

def sq479 : Sequent := ⟨f586, f60⟩

def tm222 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3141573899/243231)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (490405475/258156)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (98893325/87029)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-175907907/11833)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (48192896906/557071)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64988620/740261)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (9697938683/844900)) (.idx (.var 2) 0)) (.add (.mul (.const (-111656746704/684967)) (.idx (.var 2) 1)) (.add (.mul (.const (7196144851/492369)) (.idx (.var 2) 2)) (.const (42512254514/554679))))))))))) (.sub (.var 3) (.const 1))))

def f589 : Formula :=
  .atom .le tm222 (.const 0)

def f590 : Formula :=
  .and f586 f587

def sq480 : Sequent := ⟨f590, f245⟩

def tm223 : Term :=
  (.add (.mul (.const 200) tm220) (.const 0))

def f591 : Formula :=
  .and f0 f107

def sq481 : Sequent := ⟨f591, f245⟩

def f592 : Formula :=
  .and f0 f61

def sq482 : Sequent := ⟨f592, f245⟩

def tm224 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1807408973/910576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4852346/718431)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-116165481/533489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13487429/998645)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1013772453/630148)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10769425/937217)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (965427633/467828)) (.idx (.var 2) 0)) (.add (.mul (.const (-58653326/19787)) (.idx (.var 2) 1)) (.add (.mul (.const (-3716627/300110)) (.idx (.var 2) 2)) (.const (299732021/222199))))))))))) (.sub (.const 1) (.const 1))))

def f593 : Formula :=
  .atom .le tm224 (.const 0)

def sq483 : Sequent := ⟨f592, f593⟩

def sq484 : Sequent := ⟨f592, f0⟩

def sq485 : Sequent := ⟨f592, f592⟩

def tm225 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1807408973/910576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4852346/718431)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-116165481/533489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13487429/998645)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1013772453/630148)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10769425/937217)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (965427633/467828)) (.idx (.var 2) 0)) (.add (.mul (.const (-58653326/19787)) (.idx (.var 2) 1)) (.add (.mul (.const (-3716627/300110)) (.idx (.var 2) 2)) (.const (299732021/222199))))))))))) (.sub tm0 (.const 1))))

def f594 : Formula :=
  .atom .le tm225 (.const 0)

def sq486 : Sequent := ⟨f592, f594⟩

def sq487 : Sequent := ⟨f592, f61⟩

def tm226 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1807408973/910576)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4852346/718431)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-116165481/533489)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (13487429/998645)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1013772453/630148)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-10769425/937217)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (965427633/467828)) (.idx (.var 2) 0)) (.add (.mul (.const (-58653326/19787)) (.idx (.var 2) 1)) (.add (.mul (.const (-3716627/300110)) (.idx (.var 2) 2)) (.const (299732021/222199))))))))))) (.sub (.var 3) (.const 1))))

def f595 : Formula :=
  .atom .le tm226 (.const 0)

def f596 : Formula :=
  .and f592 f593

def sq488 : Sequent := ⟨f596, f245⟩

def tm227 : Term :=
  (.add (.mul (.const 200) tm224) (.const 0))

def f597 : Formula :=
  .and f0 f106

def sq489 : Sequent := ⟨f597, f245⟩

def f598 : Formula :=
  .and f0 f62

def sq490 : Sequent := ⟨f598, f245⟩

def tm228 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2625615144/757897)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-392489199/488359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1761327462/500983)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5887170232/958469)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1973519226/933185)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1354371774/328015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-950915652/381281)) (.idx (.var 2) 0)) (.add (.mul (.const (-3390053319/718736)) (.idx (.var 2) 1)) (.add (.mul (.const (4013684563/641503)) (.idx (.var 2) 2)) (.const (1250537473/493285))))))))))) (.sub (.const 1) (.const 1))))

def f599 : Formula :=
  .atom .le tm228 (.const 0)

def sq491 : Sequent := ⟨f598, f599⟩

def sq492 : Sequent := ⟨f598, f0⟩

def sq493 : Sequent := ⟨f598, f598⟩

def tm229 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2625615144/757897)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-392489199/488359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1761327462/500983)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5887170232/958469)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1973519226/933185)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1354371774/328015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-950915652/381281)) (.idx (.var 2) 0)) (.add (.mul (.const (-3390053319/718736)) (.idx (.var 2) 1)) (.add (.mul (.const (4013684563/641503)) (.idx (.var 2) 2)) (.const (1250537473/493285))))))))))) (.sub tm0 (.const 1))))

def f600 : Formula :=
  .atom .le tm229 (.const 0)

def sq494 : Sequent := ⟨f598, f600⟩

def sq495 : Sequent := ⟨f598, f62⟩

def tm230 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (2625615144/757897)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-392489199/488359)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1761327462/500983)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-5887170232/958469)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1973519226/933185)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (1354371774/328015)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-950915652/381281)) (.idx (.var 2) 0)) (.add (.mul (.const (-3390053319/718736)) (.idx (.var 2) 1)) (.add (.mul (.const (4013684563/641503)) (.idx (.var 2) 2)) (.const (1250537473/493285))))))))))) (.sub (.var 3) (.const 1))))

def f601 : Formula :=
  .atom .le tm230 (.const 0)

def f602 : Formula :=
  .and f598 f599

def sq496 : Sequent := ⟨f602, f245⟩

def tm231 : Term :=
  (.add (.mul (.const 200) tm228) (.const 0))

def f603 : Formula :=
  .and f0 f105

def sq497 : Sequent := ⟨f603, f245⟩

def f604 : Formula :=
  .and f0 f63

def sq498 : Sequent := ⟨f604, f245⟩

def tm232 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (87017029/305678)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (301079446/304079)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-171393363/418898)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32363986/121315)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-59471/540627)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-12427997/20898)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-69957137/524185)) (.idx (.var 2) 0)) (.add (.mul (.const (-17133525/459106)) (.idx (.var 2) 1)) (.add (.mul (.const (77979387/851570)) (.idx (.var 2) 2)) (.const (14258826/582787))))))))))) (.sub (.const 1) (.const 1))))

def f605 : Formula :=
  .atom .le tm232 (.const 0)

def sq499 : Sequent := ⟨f604, f605⟩

def sq500 : Sequent := ⟨f604, f0⟩

def sq501 : Sequent := ⟨f604, f604⟩

def tm233 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (87017029/305678)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (301079446/304079)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-171393363/418898)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32363986/121315)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-59471/540627)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-12427997/20898)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-69957137/524185)) (.idx (.var 2) 0)) (.add (.mul (.const (-17133525/459106)) (.idx (.var 2) 1)) (.add (.mul (.const (77979387/851570)) (.idx (.var 2) 2)) (.const (14258826/582787))))))))))) (.sub tm0 (.const 1))))

def f606 : Formula :=
  .atom .le tm233 (.const 0)

def sq502 : Sequent := ⟨f604, f606⟩

def sq503 : Sequent := ⟨f604, f63⟩

def tm234 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (87017029/305678)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (301079446/304079)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-171393363/418898)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-32363986/121315)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-59471/540627)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-12427997/20898)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-69957137/524185)) (.idx (.var 2) 0)) (.add (.mul (.const (-17133525/459106)) (.idx (.var 2) 1)) (.add (.mul (.const (77979387/851570)) (.idx (.var 2) 2)) (.const (14258826/582787))))))))))) (.sub (.var 3) (.const 1))))

def f607 : Formula :=
  .atom .le tm234 (.const 0)

def f608 : Formula :=
  .and f604 f605

def sq504 : Sequent := ⟨f608, f245⟩

def tm235 : Term :=
  (.add (.mul (.const 200) tm232) (.const 0))

def f609 : Formula :=
  .and f0 f104

def sq505 : Sequent := ⟨f609, f245⟩

def f610 : Formula :=
  .and f0 f64

def sq506 : Sequent := ⟨f610, f245⟩

def tm236 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1398950548/617621)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (187594375/362878)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-140217562/777627)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-99064027/621717)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (42042195/649118)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36195168/374935)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1914904508/826153)) (.idx (.var 2) 0)) (.add (.mul (.const (1664719/266324)) (.idx (.var 2) 1)) (.add (.mul (.const (70675886/549543)) (.idx (.var 2) 2)) (.const (-12657297/172121))))))))))) (.sub (.const 1) (.const 1))))

def f611 : Formula :=
  .atom .le tm236 (.const 0)

def sq507 : Sequent := ⟨f610, f611⟩

def sq508 : Sequent := ⟨f610, f0⟩

def sq509 : Sequent := ⟨f610, f610⟩

def tm237 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1398950548/617621)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (187594375/362878)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-140217562/777627)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-99064027/621717)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (42042195/649118)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36195168/374935)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1914904508/826153)) (.idx (.var 2) 0)) (.add (.mul (.const (1664719/266324)) (.idx (.var 2) 1)) (.add (.mul (.const (70675886/549543)) (.idx (.var 2) 2)) (.const (-12657297/172121))))))))))) (.sub tm0 (.const 1))))

def f612 : Formula :=
  .atom .le tm237 (.const 0)

def sq510 : Sequent := ⟨f610, f612⟩

def sq511 : Sequent := ⟨f610, f64⟩

def tm238 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1398950548/617621)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (187594375/362878)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-140217562/777627)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-99064027/621717)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (42042195/649118)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (36195168/374935)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1914904508/826153)) (.idx (.var 2) 0)) (.add (.mul (.const (1664719/266324)) (.idx (.var 2) 1)) (.add (.mul (.const (70675886/549543)) (.idx (.var 2) 2)) (.const (-12657297/172121))))))))))) (.sub (.var 3) (.const 1))))

def f613 : Formula :=
  .atom .le tm238 (.const 0)

def f614 : Formula :=
  .and f610 f611

def sq512 : Sequent := ⟨f614, f245⟩

def tm239 : Term :=
  (.add (.mul (.const 200) tm236) (.const 0))

def f615 : Formula :=
  .and f0 f103

def sq513 : Sequent := ⟨f615, f245⟩

def f616 : Formula :=
  .and f0 f65

def sq514 : Sequent := ⟨f616, f245⟩

def tm240 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1950738617/605687)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4280963261/844570)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1585542984/515873)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3216399911/805792)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (806850127/982150)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-482440226/975893)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (813315245/337203)) (.idx (.var 2) 0)) (.add (.mul (.const (-979264253/797711)) (.idx (.var 2) 1)) (.add (.mul (.const (-3015016883/913258)) (.idx (.var 2) 2)) (.const (452928709/985865))))))))))) (.sub (.const 1) (.const 1))))

def f617 : Formula :=
  .atom .le tm240 (.const 0)

def sq515 : Sequent := ⟨f616, f617⟩

def sq516 : Sequent := ⟨f616, f0⟩

def sq517 : Sequent := ⟨f616, f616⟩

def tm241 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1950738617/605687)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4280963261/844570)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1585542984/515873)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3216399911/805792)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (806850127/982150)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-482440226/975893)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (813315245/337203)) (.idx (.var 2) 0)) (.add (.mul (.const (-979264253/797711)) (.idx (.var 2) 1)) (.add (.mul (.const (-3015016883/913258)) (.idx (.var 2) 2)) (.const (452928709/985865))))))))))) (.sub tm0 (.const 1))))

def f618 : Formula :=
  .atom .le tm241 (.const 0)

def sq518 : Sequent := ⟨f616, f618⟩

def sq519 : Sequent := ⟨f616, f65⟩

def tm242 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1950738617/605687)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-4280963261/844570)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1585542984/515873)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3216399911/805792)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (806850127/982150)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-482440226/975893)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (813315245/337203)) (.idx (.var 2) 0)) (.add (.mul (.const (-979264253/797711)) (.idx (.var 2) 1)) (.add (.mul (.const (-3015016883/913258)) (.idx (.var 2) 2)) (.const (452928709/985865))))))))))) (.sub (.var 3) (.const 1))))

def f619 : Formula :=
  .atom .le tm242 (.const 0)

def f620 : Formula :=
  .and f616 f617

def sq520 : Sequent := ⟨f620, f245⟩

def tm243 : Term :=
  (.add (.mul (.const 200) tm240) (.const 0))

def f621 : Formula :=
  .and f0 f102

def sq521 : Sequent := ⟨f621, f245⟩

def f622 : Formula :=
  .and f0 f66

def sq522 : Sequent := ⟨f622, f245⟩

def tm244 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-38080500/313399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8000/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-84117144/147749)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1458925926/196955)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (5176453707/975728)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (232428335/997536)) (.idx (.var 2) 0)) (.add (.mul (.const (-7474713219/704317)) (.idx (.var 2) 1)) (.add (.mul (.const (6571582547/884863)) (.idx (.var 2) 2)) (.const (4352460403/820775))))))))))) (.sub (.const 1) (.const 1))))

def f623 : Formula :=
  .atom .le tm244 (.const 0)

def sq523 : Sequent := ⟨f622, f623⟩

def sq524 : Sequent := ⟨f622, f0⟩

def sq525 : Sequent := ⟨f622, f622⟩

def tm245 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-38080500/313399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8000/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-84117144/147749)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1458925926/196955)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (5176453707/975728)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (232428335/997536)) (.idx (.var 2) 0)) (.add (.mul (.const (-7474713219/704317)) (.idx (.var 2) 1)) (.add (.mul (.const (6571582547/884863)) (.idx (.var 2) 2)) (.const (4352460403/820775))))))))))) (.sub tm0 (.const 1))))

def f624 : Formula :=
  .atom .le tm245 (.const 0)

def sq526 : Sequent := ⟨f622, f624⟩

def sq527 : Sequent := ⟨f622, f66⟩

def tm246 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-38080500/313399)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-8000/81)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-84117144/147749)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1458925926/196955)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (5176453707/975728)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (4000/9)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (232428335/997536)) (.idx (.var 2) 0)) (.add (.mul (.const (-7474713219/704317)) (.idx (.var 2) 1)) (.add (.mul (.const (6571582547/884863)) (.idx (.var 2) 2)) (.const (4352460403/820775))))))))))) (.sub (.var 3) (.const 1))))

def f625 : Formula :=
  .atom .le tm246 (.const 0)

def f626 : Formula :=
  .and f622 f623

def sq528 : Sequent := ⟨f626, f245⟩

def tm247 : Term :=
  (.add (.mul (.const 200) tm244) (.const 0))

def f627 : Formula :=
  .and f0 f101

def sq529 : Sequent := ⟨f627, f245⟩

def f628 : Formula :=
  .and f0 f67

def sq530 : Sequent := ⟨f628, f245⟩

def tm248 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-842512603/257053)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (57416638/31015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-197500367/974467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-151087364/316791)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181735511/98857)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (62507369/711998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2534020817/725979)) (.idx (.var 2) 0)) (.add (.mul (.const (-1313953234/400827)) (.idx (.var 2) 1)) (.add (.mul (.const (91103211/391106)) (.idx (.var 2) 2)) (.const (647381003/457606))))))))))) (.sub (.const 1) (.const 1))))

def f629 : Formula :=
  .atom .le tm248 (.const 0)

def sq531 : Sequent := ⟨f628, f629⟩

def sq532 : Sequent := ⟨f628, f0⟩

def sq533 : Sequent := ⟨f628, f628⟩

def tm249 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-842512603/257053)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (57416638/31015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-197500367/974467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-151087364/316791)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181735511/98857)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (62507369/711998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2534020817/725979)) (.idx (.var 2) 0)) (.add (.mul (.const (-1313953234/400827)) (.idx (.var 2) 1)) (.add (.mul (.const (91103211/391106)) (.idx (.var 2) 2)) (.const (647381003/457606))))))))))) (.sub tm0 (.const 1))))

def f630 : Formula :=
  .atom .le tm249 (.const 0)

def sq534 : Sequent := ⟨f628, f630⟩

def sq535 : Sequent := ⟨f628, f67⟩

def tm250 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-842512603/257053)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (57416638/31015)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-197500367/974467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-151087364/316791)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (181735511/98857)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (62507369/711998)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2534020817/725979)) (.idx (.var 2) 0)) (.add (.mul (.const (-1313953234/400827)) (.idx (.var 2) 1)) (.add (.mul (.const (91103211/391106)) (.idx (.var 2) 2)) (.const (647381003/457606))))))))))) (.sub (.var 3) (.const 1))))

def f631 : Formula :=
  .atom .le tm250 (.const 0)

def f632 : Formula :=
  .and f628 f629

def sq536 : Sequent := ⟨f632, f245⟩

def tm251 : Term :=
  (.add (.mul (.const 200) tm248) (.const 0))

def f633 : Formula :=
  .and f0 f100

def sq537 : Sequent := ⟨f633, f245⟩

def f634 : Formula :=
  .and f0 f68

def sq538 : Sequent := ⟨f634, f245⟩

def tm252 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-280090173/86071)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7174758532/918671)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-604951241/189188)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (620553864/777527)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (727041229/824230)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-625848936/215279)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3795089710/803599)) (.idx (.var 2) 0)) (.add (.mul (.const (-812483980/638207)) (.idx (.var 2) 1)) (.add (.mul (.const (-1214815299/529154)) (.idx (.var 2) 2)) (.const (52276732/223213))))))))))) (.sub (.const 1) (.const 1))))

def f635 : Formula :=
  .atom .le tm252 (.const 0)

def sq539 : Sequent := ⟨f634, f635⟩

def sq540 : Sequent := ⟨f634, f0⟩

def sq541 : Sequent := ⟨f634, f634⟩

def tm253 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-280090173/86071)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7174758532/918671)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-604951241/189188)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (620553864/777527)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (727041229/824230)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-625848936/215279)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3795089710/803599)) (.idx (.var 2) 0)) (.add (.mul (.const (-812483980/638207)) (.idx (.var 2) 1)) (.add (.mul (.const (-1214815299/529154)) (.idx (.var 2) 2)) (.const (52276732/223213))))))))))) (.sub tm0 (.const 1))))

def f636 : Formula :=
  .atom .le tm253 (.const 0)

def sq542 : Sequent := ⟨f634, f636⟩

def sq543 : Sequent := ⟨f634, f68⟩

def tm254 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-280090173/86071)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (7174758532/918671)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-604951241/189188)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (620553864/777527)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (727041229/824230)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-625848936/215279)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (3795089710/803599)) (.idx (.var 2) 0)) (.add (.mul (.const (-812483980/638207)) (.idx (.var 2) 1)) (.add (.mul (.const (-1214815299/529154)) (.idx (.var 2) 2)) (.const (52276732/223213))))))))))) (.sub (.var 3) (.const 1))))

def f637 : Formula :=
  .atom .le tm254 (.const 0)

def f638 : Formula :=
  .and f634 f635

def sq544 : Sequent := ⟨f638, f245⟩

def tm255 : Term :=
  (.add (.mul (.const 200) tm252) (.const 0))

def f639 : Formula :=
  .and f0 f99

def sq545 : Sequent := ⟨f639, f245⟩

def f640 : Formula :=
  .and f0 f69

def sq546 : Sequent := ⟨f640, f245⟩

def tm256 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1311927530/781461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (210993108/966271)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-106941635/573061)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1255806757/738040)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1722663/949991)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-48293815/788717)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1191787265/675584)) (.idx (.var 2) 0)) (.add (.mul (.const (308196783/861199)) (.idx (.var 2) 1)) (.add (.mul (.const (-589234473/335054)) (.idx (.var 2) 2)) (.const (-128104517/350119))))))))))) (.sub (.const 1) (.const 1))))

def f641 : Formula :=
  .atom .le tm256 (.const 0)

def sq547 : Sequent := ⟨f640, f641⟩

def sq548 : Sequent := ⟨f640, f0⟩

def sq549 : Sequent := ⟨f640, f640⟩

def tm257 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1311927530/781461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (210993108/966271)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-106941635/573061)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1255806757/738040)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1722663/949991)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-48293815/788717)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1191787265/675584)) (.idx (.var 2) 0)) (.add (.mul (.const (308196783/861199)) (.idx (.var 2) 1)) (.add (.mul (.const (-589234473/335054)) (.idx (.var 2) 2)) (.const (-128104517/350119))))))))))) (.sub tm0 (.const 1))))

def f642 : Formula :=
  .atom .le tm257 (.const 0)

def sq550 : Sequent := ⟨f640, f642⟩

def sq551 : Sequent := ⟨f640, f69⟩

def tm258 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1311927530/781461)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (210993108/966271)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-106941635/573061)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1255806757/738040)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-1722663/949991)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-48293815/788717)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (1191787265/675584)) (.idx (.var 2) 0)) (.add (.mul (.const (308196783/861199)) (.idx (.var 2) 1)) (.add (.mul (.const (-589234473/335054)) (.idx (.var 2) 2)) (.const (-128104517/350119))))))))))) (.sub (.var 3) (.const 1))))

def f643 : Formula :=
  .atom .le tm258 (.const 0)

def f644 : Formula :=
  .and f640 f641

def sq552 : Sequent := ⟨f644, f245⟩

def tm259 : Term :=
  (.add (.mul (.const 200) tm256) (.const 0))

def f645 : Formula :=
  .and f0 f98

def sq553 : Sequent := ⟨f645, f245⟩

def f646 : Formula :=
  .and f0 f70

def sq554 : Sequent := ⟨f646, f245⟩

def tm260 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-476494244/191999)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (787519943/877909)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (118889401/643497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-138806459/185403)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (92047891/188111)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28122433/220286)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2450549116/969507)) (.idx (.var 2) 0)) (.add (.mul (.const (-744905449/881138)) (.idx (.var 2) 1)) (.add (.mul (.const (620648711/939426)) (.idx (.var 2) 2)) (.const (88117339/252276))))))))))) (.sub (.const 1) (.const 1))))

def f647 : Formula :=
  .atom .le tm260 (.const 0)

def sq555 : Sequent := ⟨f646, f647⟩

def sq556 : Sequent := ⟨f646, f0⟩

def sq557 : Sequent := ⟨f646, f646⟩

def tm261 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-476494244/191999)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (787519943/877909)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (118889401/643497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-138806459/185403)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (92047891/188111)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28122433/220286)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2450549116/969507)) (.idx (.var 2) 0)) (.add (.mul (.const (-744905449/881138)) (.idx (.var 2) 1)) (.add (.mul (.const (620648711/939426)) (.idx (.var 2) 2)) (.const (88117339/252276))))))))))) (.sub tm0 (.const 1))))

def f648 : Formula :=
  .atom .le tm261 (.const 0)

def sq558 : Sequent := ⟨f646, f648⟩

def sq559 : Sequent := ⟨f646, f70⟩

def tm262 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-476494244/191999)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (787519943/877909)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (118889401/643497)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-138806459/185403)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (92047891/188111)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (28122433/220286)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2450549116/969507)) (.idx (.var 2) 0)) (.add (.mul (.const (-744905449/881138)) (.idx (.var 2) 1)) (.add (.mul (.const (620648711/939426)) (.idx (.var 2) 2)) (.const (88117339/252276))))))))))) (.sub (.var 3) (.const 1))))

def f649 : Formula :=
  .atom .le tm262 (.const 0)

def f650 : Formula :=
  .and f646 f647

def sq560 : Sequent := ⟨f650, f245⟩

def tm263 : Term :=
  (.add (.mul (.const 200) tm260) (.const 0))

def f651 : Formula :=
  .and f0 f97

def sq561 : Sequent := ⟨f651, f245⟩

def f652 : Formula :=
  .and f0 f71

def sq562 : Sequent := ⟨f652, f245⟩

def tm264 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2701667991/649349)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2940064614/998243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (76159224/26243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1308709080/419399)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1163393940/781963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1239835930/928777)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (681443047/214647)) (.idx (.var 2) 0)) (.add (.mul (.const (-48769849/22234)) (.idx (.var 2) 1)) (.add (.mul (.const (-700488043/239049)) (.idx (.var 2) 2)) (.const (61991477/79684))))))))))) (.sub (.const 1) (.const 1))))

def f653 : Formula :=
  .atom .le tm264 (.const 0)

def sq563 : Sequent := ⟨f652, f653⟩

def sq564 : Sequent := ⟨f652, f0⟩

def sq565 : Sequent := ⟨f652, f652⟩

def tm265 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2701667991/649349)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2940064614/998243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (76159224/26243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1308709080/419399)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1163393940/781963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1239835930/928777)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (681443047/214647)) (.idx (.var 2) 0)) (.add (.mul (.const (-48769849/22234)) (.idx (.var 2) 1)) (.add (.mul (.const (-700488043/239049)) (.idx (.var 2) 2)) (.const (61991477/79684))))))))))) (.sub tm0 (.const 1))))

def f654 : Formula :=
  .atom .le tm265 (.const 0)

def sq566 : Sequent := ⟨f652, f654⟩

def sq567 : Sequent := ⟨f652, f71⟩

def tm266 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2701667991/649349)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-2940064614/998243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (76159224/26243)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1308709080/419399)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1163393940/781963)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1239835930/928777)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (681443047/214647)) (.idx (.var 2) 0)) (.add (.mul (.const (-48769849/22234)) (.idx (.var 2) 1)) (.add (.mul (.const (-700488043/239049)) (.idx (.var 2) 2)) (.const (61991477/79684))))))))))) (.sub (.var 3) (.const 1))))

def f655 : Formula :=
  .atom .le tm266 (.const 0)

def f656 : Formula :=
  .and f652 f653

def sq568 : Sequent := ⟨f656, f245⟩

def tm267 : Term :=
  (.add (.mul (.const 200) tm264) (.const 0))

def f657 : Formula :=
  .and f0 f96

def sq569 : Sequent := ⟨f657, f245⟩

def f658 : Formula :=
  .and f0 f72

def sq570 : Sequent := ⟨f658, f245⟩

def tm268 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-680742206/395793)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (151826524/247057)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14844385/98217)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (9936815946/335179)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-66/222521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-38589602281/958451)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (324031055/185118)) (.idx (.var 2) 0)) (.add (.mul (.const (2321367600/997721)) (.idx (.var 2) 1)) (.add (.mul (.const (-536029893/14983)) (.idx (.var 2) 2)) (.const (-1015146129/396616))))))))))) (.sub (.const 1) (.const 1))))

def f659 : Formula :=
  .atom .le tm268 (.const 0)

def sq571 : Sequent := ⟨f658, f659⟩

def sq572 : Sequent := ⟨f658, f0⟩

def sq573 : Sequent := ⟨f658, f658⟩

def tm269 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-680742206/395793)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (151826524/247057)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14844385/98217)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (9936815946/335179)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-66/222521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-38589602281/958451)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (324031055/185118)) (.idx (.var 2) 0)) (.add (.mul (.const (2321367600/997721)) (.idx (.var 2) 1)) (.add (.mul (.const (-536029893/14983)) (.idx (.var 2) 2)) (.const (-1015146129/396616))))))))))) (.sub tm0 (.const 1))))

def f660 : Formula :=
  .atom .le tm269 (.const 0)

def sq574 : Sequent := ⟨f658, f660⟩

def sq575 : Sequent := ⟨f658, f72⟩

def tm270 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-680742206/395793)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (151826524/247057)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (14844385/98217)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (9936815946/335179)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-66/222521)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-38589602281/958451)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (324031055/185118)) (.idx (.var 2) 0)) (.add (.mul (.const (2321367600/997721)) (.idx (.var 2) 1)) (.add (.mul (.const (-536029893/14983)) (.idx (.var 2) 2)) (.const (-1015146129/396616))))))))))) (.sub (.var 3) (.const 1))))

def f661 : Formula :=
  .atom .le tm270 (.const 0)

def f662 : Formula :=
  .and f658 f659

def sq576 : Sequent := ⟨f662, f245⟩

def tm271 : Term :=
  (.add (.mul (.const 200) tm268) (.const 0))

def f663 : Formula :=
  .and f0 f95

def sq577 : Sequent := ⟨f663, f245⟩

def f664 : Formula :=
  .and f0 f73

def sq578 : Sequent := ⟨f664, f245⟩

def tm272 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2950992168/251737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4916826716/996467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1990878513/660733)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-779953003/652983)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (984372118/313715)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10302243455/882888)) (.idx (.var 2) 0)) (.add (.mul (.const (-2330810572/480215)) (.idx (.var 2) 1)) (.add (.mul (.const (467365159/874811)) (.idx (.var 2) 2)) (.const (412583013/247505))))))))))) (.sub (.const 1) (.const 1))))

def f665 : Formula :=
  .atom .le tm272 (.const 0)

def sq579 : Sequent := ⟨f664, f665⟩

def sq580 : Sequent := ⟨f664, f0⟩

def sq581 : Sequent := ⟨f664, f664⟩

def tm273 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2950992168/251737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4916826716/996467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1990878513/660733)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-779953003/652983)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (984372118/313715)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10302243455/882888)) (.idx (.var 2) 0)) (.add (.mul (.const (-2330810572/480215)) (.idx (.var 2) 1)) (.add (.mul (.const (467365159/874811)) (.idx (.var 2) 2)) (.const (412583013/247505))))))))))) (.sub tm0 (.const 1))))

def f666 : Formula :=
  .atom .le tm273 (.const 0)

def sq582 : Sequent := ⟨f664, f666⟩

def sq583 : Sequent := ⟨f664, f73⟩

def tm274 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-2950992168/251737)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (4916826716/996467)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1990878513/660733)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-779953003/652983)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (984372118/313715)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (10302243455/882888)) (.idx (.var 2) 0)) (.add (.mul (.const (-2330810572/480215)) (.idx (.var 2) 1)) (.add (.mul (.const (467365159/874811)) (.idx (.var 2) 2)) (.const (412583013/247505))))))))))) (.sub (.var 3) (.const 1))))

def f667 : Formula :=
  .atom .le tm274 (.const 0)

def f668 : Formula :=
  .and f664 f665

def sq584 : Sequent := ⟨f668, f245⟩

def tm275 : Term :=
  (.add (.mul (.const 200) tm272) (.const 0))

def f669 : Formula :=
  .and f0 f94

def sq585 : Sequent := ⟨f669, f245⟩

def f670 : Formula :=
  .and f0 f74

def sq586 : Sequent := ⟨f670, f245⟩

def tm276 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3659910100/769551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (5976095356/646515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-10557842609/886926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1211673761/539353)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-717/631526)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-85897217/51801)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2738281754/292125)) (.idx (.var 2) 0)) (.add (.mul (.const (407029316/415747)) (.idx (.var 2) 1)) (.add (.mul (.const (-653493337/162873)) (.idx (.var 2) 2)) (.const (-1419389912/995465))))))))))) (.sub (.const 1) (.const 1))))

def f671 : Formula :=
  .atom .le tm276 (.const 0)

def sq587 : Sequent := ⟨f670, f671⟩

def sq588 : Sequent := ⟨f670, f0⟩

def sq589 : Sequent := ⟨f670, f670⟩

def tm277 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3659910100/769551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (5976095356/646515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-10557842609/886926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1211673761/539353)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-717/631526)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-85897217/51801)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2738281754/292125)) (.idx (.var 2) 0)) (.add (.mul (.const (407029316/415747)) (.idx (.var 2) 1)) (.add (.mul (.const (-653493337/162873)) (.idx (.var 2) 2)) (.const (-1419389912/995465))))))))))) (.sub tm0 (.const 1))))

def f672 : Formula :=
  .atom .le tm277 (.const 0)

def sq590 : Sequent := ⟨f670, f672⟩

def sq591 : Sequent := ⟨f670, f74⟩

def tm278 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3659910100/769551)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (5976095356/646515)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-10557842609/886926)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1211673761/539353)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-717/631526)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-85897217/51801)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2738281754/292125)) (.idx (.var 2) 0)) (.add (.mul (.const (407029316/415747)) (.idx (.var 2) 1)) (.add (.mul (.const (-653493337/162873)) (.idx (.var 2) 2)) (.const (-1419389912/995465))))))))))) (.sub (.var 3) (.const 1))))

def f673 : Formula :=
  .atom .le tm278 (.const 0)

def f674 : Formula :=
  .and f670 f671

def sq592 : Sequent := ⟨f674, f245⟩

def tm279 : Term :=
  (.add (.mul (.const 200) tm276) (.const 0))

def f675 : Formula :=
  .and f0 f93

def sq593 : Sequent := ⟨f675, f245⟩

def f676 : Formula :=
  .and f0 f75

def sq594 : Sequent := ⟨f676, f245⟩

def tm280 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-879574857/910778)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727793194/800777)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1149490801/877826)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-854935327/837076)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (302888038/273473)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-83249134/344111)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (131678799/77566)) (.idx (.var 2) 0)) (.add (.mul (.const (-1789416929/796829)) (.idx (.var 2) 1)) (.add (.mul (.const (311540264/489025)) (.idx (.var 2) 2)) (.const (1032160289/978822))))))))))) (.sub (.const 1) (.const 1))))

def f677 : Formula :=
  .atom .le tm280 (.const 0)

def sq595 : Sequent := ⟨f676, f677⟩

def sq596 : Sequent := ⟨f676, f0⟩

def sq597 : Sequent := ⟨f676, f676⟩

def tm281 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-879574857/910778)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727793194/800777)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1149490801/877826)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-854935327/837076)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (302888038/273473)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-83249134/344111)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (131678799/77566)) (.idx (.var 2) 0)) (.add (.mul (.const (-1789416929/796829)) (.idx (.var 2) 1)) (.add (.mul (.const (311540264/489025)) (.idx (.var 2) 2)) (.const (1032160289/978822))))))))))) (.sub tm0 (.const 1))))

def f678 : Formula :=
  .atom .le tm281 (.const 0)

def sq598 : Sequent := ⟨f676, f678⟩

def sq599 : Sequent := ⟨f676, f75⟩

def tm282 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-879574857/910778)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727793194/800777)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1149490801/877826)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-854935327/837076)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (302888038/273473)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-83249134/344111)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (131678799/77566)) (.idx (.var 2) 0)) (.add (.mul (.const (-1789416929/796829)) (.idx (.var 2) 1)) (.add (.mul (.const (311540264/489025)) (.idx (.var 2) 2)) (.const (1032160289/978822))))))))))) (.sub (.var 3) (.const 1))))

def f679 : Formula :=
  .atom .le tm282 (.const 0)

def f680 : Formula :=
  .and f676 f677

def sq600 : Sequent := ⟨f680, f245⟩

def tm283 : Term :=
  (.add (.mul (.const 200) tm280) (.const 0))

def f681 : Formula :=
  .and f0 f92

def sq601 : Sequent := ⟨f681, f245⟩

def f682 : Formula :=
  .and f0 f76

def sq602 : Sequent := ⟨f682, f245⟩

def tm284 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-231825078/78833)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727727010/981363)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (160319957/780517)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-269369188/196653)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1816628597/995270)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (68699889/678221)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2123854341/668125)) (.idx (.var 2) 0)) (.add (.mul (.const (-2059294694/584173)) (.idx (.var 2) 1)) (.add (.mul (.const (264507365/221723)) (.idx (.var 2) 2)) (.const (852234602/509841))))))))))) (.sub (.const 1) (.const 1))))

def f683 : Formula :=
  .atom .le tm284 (.const 0)

def sq603 : Sequent := ⟨f682, f683⟩

def sq604 : Sequent := ⟨f682, f0⟩

def sq605 : Sequent := ⟨f682, f682⟩

def tm285 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-231825078/78833)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727727010/981363)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (160319957/780517)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-269369188/196653)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1816628597/995270)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (68699889/678221)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2123854341/668125)) (.idx (.var 2) 0)) (.add (.mul (.const (-2059294694/584173)) (.idx (.var 2) 1)) (.add (.mul (.const (264507365/221723)) (.idx (.var 2) 2)) (.const (852234602/509841))))))))))) (.sub tm0 (.const 1))))

def f684 : Formula :=
  .atom .le tm285 (.const 0)

def sq606 : Sequent := ⟨f682, f684⟩

def sq607 : Sequent := ⟨f682, f76⟩

def tm286 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-231825078/78833)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (1727727010/981363)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (160319957/780517)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-269369188/196653)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1816628597/995270)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (68699889/678221)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2123854341/668125)) (.idx (.var 2) 0)) (.add (.mul (.const (-2059294694/584173)) (.idx (.var 2) 1)) (.add (.mul (.const (264507365/221723)) (.idx (.var 2) 2)) (.const (852234602/509841))))))))))) (.sub (.var 3) (.const 1))))

def f685 : Formula :=
  .atom .le tm286 (.const 0)

def f686 : Formula :=
  .and f682 f683

def sq608 : Sequent := ⟨f686, f245⟩

def tm287 : Term :=
  (.add (.mul (.const 200) tm284) (.const 0))

def f687 : Formula :=
  .and f0 f91

def sq609 : Sequent := ⟨f687, f245⟩

def f688 : Formula :=
  .and f0 f77

def sq610 : Sequent := ⟨f688, f245⟩

def tm288 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3354034276/963539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-195383157/207386)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (282181623/116251)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1350691151/420404)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (892203196/716577)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1281635659/699737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (321566012/119103)) (.idx (.var 2) 0)) (.add (.mul (.const (-679560704/438505)) (.idx (.var 2) 1)) (.add (.mul (.const (-3179289310/869717)) (.idx (.var 2) 2)) (.const (147572683/458782))))))))))) (.sub (.const 1) (.const 1))))

def f689 : Formula :=
  .atom .le tm288 (.const 0)

def sq611 : Sequent := ⟨f688, f689⟩

def sq612 : Sequent := ⟨f688, f0⟩

def sq613 : Sequent := ⟨f688, f688⟩

def tm289 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3354034276/963539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-195383157/207386)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (282181623/116251)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1350691151/420404)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (892203196/716577)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1281635659/699737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (321566012/119103)) (.idx (.var 2) 0)) (.add (.mul (.const (-679560704/438505)) (.idx (.var 2) 1)) (.add (.mul (.const (-3179289310/869717)) (.idx (.var 2) 2)) (.const (147572683/458782))))))))))) (.sub tm0 (.const 1))))

def f690 : Formula :=
  .atom .le tm289 (.const 0)

def sq614 : Sequent := ⟨f688, f690⟩

def sq615 : Sequent := ⟨f688, f77⟩

def tm290 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-3354034276/963539)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-195383157/207386)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (282181623/116251)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (1350691151/420404)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (892203196/716577)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1281635659/699737)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (321566012/119103)) (.idx (.var 2) 0)) (.add (.mul (.const (-679560704/438505)) (.idx (.var 2) 1)) (.add (.mul (.const (-3179289310/869717)) (.idx (.var 2) 2)) (.const (147572683/458782))))))))))) (.sub (.var 3) (.const 1))))

def f691 : Formula :=
  .atom .le tm290 (.const 0)

def f692 : Formula :=
  .and f688 f689

def sq616 : Sequent := ⟨f692, f245⟩

def tm291 : Term :=
  (.add (.mul (.const 200) tm288) (.const 0))

def f693 : Formula :=
  .and f0 f90

def sq617 : Sequent := ⟨f693, f245⟩

def f694 : Formula :=
  .and f0 f78

def sq618 : Sequent := ⟨f694, f245⟩

def tm292 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-975874877/745482)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (22370788/513327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (90160471/703823)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12953992901/760135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-433/364969)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-4272857965/370147)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (849406882/652791)) (.idx (.var 2) 0)) (.add (.mul (.const (1574023297/597397)) (.idx (.var 2) 1)) (.add (.mul (.const (-9480050058/461741)) (.idx (.var 2) 2)) (.const (-1800702028/621343))))))))))) (.sub (.const 1) (.const 1))))

def f695 : Formula :=
  .atom .le tm292 (.const 0)

def sq619 : Sequent := ⟨f694, f695⟩

def sq620 : Sequent := ⟨f694, f0⟩

def sq621 : Sequent := ⟨f694, f694⟩

def tm293 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-975874877/745482)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (22370788/513327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (90160471/703823)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12953992901/760135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-433/364969)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-4272857965/370147)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (849406882/652791)) (.idx (.var 2) 0)) (.add (.mul (.const (1574023297/597397)) (.idx (.var 2) 1)) (.add (.mul (.const (-9480050058/461741)) (.idx (.var 2) 2)) (.const (-1800702028/621343))))))))))) (.sub tm0 (.const 1))))

def f696 : Formula :=
  .atom .le tm293 (.const 0)

def sq622 : Sequent := ⟨f694, f696⟩

def sq623 : Sequent := ⟨f694, f78⟩

def tm294 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-975874877/745482)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (22370788/513327)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (90160471/703823)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (12953992901/760135)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-433/364969)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-4272857965/370147)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (849406882/652791)) (.idx (.var 2) 0)) (.add (.mul (.const (1574023297/597397)) (.idx (.var 2) 1)) (.add (.mul (.const (-9480050058/461741)) (.idx (.var 2) 2)) (.const (-1800702028/621343))))))))))) (.sub (.var 3) (.const 1))))

def f697 : Formula :=
  .atom .le tm294 (.const 0)

def f698 : Formula :=
  .and f694 f695

def sq624 : Sequent := ⟨f698, f245⟩

def tm295 : Term :=
  (.add (.mul (.const 200) tm292) (.const 0))

def f699 : Formula :=
  .and f0 f89

def sq625 : Sequent := ⟨f699, f245⟩

def f700 : Formula :=
  .and f0 f79

def sq626 : Sequent := ⟨f700, f245⟩

def tm296 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4793377699/743900)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (899130259/734967)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-159901799/606847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1672240613/829901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (166853034/22321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (6764120021/978912)) (.idx (.var 2) 0)) (.add (.mul (.const (-7635984019/524566)) (.idx (.var 2) 1)) (.add (.mul (.const (1800668252/970313)) (.idx (.var 2) 2)) (.const (3627091921/516963))))))))))) (.sub (.const 1) (.const 1))))

def f701 : Formula :=
  .atom .le tm296 (.const 0)

def sq627 : Sequent := ⟨f700, f701⟩

def sq628 : Sequent := ⟨f700, f0⟩

def sq629 : Sequent := ⟨f700, f700⟩

def tm297 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4793377699/743900)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (899130259/734967)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-159901799/606847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1672240613/829901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (166853034/22321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (6764120021/978912)) (.idx (.var 2) 0)) (.add (.mul (.const (-7635984019/524566)) (.idx (.var 2) 1)) (.add (.mul (.const (1800668252/970313)) (.idx (.var 2) 2)) (.const (3627091921/516963))))))))))) (.sub tm0 (.const 1))))

def f702 : Formula :=
  .atom .le tm297 (.const 0)

def sq630 : Sequent := ⟨f700, f702⟩

def sq631 : Sequent := ⟨f700, f79⟩

def tm298 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-4793377699/743900)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (899130259/734967)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-159901799/606847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1672240613/829901)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (166853034/22321)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (64000/729)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (6764120021/978912)) (.idx (.var 2) 0)) (.add (.mul (.const (-7635984019/524566)) (.idx (.var 2) 1)) (.add (.mul (.const (1800668252/970313)) (.idx (.var 2) 2)) (.const (3627091921/516963))))))))))) (.sub (.var 3) (.const 1))))

def f703 : Formula :=
  .atom .le tm298 (.const 0)

def f704 : Formula :=
  .and f700 f701

def sq632 : Sequent := ⟨f704, f245⟩

def tm299 : Term :=
  (.add (.mul (.const 200) tm296) (.const 0))

def f705 : Formula :=
  .and f0 f88

def sq633 : Sequent := ⟨f705, f245⟩

def f706 : Formula :=
  .and f0 f80

def sq634 : Sequent := ⟨f706, f245⟩

def tm300 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-330118709/278432)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (6444033607/387880)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63796155515/985917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3959387819/769804)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4348/957417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1682229459/886862)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (23319205932/985951)) (.idx (.var 2) 0)) (.add (.mul (.const (1263408572/741833)) (.idx (.var 2) 1)) (.add (.mul (.const (-308994530/36051)) (.idx (.var 2) 2)) (.const (-2975182220/795197))))))))))) (.sub (.const 1) (.const 1))))

def f707 : Formula :=
  .atom .le tm300 (.const 0)

def sq635 : Sequent := ⟨f706, f707⟩

def sq636 : Sequent := ⟨f706, f0⟩

def sq637 : Sequent := ⟨f706, f706⟩

def tm301 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-330118709/278432)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (6444033607/387880)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63796155515/985917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3959387819/769804)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4348/957417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1682229459/886862)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (23319205932/985951)) (.idx (.var 2) 0)) (.add (.mul (.const (1263408572/741833)) (.idx (.var 2) 1)) (.add (.mul (.const (-308994530/36051)) (.idx (.var 2) 2)) (.const (-2975182220/795197))))))))))) (.sub tm0 (.const 1))))

def f708 : Formula :=
  .atom .le tm301 (.const 0)

def sq638 : Sequent := ⟨f706, f708⟩

def sq639 : Sequent := ⟨f706, f80⟩

def tm302 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-330118709/278432)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (6444033607/387880)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-63796155515/985917)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (3959387819/769804)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-4348/957417)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-1682229459/886862)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (23319205932/985951)) (.idx (.var 2) 0)) (.add (.mul (.const (1263408572/741833)) (.idx (.var 2) 1)) (.add (.mul (.const (-308994530/36051)) (.idx (.var 2) 2)) (.const (-2975182220/795197))))))))))) (.sub (.var 3) (.const 1))))

def f709 : Formula :=
  .atom .le tm302 (.const 0)

def f710 : Formula :=
  .and f706 f707

def sq640 : Sequent := ⟨f710, f245⟩

def tm303 : Term :=
  (.add (.mul (.const 200) tm300) (.const 0))

def f711 : Formula :=
  .and f0 f87

def sq641 : Sequent := ⟨f711, f245⟩

def f712 : Formula :=
  .and f0 f81

def sq642 : Sequent := ⟨f712, f245⟩

def tm304 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-5696192391/948650)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3064925283/600953)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-953461447/184405)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1383192121/550340)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1579849429/268443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-112572943/419234)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2989533909/325420)) (.idx (.var 2) 0)) (.add (.mul (.const (-10564328393/898580)) (.idx (.var 2) 1)) (.add (.mul (.const (1396812125/863848)) (.idx (.var 2) 2)) (.const (4595847211/836107))))))))))) (.sub (.const 1) (.const 1))))

def f713 : Formula :=
  .atom .le tm304 (.const 0)

def sq643 : Sequent := ⟨f712, f713⟩

def sq644 : Sequent := ⟨f712, f0⟩

def sq645 : Sequent := ⟨f712, f712⟩

def tm305 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-5696192391/948650)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3064925283/600953)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-953461447/184405)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1383192121/550340)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1579849429/268443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-112572943/419234)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2989533909/325420)) (.idx (.var 2) 0)) (.add (.mul (.const (-10564328393/898580)) (.idx (.var 2) 1)) (.add (.mul (.const (1396812125/863848)) (.idx (.var 2) 2)) (.const (4595847211/836107))))))))))) (.sub tm0 (.const 1))))

def f714 : Formula :=
  .atom .le tm305 (.const 0)

def sq646 : Sequent := ⟨f712, f714⟩

def sq647 : Sequent := ⟨f712, f81⟩

def tm306 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-5696192391/948650)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3064925283/600953)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-953461447/184405)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1383192121/550340)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (1579849429/268443)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-112572943/419234)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2989533909/325420)) (.idx (.var 2) 0)) (.add (.mul (.const (-10564328393/898580)) (.idx (.var 2) 1)) (.add (.mul (.const (1396812125/863848)) (.idx (.var 2) 2)) (.const (4595847211/836107))))))))))) (.sub (.var 3) (.const 1))))

def f715 : Formula :=
  .atom .le tm306 (.const 0)

def f716 : Formula :=
  .and f712 f713

def sq648 : Sequent := ⟨f716, f245⟩

def tm307 : Term :=
  (.add (.mul (.const 200) tm304) (.const 0))

def f717 : Formula :=
  .and f0 f86

def sq649 : Sequent := ⟨f717, f245⟩

def f718 : Formula :=
  .and f0 f82

def sq650 : Sequent := ⟨f718, f245⟩

def tm308 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6007669075/761064)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2219301266/854725)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1162893/23143)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1540747682/595659)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4847927742/727507)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (110447180/911789)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (751678022/86627)) (.idx (.var 2) 0)) (.add (.mul (.const (-8308734813/634517)) (.idx (.var 2) 1)) (.add (.mul (.const (143192650/61513)) (.idx (.var 2) 2)) (.const (719345177/113447))))))))))) (.sub (.const 1) (.const 1))))

def f719 : Formula :=
  .atom .le tm308 (.const 0)

def sq651 : Sequent := ⟨f718, f719⟩

def sq652 : Sequent := ⟨f718, f0⟩

def sq653 : Sequent := ⟨f718, f718⟩

def tm309 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6007669075/761064)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2219301266/854725)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1162893/23143)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1540747682/595659)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4847927742/727507)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (110447180/911789)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (751678022/86627)) (.idx (.var 2) 0)) (.add (.mul (.const (-8308734813/634517)) (.idx (.var 2) 1)) (.add (.mul (.const (143192650/61513)) (.idx (.var 2) 2)) (.const (719345177/113447))))))))))) (.sub tm0 (.const 1))))

def f720 : Formula :=
  .atom .le tm309 (.const 0)

def sq654 : Sequent := ⟨f718, f720⟩

def sq655 : Sequent := ⟨f718, f82⟩

def tm310 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-6007669075/761064)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (2219301266/854725)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-1162893/23143)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-1540747682/595659)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (4847927742/727507)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (110447180/911789)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (751678022/86627)) (.idx (.var 2) 0)) (.add (.mul (.const (-8308734813/634517)) (.idx (.var 2) 1)) (.add (.mul (.const (143192650/61513)) (.idx (.var 2) 2)) (.const (719345177/113447))))))))))) (.sub (.var 3) (.const 1))))

def f721 : Formula :=
  .atom .le tm310 (.const 0)

def f722 : Formula :=
  .and f718 f719

def sq656 : Sequent := ⟨f722, f245⟩

def tm311 : Term :=
  (.add (.mul (.const 200) tm308) (.const 0))

def f723 : Formula :=
  .and f0 f85

def sq657 : Sequent := ⟨f723, f245⟩

def f724 : Formula :=
  .and f0 f83

def sq658 : Sequent := ⟨f724, f245⟩

def tm312 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1791616056/836293)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3611661065/435918)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1281477403/858738)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-488978825/943679)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458317175/597489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-395850833/190318)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2229123091/526379)) (.idx (.var 2) 0)) (.add (.mul (.const (-1221355241/867815)) (.idx (.var 2) 1)) (.add (.mul (.const (-260886289/137667)) (.idx (.var 2) 2)) (.const (87935206/679237))))))))))) (.sub (.const 1) (.const 1))))

def f725 : Formula :=
  .atom .le tm312 (.const 0)

def sq659 : Sequent := ⟨f724, f725⟩

def sq660 : Sequent := ⟨f724, f0⟩

def sq661 : Sequent := ⟨f724, f724⟩

def tm313 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1791616056/836293)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3611661065/435918)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1281477403/858738)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-488978825/943679)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458317175/597489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-395850833/190318)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2229123091/526379)) (.idx (.var 2) 0)) (.add (.mul (.const (-1221355241/867815)) (.idx (.var 2) 1)) (.add (.mul (.const (-260886289/137667)) (.idx (.var 2) 2)) (.const (87935206/679237))))))))))) (.sub tm0 (.const 1))))

def f726 : Formula :=
  .atom .le tm313 (.const 0)

def sq662 : Sequent := ⟨f724, f726⟩

def sq663 : Sequent := ⟨f724, f83⟩

def tm314 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (-1791616056/836293)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (3611661065/435918)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (1281477403/858738)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-488978825/943679)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (458317175/597489)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-395850833/190318)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (2229123091/526379)) (.idx (.var 2) 0)) (.add (.mul (.const (-1221355241/867815)) (.idx (.var 2) 1)) (.add (.mul (.const (-260886289/137667)) (.idx (.var 2) 2)) (.const (87935206/679237))))))))))) (.sub (.var 3) (.const 1))))

def f727 : Formula :=
  .atom .le tm314 (.const 0)

def f728 : Formula :=
  .and f724 f725

def sq664 : Sequent := ⟨f728, f245⟩

def tm315 : Term :=
  (.add (.mul (.const 200) tm312) (.const 0))

def f729 : Formula :=
  .and f0 f84

def sq665 : Sequent := ⟨f729, f245⟩

def tm316 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3748110/273847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-482635957/558729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49736865/955324)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (7423105097/934333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-37136/419181)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-865465147/325430)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-21958210/78947)) (.idx (.var 2) 0)) (.add (.mul (.const (1372483361/576077)) (.idx (.var 2) 1)) (.add (.mul (.const (-4520760383/476658)) (.idx (.var 2) 2)) (.const (-1124187581/431588))))))))))) (.sub (.const 1) (.const 1))))

def f730 : Formula :=
  .atom .le tm316 (.const 0)

def sq666 : Sequent := ⟨f729, f730⟩

def sq667 : Sequent := ⟨f729, f0⟩

def sq668 : Sequent := ⟨f729, f729⟩

def tm317 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3748110/273847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-482635957/558729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49736865/955324)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (7423105097/934333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-37136/419181)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-865465147/325430)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-21958210/78947)) (.idx (.var 2) 0)) (.add (.mul (.const (1372483361/576077)) (.idx (.var 2) 1)) (.add (.mul (.const (-4520760383/476658)) (.idx (.var 2) 2)) (.const (-1124187581/431588))))))))))) (.sub tm0 (.const 1))))

def f731 : Formula :=
  .atom .le tm317 (.const 0)

def sq669 : Sequent := ⟨f729, f731⟩

def sq670 : Sequent := ⟨f729, f84⟩

def tm318 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 2) 1) (.idx (.var 2) 2)) (.idx (.var 2) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.const (1/200)))))) (.mul (.add (.mul (.const (3748110/273847)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 1))) (.add (.mul (.const (-482635957/558729)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 2))) (.add (.mul (.const (49736865/955324)) (.mul (.idx (.var 2) 0) (.idx (.var 2) 0))) (.add (.mul (.const (7423105097/934333)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 2))) (.add (.mul (.const (-37136/419181)) (.mul (.idx (.var 2) 1) (.idx (.var 2) 1))) (.add (.mul (.const (-865465147/325430)) (.mul (.idx (.var 2) 2) (.idx (.var 2) 2))) (.add (.mul (.const (-21958210/78947)) (.idx (.var 2) 0)) (.add (.mul (.const (1372483361/576077)) (.idx (.var 2) 1)) (.add (.mul (.const (-4520760383/476658)) (.idx (.var 2) 2)) (.const (-1124187581/431588))))))))))) (.sub (.var 3) (.const 1))))

def f732 : Formula :=
  .atom .le tm318 (.const 0)

def f733 : Formula :=
  .and f729 f730

def sq671 : Sequent := ⟨f733, f245⟩

def tm319 : Term :=
  (.add (.mul (.const 200) tm316) (.const 0))

def tm320 : Term :=
  (.add (.mul (.const 400) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-800)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2000)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3))))))

def f734 : Formula :=
  .atom .le tm320 (.const 0)

def sq672 : Sequent := ⟨f241, f734⟩

def f735 : Formula :=
  .and f169 f170

def sq673 : Sequent := ⟨f735, f734⟩

def tm321 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 0) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 0) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 0) 2)) (.const (286392834/561017))))))))))) (.sub (.const 1) (.const 1))))

def f736 : Formula :=
  .atom .le tm321 (.const 0)

def sq674 : Sequent := ⟨f735, f736⟩

def sq675 : Sequent := ⟨f735, f169⟩

def sq676 : Sequent := ⟨f735, f735⟩

def tm322 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 0) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 0) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 0) 2)) (.const (286392834/561017))))))))))) (.sub tm1 (.const 1))))

def f737 : Formula :=
  .atom .le tm322 (.const 0)

def sq677 : Sequent := ⟨f735, f737⟩

def sq678 : Sequent := ⟨f735, f170⟩

def tm323 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-226015880/994529)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-12221277/342113)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (14782197/788524)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (34040329/271417)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (441722767/699189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10757514/938737)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (186245656/908411)) (.idx (.var 0) 0)) (.add (.mul (.const (-868839456/765469)) (.idx (.var 0) 1)) (.add (.mul (.const (-95996452/892459)) (.idx (.var 0) 2)) (.const (286392834/561017))))))))))) (.sub (.var 1) (.const 1))))

def f738 : Formula :=
  .atom .le tm323 (.const 0)

def f739 : Formula :=
  .and f735 f736

def sq679 : Sequent := ⟨f739, f734⟩

def tm324 : Term :=
  (.add (.mul (.const 1000) tm321) (.const 0))

def f740 : Formula :=
  .and f169 f239

def sq680 : Sequent := ⟨f740, f734⟩

def f741 : Formula :=
  .and f169 f171

def sq681 : Sequent := ⟨f741, f734⟩

def tm325 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 0) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 0) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 0) 2)) (.const (2632947191/910618))))))))))) (.sub (.const 1) (.const 1))))

def f742 : Formula :=
  .atom .le tm325 (.const 0)

def sq682 : Sequent := ⟨f741, f742⟩

def sq683 : Sequent := ⟨f741, f169⟩

def sq684 : Sequent := ⟨f741, f741⟩

def tm326 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 0) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 0) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 0) 2)) (.const (2632947191/910618))))))))))) (.sub tm1 (.const 1))))

def f743 : Formula :=
  .atom .le tm326 (.const 0)

def sq685 : Sequent := ⟨f741, f743⟩

def sq686 : Sequent := ⟨f741, f171⟩

def tm327 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-29976953/222786)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (10958771/468397)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (111782/332139)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-21139187/30165)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1674752640/473893)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1952/87)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (92479629/768881)) (.idx (.var 0) 0)) (.add (.mul (.const (-6333720890/990987)) (.idx (.var 0) 1)) (.add (.mul (.const (561007405/880231)) (.idx (.var 0) 2)) (.const (2632947191/910618))))))))))) (.sub (.var 1) (.const 1))))

def f744 : Formula :=
  .atom .le tm327 (.const 0)

def f745 : Formula :=
  .and f741 f742

def sq687 : Sequent := ⟨f745, f734⟩

def tm328 : Term :=
  (.add (.mul (.const 1000) tm325) (.const 0))

def f746 : Formula :=
  .and f169 f238

def sq688 : Sequent := ⟨f746, f734⟩

def f747 : Formula :=
  .and f169 f172

def sq689 : Sequent := ⟨f747, f734⟩

def tm329 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 0) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 0) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 0) 2)) (.const (39124772/32805)))))))))) (.sub (.const 1) (.const 1))))

def f748 : Formula :=
  .atom .le tm329 (.const 0)

def sq690 : Sequent := ⟨f747, f748⟩

def sq691 : Sequent := ⟨f747, f169⟩

def sq692 : Sequent := ⟨f747, f747⟩

def tm330 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 0) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 0) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 0) 2)) (.const (39124772/32805)))))))))) (.sub tm1 (.const 1))))

def f749 : Formula :=
  .atom .le tm330 (.const 0)

def sq693 : Sequent := ⟨f747, f749⟩

def sq694 : Sequent := ⟨f747, f172⟩

def tm331 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-127984/729)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13635335/95272)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (8229112/6561)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-16058023/932298)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (127984/729)) (.idx (.var 0) 0)) (.add (.mul (.const (-2431303695/994279)) (.idx (.var 0) 1)) (.add (.mul (.const (-89936570/652723)) (.idx (.var 0) 2)) (.const (39124772/32805)))))))))) (.sub (.var 1) (.const 1))))

def f750 : Formula :=
  .atom .le tm331 (.const 0)

def f751 : Formula :=
  .and f747 f748

def sq695 : Sequent := ⟨f751, f734⟩

def tm332 : Term :=
  (.add (.mul (.const 1000) tm329) (.const 0))

def f752 : Formula :=
  .and f169 f237

def sq696 : Sequent := ⟨f752, f734⟩

def f753 : Formula :=
  .and f169 f173

def sq697 : Sequent := ⟨f753, f734⟩

def tm333 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 0) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 0) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 0) 2)) (.const (-1947116053/493198))))))))))) (.sub (.const 1) (.const 1))))

def f754 : Formula :=
  .atom .le tm333 (.const 0)

def sq698 : Sequent := ⟨f753, f754⟩

def sq699 : Sequent := ⟨f753, f169⟩

def sq700 : Sequent := ⟨f753, f753⟩

def tm334 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 0) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 0) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 0) 2)) (.const (-1947116053/493198))))))))))) (.sub tm1 (.const 1))))

def f755 : Formula :=
  .atom .le tm334 (.const 0)

def sq701 : Sequent := ⟨f753, f755⟩

def sq702 : Sequent := ⟨f753, f173⟩

def tm335 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-3720704/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-636352/6507)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1280/9)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (450198283/334861)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3273737027/746304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-200/9)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1860352/3615)) (.idx (.var 0) 0)) (.add (.mul (.const (3687400413/442424)) (.idx (.var 0) 1)) (.add (.mul (.const (-404612747/315340)) (.idx (.var 0) 2)) (.const (-1947116053/493198))))))))))) (.sub (.var 1) (.const 1))))

def f756 : Formula :=
  .atom .le tm335 (.const 0)

def f757 : Formula :=
  .and f753 f754

def sq703 : Sequent := ⟨f757, f734⟩

def tm336 : Term :=
  (.add (.mul (.const 1000) tm333) (.const 0))

def f758 : Formula :=
  .and f169 f236

def sq704 : Sequent := ⟨f758, f734⟩

def f759 : Formula :=
  .and f169 f174

def sq705 : Sequent := ⟨f759, f734⟩

def tm337 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 0) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 0) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 0) 2)) (.const (1648777036/878707))))))))))) (.sub (.const 1) (.const 1))))

def f760 : Formula :=
  .atom .le tm337 (.const 0)

def sq706 : Sequent := ⟨f759, f760⟩

def sq707 : Sequent := ⟨f759, f169⟩

def sq708 : Sequent := ⟨f759, f759⟩

def tm338 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 0) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 0) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 0) 2)) (.const (1648777036/878707))))))))))) (.sub tm1 (.const 1))))

def f761 : Formula :=
  .atom .le tm338 (.const 0)

def sq709 : Sequent := ⟨f759, f761⟩

def sq710 : Sequent := ⟨f759, f174⟩

def tm339 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-110704017/66635)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-247332340/735697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (152315207/447494)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (458313481/548300)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (1177546455/535558)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (46157996/690573)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (197056389/129374)) (.idx (.var 0) 0)) (.add (.mul (.const (-516639292/127217)) (.idx (.var 0) 1)) (.add (.mul (.const (-43952789/58328)) (.idx (.var 0) 2)) (.const (1648777036/878707))))))))))) (.sub (.var 1) (.const 1))))

def f762 : Formula :=
  .atom .le tm339 (.const 0)

def f763 : Formula :=
  .and f759 f760

def sq711 : Sequent := ⟨f763, f734⟩

def tm340 : Term :=
  (.add (.mul (.const 1000) tm337) (.const 0))

def f764 : Formula :=
  .and f169 f235

def sq712 : Sequent := ⟨f764, f734⟩

def f765 : Formula :=
  .and f169 f175

def sq713 : Sequent := ⟨f765, f734⟩

def tm341 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 0) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 0) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 0) 2)) (.const (-312678635/79278))))))))))) (.sub (.const 1) (.const 1))))

def f766 : Formula :=
  .atom .le tm341 (.const 0)

def sq714 : Sequent := ⟨f765, f766⟩

def sq715 : Sequent := ⟨f765, f169⟩

def sq716 : Sequent := ⟨f765, f765⟩

def tm342 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 0) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 0) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 0) 2)) (.const (-312678635/79278))))))))))) (.sub tm1 (.const 1))))

def f767 : Formula :=
  .atom .le tm342 (.const 0)

def sq717 : Sequent := ⟨f765, f767⟩

def sq718 : Sequent := ⟨f765, f175⟩

def tm343 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453327167/341959)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-155595477/888620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-17145760/812851)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (234381373/319515)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-4120116134/858011)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-488/39)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-729164981/603895)) (.idx (.var 0) 0)) (.add (.mul (.const (195760877/22484)) (.idx (.var 0) 1)) (.add (.mul (.const (-574064783/873087)) (.idx (.var 0) 2)) (.const (-312678635/79278))))))))))) (.sub (.var 1) (.const 1))))

def f768 : Formula :=
  .atom .le tm343 (.const 0)

def f769 : Formula :=
  .and f765 f766

def sq719 : Sequent := ⟨f769, f734⟩

def tm344 : Term :=
  (.add (.mul (.const 1000) tm341) (.const 0))

def f770 : Formula :=
  .and f169 f234

def sq720 : Sequent := ⟨f770, f734⟩

def f771 : Formula :=
  .and f169 f176

def sq721 : Sequent := ⟨f771, f734⟩

def tm345 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 0) 2)) (.const (-162864022755/580618))))))))))) (.sub (.const 1) (.const 1))))

def f772 : Formula :=
  .atom .le tm345 (.const 0)

def sq722 : Sequent := ⟨f771, f772⟩

def sq723 : Sequent := ⟨f771, f169⟩

def sq724 : Sequent := ⟨f771, f771⟩

def tm346 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 0) 2)) (.const (-162864022755/580618))))))))))) (.sub tm1 (.const 1))))

def f773 : Formula :=
  .atom .le tm346 (.const 0)

def sq725 : Sequent := ⟨f771, f773⟩

def sq726 : Sequent := ⟨f771, f176⟩

def tm347 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-17626135533/276041)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-159084232108/840351)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (30511271281/598094)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-303806720740/392173)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-857940574/112703)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (105414704099/653363)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-637223588477/622113)) (.idx (.var 0) 2)) (.const (-162864022755/580618))))))))))) (.sub (.var 1) (.const 1))))

def f774 : Formula :=
  .atom .le tm347 (.const 0)

def f775 : Formula :=
  .and f771 f772

def sq727 : Sequent := ⟨f775, f734⟩

def tm348 : Term :=
  (.add (.mul (.const 1000) tm345) (.const 0))

def f776 : Formula :=
  .and f169 f233

def sq728 : Sequent := ⟨f776, f734⟩

def f777 : Formula :=
  .and f169 f177

def sq729 : Sequent := ⟨f777, f734⟩

def tm349 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 0) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 0) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 0) 2)) (.const (32302115855/771688))))))))))) (.sub (.const 1) (.const 1))))

def f778 : Formula :=
  .atom .le tm349 (.const 0)

def sq730 : Sequent := ⟨f777, f778⟩

def sq731 : Sequent := ⟨f777, f169⟩

def sq732 : Sequent := ⟨f777, f777⟩

def tm350 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 0) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 0) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 0) 2)) (.const (32302115855/771688))))))))))) (.sub tm1 (.const 1))))

def f779 : Formula :=
  .atom .le tm350 (.const 0)

def sq733 : Sequent := ⟨f777, f779⟩

def sq734 : Sequent := ⟨f777, f177⟩

def tm351 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (3396031725/412879)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3931715872/779483)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (365538157/377228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-12907264978/214695)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (15726926141/215304)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6420383099/486962)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-2445170207/488639)) (.idx (.var 0) 0)) (.add (.mul (.const (-101882208959/926489)) (.idx (.var 0) 1)) (.add (.mul (.const (30459870808/692639)) (.idx (.var 0) 2)) (.const (32302115855/771688))))))))))) (.sub (.var 1) (.const 1))))

def f780 : Formula :=
  .atom .le tm351 (.const 0)

def f781 : Formula :=
  .and f777 f778

def sq735 : Sequent := ⟨f781, f734⟩

def tm352 : Term :=
  (.add (.mul (.const 1000) tm349) (.const 0))

def f782 : Formula :=
  .and f169 f232

def sq736 : Sequent := ⟨f782, f734⟩

def f783 : Formula :=
  .and f169 f178

def sq737 : Sequent := ⟨f783, f734⟩

def tm353 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 0) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 0) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 0) 2)) (.const (-2074194415/944191))))))))))) (.sub (.const 1) (.const 1))))

def f784 : Formula :=
  .atom .le tm353 (.const 0)

def sq738 : Sequent := ⟨f783, f784⟩

def sq739 : Sequent := ⟨f783, f169⟩

def sq740 : Sequent := ⟨f783, f783⟩

def tm354 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 0) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 0) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 0) 2)) (.const (-2074194415/944191))))))))))) (.sub tm1 (.const 1))))

def f785 : Formula :=
  .atom .le tm354 (.const 0)

def sq741 : Sequent := ⟨f783, f785⟩

def sq742 : Sequent := ⟨f783, f178⟩

def tm355 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (611079233/889262)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8467007/170402)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-23494922/484019)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (225043256/764975)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1823125865/800763)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (30573793/554803)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-667784846/989975)) (.idx (.var 0) 0)) (.add (.mul (.const (2582317771/576274)) (.idx (.var 0) 1)) (.add (.mul (.const (-45697915/136059)) (.idx (.var 0) 2)) (.const (-2074194415/944191))))))))))) (.sub (.var 1) (.const 1))))

def f786 : Formula :=
  .atom .le tm355 (.const 0)

def f787 : Formula :=
  .and f783 f784

def sq743 : Sequent := ⟨f787, f734⟩

def tm356 : Term :=
  (.add (.mul (.const 1000) tm353) (.const 0))

def f788 : Formula :=
  .and f169 f231

def sq744 : Sequent := ⟨f788, f734⟩

def f789 : Formula :=
  .and f169 f179

def sq745 : Sequent := ⟨f789, f734⟩

def tm357 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 0) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 0) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 0) 2)) (.const (-461424968/955333))))))))))) (.sub (.const 1) (.const 1))))

def f790 : Formula :=
  .atom .le tm357 (.const 0)

def sq746 : Sequent := ⟨f789, f790⟩

def sq747 : Sequent := ⟨f789, f169⟩

def sq748 : Sequent := ⟨f789, f789⟩

def tm358 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 0) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 0) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 0) 2)) (.const (-461424968/955333))))))))))) (.sub tm1 (.const 1))))

def f791 : Formula :=
  .atom .le tm358 (.const 0)

def sq749 : Sequent := ⟨f789, f791⟩

def sq750 : Sequent := ⟨f789, f179⟩

def tm359 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (440698810/852799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-85398905/289497)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (41075283/689420)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-791428778/997389)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-152068483/970623)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (38436469/127035)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-317051879/984748)) (.idx (.var 0) 0)) (.add (.mul (.const (620210411/807746)) (.idx (.var 0) 1)) (.add (.mul (.const (393837711/997484)) (.idx (.var 0) 2)) (.const (-461424968/955333))))))))))) (.sub (.var 1) (.const 1))))

def f792 : Formula :=
  .atom .le tm359 (.const 0)

def f793 : Formula :=
  .and f789 f790

def sq751 : Sequent := ⟨f793, f734⟩

def tm360 : Term :=
  (.add (.mul (.const 1000) tm357) (.const 0))

def f794 : Formula :=
  .and f169 f230

def sq752 : Sequent := ⟨f794, f734⟩

def f795 : Formula :=
  .and f169 f180

def sq753 : Sequent := ⟨f795, f734⟩

def tm361 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 0) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 0) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 0) 2)) (.const (5893227809/74342))))))))))) (.sub (.const 1) (.const 1))))

def f796 : Formula :=
  .atom .le tm361 (.const 0)

def sq754 : Sequent := ⟨f795, f796⟩

def sq755 : Sequent := ⟨f795, f169⟩

def sq756 : Sequent := ⟨f795, f795⟩

def tm362 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 0) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 0) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 0) 2)) (.const (5893227809/74342))))))))))) (.sub tm1 (.const 1))))

def f797 : Formula :=
  .atom .le tm362 (.const 0)

def sq757 : Sequent := ⟨f795, f797⟩

def sq758 : Sequent := ⟨f795, f180⟩

def tm363 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-11792183122/298245)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-296528/931)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (148555908/40343)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2824032/245)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (53909411089/738028)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-164/19)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (24239793211/621410)) (.idx (.var 0) 0)) (.add (.mul (.const (-80582404622/526843)) (.idx (.var 0) 1)) (.add (.mul (.const (-9080121779/867896)) (.idx (.var 0) 2)) (.const (5893227809/74342))))))))))) (.sub (.var 1) (.const 1))))

def f798 : Formula :=
  .atom .le tm363 (.const 0)

def f799 : Formula :=
  .and f795 f796

def sq759 : Sequent := ⟨f799, f734⟩

def tm364 : Term :=
  (.add (.mul (.const 1000) tm361) (.const 0))

def f800 : Formula :=
  .and f169 f229

def sq760 : Sequent := ⟨f800, f734⟩

def f801 : Formula :=
  .and f169 f181

def sq761 : Sequent := ⟨f801, f734⟩

def tm365 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 0) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 0) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 0) 2)) (.const (-1217853940/374393))))))))))) (.sub (.const 1) (.const 1))))

def f802 : Formula :=
  .atom .le tm365 (.const 0)

def sq762 : Sequent := ⟨f801, f802⟩

def sq763 : Sequent := ⟨f801, f169⟩

def sq764 : Sequent := ⟨f801, f801⟩

def tm366 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 0) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 0) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 0) 2)) (.const (-1217853940/374393))))))))))) (.sub tm1 (.const 1))))

def f803 : Formula :=
  .atom .le tm366 (.const 0)

def sq765 : Sequent := ⟨f801, f803⟩

def sq766 : Sequent := ⟨f801, f181⟩

def tm367 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (711424381/752067)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-123801247/718455)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19485092/440133)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (387086067/398054)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3045681658/792593)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1952/75)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-737996105/881319)) (.idx (.var 0) 0)) (.add (.mul (.const (2424846873/341732)) (.idx (.var 0) 1)) (.add (.mul (.const (-222971386/232591)) (.idx (.var 0) 2)) (.const (-1217853940/374393))))))))))) (.sub (.var 1) (.const 1))))

def f804 : Formula :=
  .atom .le tm367 (.const 0)

def f805 : Formula :=
  .and f801 f802

def sq767 : Sequent := ⟨f805, f734⟩

def tm368 : Term :=
  (.add (.mul (.const 1000) tm365) (.const 0))

def f806 : Formula :=
  .and f169 f228

def sq768 : Sequent := ⟨f806, f734⟩

def f807 : Formula :=
  .and f169 f182

def sq769 : Sequent := ⟨f807, f734⟩

def tm369 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 0) 2)) (.const (-497948639335/999993))))))))))) (.sub (.const 1) (.const 1))))

def f808 : Formula :=
  .atom .le tm369 (.const 0)

def sq770 : Sequent := ⟨f807, f808⟩

def sq771 : Sequent := ⟨f807, f169⟩

def sq772 : Sequent := ⟨f807, f807⟩

def tm370 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 0) 2)) (.const (-497948639335/999993))))))))))) (.sub tm1 (.const 1))))

def f809 : Formula :=
  .atom .le tm370 (.const 0)

def sq773 : Sequent := ⟨f807, f809⟩

def sq774 : Sequent := ⟨f807, f182⟩

def tm371 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (82151097649/495091)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7236038887/107764)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24428630331/986467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-385955194444/710609)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (245489925894/992665)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-19921784035/158993)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (97993426684/100619)) (.idx (.var 0) 2)) (.const (-497948639335/999993))))))))))) (.sub (.var 1) (.const 1))))

def f810 : Formula :=
  .atom .le tm371 (.const 0)

def f811 : Formula :=
  .and f807 f808

def sq775 : Sequent := ⟨f811, f734⟩

def tm372 : Term :=
  (.add (.mul (.const 1000) tm369) (.const 0))

def f812 : Formula :=
  .and f169 f227

def sq776 : Sequent := ⟨f812, f734⟩

def f813 : Formula :=
  .and f169 f183

def sq777 : Sequent := ⟨f813, f734⟩

def tm373 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 0) 2)) (.const (109417491763/283391))))))))))) (.sub (.const 1) (.const 1))))

def f814 : Formula :=
  .atom .le tm373 (.const 0)

def sq778 : Sequent := ⟨f813, f814⟩

def sq779 : Sequent := ⟨f813, f169⟩

def sq780 : Sequent := ⟨f813, f813⟩

def tm374 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 0) 2)) (.const (109417491763/283391))))))))))) (.sub tm1 (.const 1))))

def f815 : Formula :=
  .atom .le tm374 (.const 0)

def sq781 : Sequent := ⟨f813, f815⟩

def sq782 : Sequent := ⟨f813, f183⟩

def tm375 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (464006973689/936335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-143058585368/547701)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (65192044543/997870)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (565872437657/802338)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (276777278545/905317)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-93787927497/242797)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (269393585382/326083)) (.idx (.var 0) 2)) (.const (109417491763/283391))))))))))) (.sub (.var 1) (.const 1))))

def f816 : Formula :=
  .atom .le tm375 (.const 0)

def f817 : Formula :=
  .and f813 f814

def sq783 : Sequent := ⟨f817, f734⟩

def tm376 : Term :=
  (.add (.mul (.const 1000) tm373) (.const 0))

def f818 : Formula :=
  .and f169 f226

def sq784 : Sequent := ⟨f818, f734⟩

def f819 : Formula :=
  .and f169 f184

def sq785 : Sequent := ⟨f819, f734⟩

def tm377 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 0) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 0) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 0) 2)) (.const (-219037863/39608))))))))))) (.sub (.const 1) (.const 1))))

def f820 : Formula :=
  .atom .le tm377 (.const 0)

def sq786 : Sequent := ⟨f819, f820⟩

def sq787 : Sequent := ⟨f819, f169⟩

def sq788 : Sequent := ⟨f819, f819⟩

def tm378 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 0) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 0) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 0) 2)) (.const (-219037863/39608))))))))))) (.sub tm1 (.const 1))))

def f821 : Formula :=
  .atom .le tm378 (.const 0)

def sq789 : Sequent := ⟨f819, f821⟩

def sq790 : Sequent := ⟨f819, f184⟩

def tm379 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (180576547/112539)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17620221/691415)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-63605447/626255)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-48207321/959105)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3603125599/650770)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4820/143)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1438315495/899713)) (.idx (.var 0) 0)) (.add (.mul (.const (729629147/65925)) (.idx (.var 0) 1)) (.add (.mul (.const (11965638/308575)) (.idx (.var 0) 2)) (.const (-219037863/39608))))))))))) (.sub (.var 1) (.const 1))))

def f822 : Formula :=
  .atom .le tm379 (.const 0)

def f823 : Formula :=
  .and f819 f820

def sq791 : Sequent := ⟨f823, f734⟩

def tm380 : Term :=
  (.add (.mul (.const 1000) tm377) (.const 0))

def f824 : Formula :=
  .and f169 f225

def sq792 : Sequent := ⟨f824, f734⟩

def f825 : Formula :=
  .and f169 f185

def sq793 : Sequent := ⟨f825, f734⟩

def tm381 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 0) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 0) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 0) 2)) (.const (-111292627/64735))))))))))) (.sub (.const 1) (.const 1))))

def f826 : Formula :=
  .atom .le tm381 (.const 0)

def sq794 : Sequent := ⟨f825, f826⟩

def sq795 : Sequent := ⟨f825, f169⟩

def sq796 : Sequent := ⟨f825, f825⟩

def tm382 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 0) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 0) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 0) 2)) (.const (-111292627/64735))))))))))) (.sub tm1 (.const 1))))

def f827 : Formula :=
  .atom .le tm382 (.const 0)

def sq797 : Sequent := ⟨f825, f827⟩

def sq798 : Sequent := ⟨f825, f185⟩

def tm383 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (285919967/500228)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (1131/25)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-555771/12050)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-107080841/460798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1231855982/746321)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-121/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-485642613/837482)) (.idx (.var 0) 0)) (.add (.mul (.const (2585343212/766927)) (.idx (.var 0) 1)) (.add (.mul (.const (12592163/53771)) (.idx (.var 0) 2)) (.const (-111292627/64735))))))))))) (.sub (.var 1) (.const 1))))

def f828 : Formula :=
  .atom .le tm383 (.const 0)

def f829 : Formula :=
  .and f825 f826

def sq799 : Sequent := ⟨f829, f734⟩

def tm384 : Term :=
  (.add (.mul (.const 1000) tm381) (.const 0))

def f830 : Formula :=
  .and f169 f224

def sq800 : Sequent := ⟨f830, f734⟩

def f831 : Formula :=
  .and f169 f186

def sq801 : Sequent := ⟨f831, f734⟩

def tm385 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 0) 2)) (.const (513148022210/919633))))))))))) (.sub (.const 1) (.const 1))))

def f832 : Formula :=
  .atom .le tm385 (.const 0)

def sq802 : Sequent := ⟨f831, f832⟩

def sq803 : Sequent := ⟨f831, f169⟩

def sq804 : Sequent := ⟨f831, f831⟩

def tm386 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 0) 2)) (.const (513148022210/919633))))))))))) (.sub tm1 (.const 1))))

def f833 : Formula :=
  .atom .le tm386 (.const 0)

def sq805 : Sequent := ⟨f831, f833⟩

def sq806 : Sequent := ⟨f831, f186⟩

def tm387 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-80956068733/224412)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32490327/218600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (49441486167/905914)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (5934600923/592041)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (458076408276/934273)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (117419701/989125)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (176312325091/470699)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-4504238525/494136)) (.idx (.var 0) 2)) (.const (513148022210/919633))))))))))) (.sub (.var 1) (.const 1))))

def f834 : Formula :=
  .atom .le tm387 (.const 0)

def f835 : Formula :=
  .and f831 f832

def sq807 : Sequent := ⟨f835, f734⟩

def tm388 : Term :=
  (.add (.mul (.const 1000) tm385) (.const 0))

def f836 : Formula :=
  .and f169 f223

def sq808 : Sequent := ⟨f836, f734⟩

def f837 : Formula :=
  .and f169 f187

def sq809 : Sequent := ⟨f837, f734⟩

def tm389 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 0) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 0) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 0) 2)) (.const (-587540059/765919))))))))))) (.sub (.const 1) (.const 1))))

def f838 : Formula :=
  .atom .le tm389 (.const 0)

def sq810 : Sequent := ⟨f837, f838⟩

def sq811 : Sequent := ⟨f837, f169⟩

def sq812 : Sequent := ⟨f837, f837⟩

def tm390 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 0) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 0) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 0) 2)) (.const (-587540059/765919))))))))))) (.sub tm1 (.const 1))))

def f839 : Formula :=
  .atom .le tm390 (.const 0)

def sq813 : Sequent := ⟨f837, f839⟩

def sq814 : Sequent := ⟨f837, f187⟩

def tm391 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (43178941/371684)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-20794303/936600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1733583/453620)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (114183869/545209)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-690000371/843906)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (6516052/341403)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-31102993/281547)) (.idx (.var 0) 0)) (.add (.mul (.const (514579759/323880)) (.idx (.var 0) 1)) (.add (.mul (.const (-50210349/222829)) (.idx (.var 0) 2)) (.const (-587540059/765919))))))))))) (.sub (.var 1) (.const 1))))

def f840 : Formula :=
  .atom .le tm391 (.const 0)

def f841 : Formula :=
  .and f837 f838

def sq815 : Sequent := ⟨f841, f734⟩

def tm392 : Term :=
  (.add (.mul (.const 1000) tm389) (.const 0))

def f842 : Formula :=
  .and f169 f222

def sq816 : Sequent := ⟨f842, f734⟩

def f843 : Formula :=
  .and f169 f188

def sq817 : Sequent := ⟨f843, f734⟩

def tm393 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 0) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 0) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 0) 2)) (.const (-592173234/574199))))))))))) (.sub (.const 1) (.const 1))))

def f844 : Formula :=
  .atom .le tm393 (.const 0)

def sq818 : Sequent := ⟨f843, f844⟩

def sq819 : Sequent := ⟨f843, f169⟩

def sq820 : Sequent := ⟨f843, f843⟩

def tm394 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 0) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 0) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 0) 2)) (.const (-592173234/574199))))))))))) (.sub tm1 (.const 1))))

def f845 : Formula :=
  .atom .le tm394 (.const 0)

def sq821 : Sequent := ⟨f843, f845⟩

def sq822 : Sequent := ⟨f843, f188⟩

def tm395 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (172808598/681215)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10116025/150392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-12071992/808841)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (447031222/988085)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-156110082/139457)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8996843/392131)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-243270216/989567)) (.idx (.var 0) 0)) (.add (.mul (.const (139873259/65020)) (.idx (.var 0) 1)) (.add (.mul (.const (-63149585/150222)) (.idx (.var 0) 2)) (.const (-592173234/574199))))))))))) (.sub (.var 1) (.const 1))))

def f846 : Formula :=
  .atom .le tm395 (.const 0)

def f847 : Formula :=
  .and f843 f844

def sq823 : Sequent := ⟨f847, f734⟩

def tm396 : Term :=
  (.add (.mul (.const 1000) tm393) (.const 0))

def f848 : Formula :=
  .and f169 f221

def sq824 : Sequent := ⟨f848, f734⟩

def f849 : Formula :=
  .and f169 f189

def sq825 : Sequent := ⟨f849, f734⟩

def tm397 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 0) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 0) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 0) 2)) (.const (332709852/494053))))))))))) (.sub (.const 1) (.const 1))))

def f850 : Formula :=
  .atom .le tm397 (.const 0)

def sq826 : Sequent := ⟨f849, f850⟩

def sq827 : Sequent := ⟨f849, f169⟩

def sq828 : Sequent := ⟨f849, f849⟩

def tm398 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 0) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 0) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 0) 2)) (.const (332709852/494053))))))))))) (.sub tm1 (.const 1))))

def f851 : Formula :=
  .atom .le tm398 (.const 0)

def sq829 : Sequent := ⟨f849, f851⟩

def sq830 : Sequent := ⟨f849, f189⟩

def tm399 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (128656933/492598)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-116414372/991161)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (9556849/745393)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-490140257/805503)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (572567320/998607)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (75587095/498239)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-206946739/766016)) (.idx (.var 0) 0)) (.add (.mul (.const (-287959659/231418)) (.idx (.var 0) 1)) (.add (.mul (.const (337626155/516956)) (.idx (.var 0) 2)) (.const (332709852/494053))))))))))) (.sub (.var 1) (.const 1))))

def f852 : Formula :=
  .atom .le tm399 (.const 0)

def f853 : Formula :=
  .and f849 f850

def sq831 : Sequent := ⟨f853, f734⟩

def tm400 : Term :=
  (.add (.mul (.const 1000) tm397) (.const 0))

def f854 : Formula :=
  .and f169 f220

def sq832 : Sequent := ⟨f854, f734⟩

def f855 : Formula :=
  .and f169 f190

def sq833 : Sequent := ⟨f855, f734⟩

def tm401 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 0) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 0) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 0) 2)) (.const (138427371/316640))))))))))) (.sub (.const 1) (.const 1))))

def f856 : Formula :=
  .atom .le tm401 (.const 0)

def sq834 : Sequent := ⟨f855, f856⟩

def sq835 : Sequent := ⟨f855, f169⟩

def sq836 : Sequent := ⟨f855, f855⟩

def tm402 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 0) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 0) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 0) 2)) (.const (138427371/316640))))))))))) (.sub tm1 (.const 1))))

def f857 : Formula :=
  .atom .le tm402 (.const 0)

def sq837 : Sequent := ⟨f855, f857⟩

def sq838 : Sequent := ⟨f855, f190⟩

def tm403 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (41804359/350170)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-9095005/980659)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11771849/931811)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-179131483/826505)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (265961155/710073)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (18505885/843811)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-110736493/997363)) (.idx (.var 0) 0)) (.add (.mul (.const (-502372397/618683)) (.idx (.var 0) 1)) (.add (.mul (.const (212125917/939874)) (.idx (.var 0) 2)) (.const (138427371/316640))))))))))) (.sub (.var 1) (.const 1))))

def f858 : Formula :=
  .atom .le tm403 (.const 0)

def f859 : Formula :=
  .and f855 f856

def sq839 : Sequent := ⟨f859, f734⟩

def tm404 : Term :=
  (.add (.mul (.const 1000) tm401) (.const 0))

def f860 : Formula :=
  .and f169 f219

def sq840 : Sequent := ⟨f860, f734⟩

def f861 : Formula :=
  .and f169 f191

def sq841 : Sequent := ⟨f861, f734⟩

def tm405 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 0) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 0) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 0) 2)) (.const (-1126746000/347443))))))))))) (.sub (.const 1) (.const 1))))

def f862 : Formula :=
  .atom .le tm405 (.const 0)

def sq842 : Sequent := ⟨f861, f862⟩

def sq843 : Sequent := ⟨f861, f169⟩

def sq844 : Sequent := ⟨f861, f861⟩

def tm406 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 0) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 0) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 0) 2)) (.const (-1126746000/347443))))))))))) (.sub tm1 (.const 1))))

def f863 : Formula :=
  .atom .le tm406 (.const 0)

def sq845 : Sequent := ⟨f861, f863⟩

def sq846 : Sequent := ⟨f861, f191⟩

def tm407 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-25508423/399555)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (53397403/977100)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3211158/704567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (1500656004/981739)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-357496633/113017)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-133478519/948174)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (68342006/984493)) (.idx (.var 0) 0)) (.add (.mul (.const (1595175999/249005)) (.idx (.var 0) 1)) (.add (.mul (.const (-1376891708/887557)) (.idx (.var 0) 2)) (.const (-1126746000/347443))))))))))) (.sub (.var 1) (.const 1))))

def f864 : Formula :=
  .atom .le tm407 (.const 0)

def f865 : Formula :=
  .and f861 f862

def sq847 : Sequent := ⟨f865, f734⟩

def tm408 : Term :=
  (.add (.mul (.const 1000) tm405) (.const 0))

def f866 : Formula :=
  .and f169 f218

def sq848 : Sequent := ⟨f866, f734⟩

def f867 : Formula :=
  .and f169 f192

def sq849 : Sequent := ⟨f867, f734⟩

def tm409 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 0) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 0) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 0) 2)) (.const (292336317/533944))))))))))) (.sub (.const 1) (.const 1))))

def f868 : Formula :=
  .atom .le tm409 (.const 0)

def sq850 : Sequent := ⟨f867, f868⟩

def sq851 : Sequent := ⟨f867, f169⟩

def sq852 : Sequent := ⟨f867, f867⟩

def tm410 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 0) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 0) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 0) 2)) (.const (292336317/533944))))))))))) (.sub tm1 (.const 1))))

def f869 : Formula :=
  .atom .le tm410 (.const 0)

def sq853 : Sequent := ⟨f867, f869⟩

def sq854 : Sequent := ⟨f867, f192⟩

def tm411 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-81166951/549787)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1140553/295631)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (1103324/361303)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-37760/1467)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (310047617/488524)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (4566352/636005)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (14624552/104835)) (.idx (.var 0) 0)) (.add (.mul (.const (-745238296/632591)) (.idx (.var 0) 1)) (.add (.mul (.const (28272187/966455)) (.idx (.var 0) 2)) (.const (292336317/533944))))))))))) (.sub (.var 1) (.const 1))))

def f870 : Formula :=
  .atom .le tm411 (.const 0)

def f871 : Formula :=
  .and f867 f868

def sq855 : Sequent := ⟨f871, f734⟩

def tm412 : Term :=
  (.add (.mul (.const 1000) tm409) (.const 0))

def f872 : Formula :=
  .and f169 f217

def sq856 : Sequent := ⟨f872, f734⟩

def f873 : Formula :=
  .and f169 f193

def sq857 : Sequent := ⟨f873, f734⟩

def tm413 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 0) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 0) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 0) 2)) (.const (-275632/241))))))))))) (.sub (.const 1) (.const 1))))

def f874 : Formula :=
  .atom .le tm413 (.const 0)

def sq858 : Sequent := ⟨f873, f874⟩

def sq859 : Sequent := ⟨f873, f169⟩

def sq860 : Sequent := ⟨f873, f873⟩

def tm414 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 0) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 0) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 0) 2)) (.const (-275632/241))))))))))) (.sub tm1 (.const 1))))

def f875 : Formula :=
  .atom .le tm414 (.const 0)

def sq861 : Sequent := ⟨f873, f875⟩

def sq862 : Sequent := ⟨f873, f193⟩

def tm415 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (348920001/986614)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-320/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1920/241)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (2440/39)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-2756320/2169)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (16616969/223117)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-345978209/998413)) (.idx (.var 0) 0)) (.add (.mul (.const (5237008/2169)) (.idx (.var 0) 1)) (.add (.mul (.const (-744/13)) (.idx (.var 0) 2)) (.const (-275632/241))))))))))) (.sub (.var 1) (.const 1))))

def f876 : Formula :=
  .atom .le tm415 (.const 0)

def f877 : Formula :=
  .and f873 f874

def sq863 : Sequent := ⟨f877, f734⟩

def tm416 : Term :=
  (.add (.mul (.const 1000) tm413) (.const 0))

def f878 : Formula :=
  .and f169 f216

def sq864 : Sequent := ⟨f878, f734⟩

def f879 : Formula :=
  .and f169 f194

def sq865 : Sequent := ⟨f879, f734⟩

def tm417 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 0) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 0) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 0) 2)) (.const (139581067/49924))))))))))) (.sub (.const 1) (.const 1))))

def f880 : Formula :=
  .atom .le tm417 (.const 0)

def sq866 : Sequent := ⟨f879, f880⟩

def sq867 : Sequent := ⟨f879, f169⟩

def sq868 : Sequent := ⟨f879, f879⟩

def tm418 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 0) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 0) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 0) 2)) (.const (139581067/49924))))))))))) (.sub tm1 (.const 1))))

def f881 : Formula :=
  .atom .le tm418 (.const 0)

def sq869 : Sequent := ⟨f879, f881⟩

def sq870 : Sequent := ⟨f879, f194⟩

def tm419 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-682388015/762382)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (148779461/883961)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (24458105/989056)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-385645525/593384)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (2827414015/918337)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (116092331/127050)) (.idx (.var 0) 0)) (.add (.mul (.const (-5078246065/862467)) (.idx (.var 0) 1)) (.add (.mul (.const (417297328/724541)) (.idx (.var 0) 2)) (.const (139581067/49924))))))))))) (.sub (.var 1) (.const 1))))

def f882 : Formula :=
  .atom .le tm419 (.const 0)

def f883 : Formula :=
  .and f879 f880

def sq871 : Sequent := ⟨f883, f734⟩

def tm420 : Term :=
  (.add (.mul (.const 1000) tm417) (.const 0))

def f884 : Formula :=
  .and f169 f215

def sq872 : Sequent := ⟨f884, f734⟩

def f885 : Formula :=
  .and f169 f195

def sq873 : Sequent := ⟨f885, f734⟩

def tm421 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 0) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 0) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 0) 2)) (.const (-57714997/273133))))))))))) (.sub (.const 1) (.const 1))))

def f886 : Formula :=
  .atom .le tm421 (.const 0)

def sq874 : Sequent := ⟨f885, f886⟩

def sq875 : Sequent := ⟨f885, f169⟩

def sq876 : Sequent := ⟨f885, f885⟩

def tm422 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 0) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 0) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 0) 2)) (.const (-57714997/273133))))))))))) (.sub tm1 (.const 1))))

def f887 : Formula :=
  .atom .le tm422 (.const 0)

def sq877 : Sequent := ⟨f885, f887⟩

def sq878 : Sequent := ⟨f885, f195⟩

def tm423 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-140150393/584696)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (114225736/761451)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-24057501/496075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (259243057/760997)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (18707851/668911)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-84783257/728233)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (198980982/620431)) (.idx (.var 0) 0)) (.add (.mul (.const (93434050/618137)) (.idx (.var 0) 1)) (.add (.mul (.const (-461313291/997364)) (.idx (.var 0) 2)) (.const (-57714997/273133))))))))))) (.sub (.var 1) (.const 1))))

def f888 : Formula :=
  .atom .le tm423 (.const 0)

def f889 : Formula :=
  .and f885 f886

def sq879 : Sequent := ⟨f889, f734⟩

def tm424 : Term :=
  (.add (.mul (.const 1000) tm421) (.const 0))

def f890 : Formula :=
  .and f169 f214

def sq880 : Sequent := ⟨f890, f734⟩

def f891 : Formula :=
  .and f169 f196

def sq881 : Sequent := ⟨f891, f734⟩

def tm425 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 0) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 0) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 0) 2)) (.const (384107719/929334))))))))))) (.sub (.const 1) (.const 1))))

def f892 : Formula :=
  .atom .le tm425 (.const 0)

def sq882 : Sequent := ⟨f891, f892⟩

def sq883 : Sequent := ⟨f891, f169⟩

def sq884 : Sequent := ⟨f891, f891⟩

def tm426 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 0) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 0) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 0) 2)) (.const (384107719/929334))))))))))) (.sub tm1 (.const 1))))

def f893 : Formula :=
  .atom .le tm426 (.const 0)

def sq885 : Sequent := ⟨f891, f893⟩

def sq886 : Sequent := ⟨f891, f196⟩

def tm427 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (134914196/643353)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (19682687/244440)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-45340375/715361)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-228640883/521049)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (182718787/971625)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (36153239/996680)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-97652903/707147)) (.idx (.var 0) 0)) (.add (.mul (.const (-574865351/940800)) (.idx (.var 0) 1)) (.add (.mul (.const (253782587/570293)) (.idx (.var 0) 2)) (.const (384107719/929334))))))))))) (.sub (.var 1) (.const 1))))

def f894 : Formula :=
  .atom .le tm427 (.const 0)

def f895 : Formula :=
  .and f891 f892

def sq887 : Sequent := ⟨f895, f734⟩

def tm428 : Term :=
  (.add (.mul (.const 1000) tm425) (.const 0))

def f896 : Formula :=
  .and f169 f213

def sq888 : Sequent := ⟨f896, f734⟩

def f897 : Formula :=
  .and f169 f197

def sq889 : Sequent := ⟨f897, f734⟩

def tm429 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 0) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 0) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 0) 2)) (.const (-4049311051/930046))))))))))) (.sub (.const 1) (.const 1))))

def f898 : Formula :=
  .atom .le tm429 (.const 0)

def sq890 : Sequent := ⟨f897, f898⟩

def sq891 : Sequent := ⟨f897, f169⟩

def sq892 : Sequent := ⟨f897, f897⟩

def tm430 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 0) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 0) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 0) 2)) (.const (-4049311051/930046))))))))))) (.sub tm1 (.const 1))))

def f899 : Formula :=
  .atom .le tm430 (.const 0)

def sq893 : Sequent := ⟨f897, f899⟩

def sq894 : Sequent := ⟨f897, f197⟩

def tm431 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-153696320/544269)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (95194684/680171)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-11707042/984131)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (143490304/70995)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-1332893361/374146)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-255782613/998437)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (308550093/918865)) (.idx (.var 0) 0)) (.add (.mul (.const (7685202113/975457)) (.idx (.var 0) 1)) (.add (.mul (.const (-1748046269/787819)) (.idx (.var 0) 2)) (.const (-4049311051/930046))))))))))) (.sub (.var 1) (.const 1))))

def f900 : Formula :=
  .atom .le tm431 (.const 0)

def f901 : Formula :=
  .and f897 f898

def sq895 : Sequent := ⟨f901, f734⟩

def tm432 : Term :=
  (.add (.mul (.const 1000) tm429) (.const 0))

def f902 : Formula :=
  .and f169 f212

def sq896 : Sequent := ⟨f902, f734⟩

def f903 : Formula :=
  .and f169 f198

def sq897 : Sequent := ⟨f903, f734⟩

def tm433 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 0) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 0) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 0) 2)) (.const (189449415/537218))))))))))) (.sub (.const 1) (.const 1))))

def f904 : Formula :=
  .atom .le tm433 (.const 0)

def sq898 : Sequent := ⟨f903, f904⟩

def sq899 : Sequent := ⟨f903, f169⟩

def sq900 : Sequent := ⟨f903, f903⟩

def tm434 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 0) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 0) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 0) 2)) (.const (189449415/537218))))))))))) (.sub tm1 (.const 1))))

def f905 : Formula :=
  .atom .le tm434 (.const 0)

def sq901 : Sequent := ⟨f903, f905⟩

def sq902 : Sequent := ⟨f903, f198⟩

def tm435 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-22264007/127075)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-1192843/424371)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (13341167/955505)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (52326245/422546)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (487742260/995783)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-72077022/980761)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (7881479/49833)) (.idx (.var 0) 0)) (.add (.mul (.const (-611727569/724514)) (.idx (.var 0) 1)) (.add (.mul (.const (-164126185/967564)) (.idx (.var 0) 2)) (.const (189449415/537218))))))))))) (.sub (.var 1) (.const 1))))

def f906 : Formula :=
  .atom .le tm435 (.const 0)

def f907 : Formula :=
  .and f903 f904

def sq903 : Sequent := ⟨f907, f734⟩

def tm436 : Term :=
  (.add (.mul (.const 1000) tm433) (.const 0))

def f908 : Formula :=
  .and f169 f211

def sq904 : Sequent := ⟨f908, f734⟩

def f909 : Formula :=
  .and f169 f199

def sq905 : Sequent := ⟨f909, f734⟩

def tm437 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 0) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 0) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 0) 2)) (.const (-37780291/39382))))))))))) (.sub (.const 1) (.const 1))))

def f910 : Formula :=
  .atom .le tm437 (.const 0)

def sq906 : Sequent := ⟨f909, f910⟩

def sq907 : Sequent := ⟨f909, f169⟩

def sq908 : Sequent := ⟨f909, f909⟩

def tm438 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 0) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 0) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 0) 2)) (.const (-37780291/39382))))))))))) (.sub tm1 (.const 1))))

def f911 : Formula :=
  .atom .le tm438 (.const 0)

def sq909 : Sequent := ⟨f909, f911⟩

def sq910 : Sequent := ⟨f909, f199⟩

def tm439 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (194379890/854257)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-59270497/997020)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-5676877/627686)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (684248059/751825)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-688137854/885203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-10869932/243837)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-176637783/742405)) (.idx (.var 0) 0)) (.add (.mul (.const (1182407958/677287)) (.idx (.var 0) 1)) (.add (.mul (.const (-47263125/53026)) (.idx (.var 0) 2)) (.const (-37780291/39382))))))))))) (.sub (.var 1) (.const 1))))

def f912 : Formula :=
  .atom .le tm439 (.const 0)

def f913 : Formula :=
  .and f909 f910

def sq911 : Sequent := ⟨f913, f734⟩

def tm440 : Term :=
  (.add (.mul (.const 1000) tm437) (.const 0))

def f914 : Formula :=
  .and f169 f210

def sq912 : Sequent := ⟨f914, f734⟩

def f915 : Formula :=
  .and f169 f200

def sq913 : Sequent := ⟨f915, f734⟩

def tm441 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 0) 2)) (.const (-466647799287/897298))))))))))) (.sub (.const 1) (.const 1))))

def f916 : Formula :=
  .atom .le tm441 (.const 0)

def sq914 : Sequent := ⟨f915, f916⟩

def sq915 : Sequent := ⟨f915, f169⟩

def sq916 : Sequent := ⟨f915, f915⟩

def tm442 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 0) 2)) (.const (-466647799287/897298))))))))))) (.sub tm1 (.const 1))))

def f917 : Formula :=
  .atom .le tm442 (.const 0)

def sq917 : Sequent := ⟨f915, f917⟩

def sq918 : Sequent := ⟨f915, f200⟩

def tm443 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-340362993848/694609)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (109919586989/304358)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-113040416/225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (200448775277/987934)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (91405020031/93165)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-284962849394/309429)) (.idx (.var 0) 2)) (.const (-466647799287/897298))))))))))) (.sub (.var 1) (.const 1))))

def f918 : Formula :=
  .atom .le tm443 (.const 0)

def f919 : Formula :=
  .and f915 f916

def sq919 : Sequent := ⟨f919, f734⟩

def tm444 : Term :=
  (.add (.mul (.const 1000) tm441) (.const 0))

def f920 : Formula :=
  .and f169 f209

def sq920 : Sequent := ⟨f920, f734⟩

def f921 : Formula :=
  .and f169 f201

def sq921 : Sequent := ⟨f921, f734⟩

def tm445 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 0) 2)) (.const (270563078873/702104))))))))))) (.sub (.const 1) (.const 1))))

def f922 : Formula :=
  .atom .le tm445 (.const 0)

def sq922 : Sequent := ⟨f921, f922⟩

def sq923 : Sequent := ⟨f921, f169⟩

def sq924 : Sequent := ⟨f921, f921⟩

def tm446 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 0) 2)) (.const (270563078873/702104))))))))))) (.sub tm1 (.const 1))))

def f923 : Formula :=
  .atom .le tm446 (.const 0)

def sq925 : Sequent := ⟨f921, f923⟩

def sq926 : Sequent := ⟨f921, f201⟩

def tm447 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (89090069381/443803)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-3753961427/257302)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-34295740989/77183)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (587669036790/852521)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-124540936311/828959)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-294059640062/354269)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (265464491578/856969)) (.idx (.var 0) 2)) (.const (270563078873/702104))))))))))) (.sub (.var 1) (.const 1))))

def f924 : Formula :=
  .atom .le tm447 (.const 0)

def f925 : Formula :=
  .and f921 f922

def sq927 : Sequent := ⟨f925, f734⟩

def tm448 : Term :=
  (.add (.mul (.const 1000) tm445) (.const 0))

def f926 : Formula :=
  .and f169 f208

def sq928 : Sequent := ⟨f926, f734⟩

def f927 : Formula :=
  .and f169 f202

def sq929 : Sequent := ⟨f927, f734⟩

def tm449 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 0) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 0) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 0) 2)) (.const (-12867726179/978289))))))))))) (.sub (.const 1) (.const 1))))

def f928 : Formula :=
  .atom .le tm449 (.const 0)

def sq930 : Sequent := ⟨f927, f928⟩

def sq931 : Sequent := ⟨f927, f169⟩

def sq932 : Sequent := ⟨f927, f927⟩

def tm450 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 0) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 0) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 0) 2)) (.const (-12867726179/978289))))))))))) (.sub tm1 (.const 1))))

def f929 : Formula :=
  .atom .le tm450 (.const 0)

def sq933 : Sequent := ⟨f927, f929⟩

def sq934 : Sequent := ⟨f927, f202⟩

def tm451 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (453606501/594715)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-258046967/916283)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (20321859/377600)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (156555462/62203)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-12176591369/933286)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1936/163)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-34986909/44335)) (.idx (.var 0) 0)) (.add (.mul (.const (11336689430/432693)) (.idx (.var 0) 1)) (.add (.mul (.const (-1705217557/680604)) (.idx (.var 0) 2)) (.const (-12867726179/978289))))))))))) (.sub (.var 1) (.const 1))))

def f930 : Formula :=
  .atom .le tm451 (.const 0)

def f931 : Formula :=
  .and f927 f928

def sq935 : Sequent := ⟨f931, f734⟩

def tm452 : Term :=
  (.add (.mul (.const 1000) tm449) (.const 0))

def f932 : Formula :=
  .and f169 f207

def sq936 : Sequent := ⟨f932, f734⟩

def f933 : Formula :=
  .and f169 f203

def sq937 : Sequent := ⟨f933, f734⟩

def tm453 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 0) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 0) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 0) 2)) (.const (3744383/435))))))))))) (.sub (.const 1) (.const 1))))

def f934 : Formula :=
  .atom .le tm453 (.const 0)

def sq938 : Sequent := ⟨f933, f934⟩

def sq939 : Sequent := ⟨f933, f169⟩

def sq940 : Sequent := ⟨f933, f933⟩

def tm454 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 0) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 0) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 0) 2)) (.const (3744383/435))))))))))) (.sub tm1 (.const 1))))

def f935 : Formula :=
  .atom .le tm454 (.const 0)

def sq941 : Sequent := ⟨f933, f935⟩

def sq942 : Sequent := ⟨f933, f203⟩

def tm455 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (97238/81)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3130/27)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-320117/2430)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1967003/1080)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (11449808/1305)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (1888751/12960)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-10870/9)) (.idx (.var 0) 0)) (.add (.mul (.const (-17363290827/998948)) (.idx (.var 0) 1)) (.add (.mul (.const (1953083/1080)) (.idx (.var 0) 2)) (.const (3744383/435))))))))))) (.sub (.var 1) (.const 1))))

def f936 : Formula :=
  .atom .le tm455 (.const 0)

def f937 : Formula :=
  .and f933 f934

def sq943 : Sequent := ⟨f937, f734⟩

def tm456 : Term :=
  (.add (.mul (.const 1000) tm453) (.const 0))

def f938 : Formula :=
  .and f169 f206

def sq944 : Sequent := ⟨f938, f734⟩

def f939 : Formula :=
  .and f169 f204

def sq945 : Sequent := ⟨f939, f734⟩

def tm457 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 0) 2)) (.const (-225258249609/586834))))))))))) (.sub (.const 1) (.const 1))))

def f940 : Formula :=
  .atom .le tm457 (.const 0)

def sq946 : Sequent := ⟨f939, f940⟩

def sq947 : Sequent := ⟨f939, f169⟩

def sq948 : Sequent := ⟨f939, f939⟩

def tm458 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 0) 2)) (.const (-225258249609/586834))))))))))) (.sub tm1 (.const 1))))

def f941 : Formula :=
  .atom .le tm458 (.const 0)

def sq949 : Sequent := ⟨f939, f941⟩

def sq950 : Sequent := ⟨f939, f204⟩

def tm459 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (-309893555947/967127)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-10048/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (85881139171/843164)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (10408076961/705056)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-390081798775/586834)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (656/5)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (278154096371/728523)) (.idx (.var 0) 0)) (.add (.mul (.const 1048576) (.idx (.var 0) 1)) (.add (.mul (.const (-6855350038/482127)) (.idx (.var 0) 2)) (.const (-225258249609/586834))))))))))) (.sub (.var 1) (.const 1))))

def f942 : Formula :=
  .atom .le tm459 (.const 0)

def f943 : Formula :=
  .and f939 f940

def sq951 : Sequent := ⟨f943, f734⟩

def tm460 : Term :=
  (.add (.mul (.const 1000) tm457) (.const 0))

def f944 : Formula :=
  .and f169 f205

def sq952 : Sequent := ⟨f944, f734⟩

def tm461 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 0) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 0) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 0) 2)) (.const (-3575003239/942719))))))))))) (.sub (.const 1) (.const 1))))

def f945 : Formula :=
  .atom .le tm461 (.const 0)

def sq953 : Sequent := ⟨f944, f945⟩

def sq954 : Sequent := ⟨f944, f169⟩

def sq955 : Sequent := ⟨f944, f944⟩

def tm462 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 0) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 0) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 0) 2)) (.const (-3575003239/942719))))))))))) (.sub tm1 (.const 1))))

def f946 : Formula :=
  .atom .le tm462 (.const 0)

def sq956 : Sequent := ⟨f944, f946⟩

def sq957 : Sequent := ⟨f944, f205⟩

def tm463 : Term :=
  (.add (.add (.mul (.const (2/5)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (-4/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-8/5)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-2)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.const (-3/1000)))))) (.mul (.add (.mul (.const (216829969/190327)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (32944/4401)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-73700338/987467)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-31136/163)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-3189821532/842225)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (640/81)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-1019898230/897223)) (.idx (.var 0) 0)) (.add (.mul (.const (4212332533/555746)) (.idx (.var 0) 1)) (.add (.mul (.const (90800/489)) (.idx (.var 0) 2)) (.const (-3575003239/942719))))))))))) (.sub (.var 1) (.const 1))))

def f947 : Formula :=
  .atom .le tm463 (.const 0)

def f948 : Formula :=
  .and f944 f945

def sq958 : Sequent := ⟨f948, f734⟩

def tm464 : Term :=
  (.add (.mul (.const 1000) tm461) (.const 0))

def f949 : Formula :=
  .atom .le (.const 0) (.const 0)

def sq959 : Sequent := ⟨f243, f949⟩

def tm465 : Term :=
  (.add (.mul (.const (5/2)) tm3) (.add (.mul (.const (1/2)) tm320) (.add (.mul (.const 500) (.const 0)) (.add (.mul (.const 500) (.const 0)) (.const 0)))))

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
    (termX := (.var 2)) (simplex := sx0) (S := ex0)
    (degree := 5) (polynomial := tm5) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex0) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf5 : ProofObject Hnet sq3 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq4 pf1 sq6 pf4
    3 tm0 (.const 1) f250
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf6 : ProofObject Hnet sq8 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm7
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf7 : ProofObject Hnet sq2 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f247
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
    (termX := (.var 2)) (simplex := sx1) (S := ex1)
    (degree := 5) (polynomial := tm9) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex1) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf13 : ProofObject Hnet sq11 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq12 pf9 sq14 pf12
    3 tm0 (.const 1) f256
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf14 : ProofObject Hnet sq16 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm11
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf15 : ProofObject Hnet sq10 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f254
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
    (termX := (.var 2)) (simplex := sx2) (S := ex2)
    (degree := 5) (polynomial := tm13) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex2) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf21 : ProofObject Hnet sq19 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq20 pf17 sq22 pf20
    3 tm0 (.const 1) f262
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf22 : ProofObject Hnet sq24 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm15
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf23 : ProofObject Hnet sq18 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f260
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
    (termX := (.var 2)) (simplex := sx3) (S := ex3)
    (degree := 5) (polynomial := tm17) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex3) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf29 : ProofObject Hnet sq27 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq28 pf25 sq30 pf28
    3 tm0 (.const 1) f268
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf30 : ProofObject Hnet sq32 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm19
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf31 : ProofObject Hnet sq26 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f266
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
    (termX := (.var 2)) (simplex := sx4) (S := ex4)
    (degree := 5) (polynomial := tm21) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex4) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf37 : ProofObject Hnet sq35 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq36 pf33 sq38 pf36
    3 tm0 (.const 1) f274
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf38 : ProofObject Hnet sq40 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm23
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf39 : ProofObject Hnet sq34 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f272
    sq35 pf37 sq40 pf38
    rfl rfl rfl rfl))

def pf40 : ProofObject Hnet sq45 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf41 : ProofObject Hnet sq44 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq45 pf40 f6 rfl rfl))

def pf42 : ProofObject Hnet sq45 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf43 : ProofObject Hnet sq47 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq45 pf42 f0 rfl rfl))

def pf44 : ProofObject Hnet sq46 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq47) (regionProof := pf43)
    (termX := (.var 2)) (simplex := sx5) (S := ex5)
    (degree := 5) (polynomial := tm25) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex5) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf45 : ProofObject Hnet sq43 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq44 pf41 sq46 pf44
    3 tm0 (.const 1) f280
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf46 : ProofObject Hnet sq48 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm27
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf47 : ProofObject Hnet sq42 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f278
    sq43 pf45 sq48 pf46
    rfl rfl rfl rfl))

def pf48 : ProofObject Hnet sq53 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf49 : ProofObject Hnet sq52 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq53 pf48 f7 rfl rfl))

def pf50 : ProofObject Hnet sq53 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf51 : ProofObject Hnet sq55 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq53 pf50 f0 rfl rfl))

def pf52 : ProofObject Hnet sq54 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq55) (regionProof := pf51)
    (termX := (.var 2)) (simplex := sx6) (S := ex6)
    (degree := 5) (polynomial := tm29) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex6) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf53 : ProofObject Hnet sq51 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq52 pf49 sq54 pf52
    3 tm0 (.const 1) f286
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf54 : ProofObject Hnet sq56 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm31
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf55 : ProofObject Hnet sq50 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f284
    sq51 pf53 sq56 pf54
    rfl rfl rfl rfl))

def pf56 : ProofObject Hnet sq61 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf57 : ProofObject Hnet sq60 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq61 pf56 f8 rfl rfl))

def pf58 : ProofObject Hnet sq61 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf59 : ProofObject Hnet sq63 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq61 pf58 f0 rfl rfl))

def pf60 : ProofObject Hnet sq62 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq63) (regionProof := pf59)
    (termX := (.var 2)) (simplex := sx7) (S := ex7)
    (degree := 5) (polynomial := tm33) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex7) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf61 : ProofObject Hnet sq59 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq60 pf57 sq62 pf60
    3 tm0 (.const 1) f292
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf62 : ProofObject Hnet sq64 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm35
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf63 : ProofObject Hnet sq58 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f290
    sq59 pf61 sq64 pf62
    rfl rfl rfl rfl))

def pf64 : ProofObject Hnet sq69 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf65 : ProofObject Hnet sq68 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq69 pf64 f9 rfl rfl))

def pf66 : ProofObject Hnet sq69 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf67 : ProofObject Hnet sq71 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq69 pf66 f0 rfl rfl))

def pf68 : ProofObject Hnet sq70 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq71) (regionProof := pf67)
    (termX := (.var 2)) (simplex := sx8) (S := ex8)
    (degree := 5) (polynomial := tm37) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex8) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf69 : ProofObject Hnet sq67 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq68 pf65 sq70 pf68
    3 tm0 (.const 1) f298
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf70 : ProofObject Hnet sq72 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm39
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf71 : ProofObject Hnet sq66 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f296
    sq67 pf69 sq72 pf70
    rfl rfl rfl rfl))

def pf72 : ProofObject Hnet sq77 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf73 : ProofObject Hnet sq76 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq77 pf72 f10 rfl rfl))

def pf74 : ProofObject Hnet sq77 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf75 : ProofObject Hnet sq79 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq77 pf74 f0 rfl rfl))

def pf76 : ProofObject Hnet sq78 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq79) (regionProof := pf75)
    (termX := (.var 2)) (simplex := sx9) (S := ex9)
    (degree := 5) (polynomial := tm41) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex9) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf77 : ProofObject Hnet sq75 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq76 pf73 sq78 pf76
    3 tm0 (.const 1) f304
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf78 : ProofObject Hnet sq80 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm43
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf79 : ProofObject Hnet sq74 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f302
    sq75 pf77 sq80 pf78
    rfl rfl rfl rfl))

def pf80 : ProofObject Hnet sq85 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf81 : ProofObject Hnet sq84 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq85 pf80 f11 rfl rfl))

def pf82 : ProofObject Hnet sq85 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf83 : ProofObject Hnet sq87 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq85 pf82 f0 rfl rfl))

def pf84 : ProofObject Hnet sq86 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq87) (regionProof := pf83)
    (termX := (.var 2)) (simplex := sx10) (S := ex10)
    (degree := 5) (polynomial := tm45) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex10) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf85 : ProofObject Hnet sq83 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq84 pf81 sq86 pf84
    3 tm0 (.const 1) f310
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf86 : ProofObject Hnet sq88 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm47
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf87 : ProofObject Hnet sq82 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f308
    sq83 pf85 sq88 pf86
    rfl rfl rfl rfl))

def pf88 : ProofObject Hnet sq93 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf89 : ProofObject Hnet sq92 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq93 pf88 f12 rfl rfl))

def pf90 : ProofObject Hnet sq93 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf91 : ProofObject Hnet sq95 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq93 pf90 f0 rfl rfl))

def pf92 : ProofObject Hnet sq94 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq95) (regionProof := pf91)
    (termX := (.var 2)) (simplex := sx11) (S := ex11)
    (degree := 5) (polynomial := tm49) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex11) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf93 : ProofObject Hnet sq91 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq92 pf89 sq94 pf92
    3 tm0 (.const 1) f316
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf94 : ProofObject Hnet sq96 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm51
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf95 : ProofObject Hnet sq90 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f314
    sq91 pf93 sq96 pf94
    rfl rfl rfl rfl))

def pf96 : ProofObject Hnet sq101 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf97 : ProofObject Hnet sq100 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq101 pf96 f13 rfl rfl))

def pf98 : ProofObject Hnet sq101 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf99 : ProofObject Hnet sq103 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq101 pf98 f0 rfl rfl))

def pf100 : ProofObject Hnet sq102 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq103) (regionProof := pf99)
    (termX := (.var 2)) (simplex := sx12) (S := ex12)
    (degree := 5) (polynomial := tm53) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex12) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf101 : ProofObject Hnet sq99 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq100 pf97 sq102 pf100
    3 tm0 (.const 1) f322
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf102 : ProofObject Hnet sq104 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm55
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf103 : ProofObject Hnet sq98 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f320
    sq99 pf101 sq104 pf102
    rfl rfl rfl rfl))

def pf104 : ProofObject Hnet sq109 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf105 : ProofObject Hnet sq108 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq109 pf104 f14 rfl rfl))

def pf106 : ProofObject Hnet sq109 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf107 : ProofObject Hnet sq111 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq109 pf106 f0 rfl rfl))

def pf108 : ProofObject Hnet sq110 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq111) (regionProof := pf107)
    (termX := (.var 2)) (simplex := sx13) (S := ex13)
    (degree := 5) (polynomial := tm57) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex13) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf109 : ProofObject Hnet sq107 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq108 pf105 sq110 pf108
    3 tm0 (.const 1) f328
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf110 : ProofObject Hnet sq112 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm59
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf111 : ProofObject Hnet sq106 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f326
    sq107 pf109 sq112 pf110
    rfl rfl rfl rfl))

def pf112 : ProofObject Hnet sq117 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf113 : ProofObject Hnet sq116 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq117 pf112 f15 rfl rfl))

def pf114 : ProofObject Hnet sq117 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf115 : ProofObject Hnet sq119 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq117 pf114 f0 rfl rfl))

def pf116 : ProofObject Hnet sq118 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq119) (regionProof := pf115)
    (termX := (.var 2)) (simplex := sx14) (S := ex14)
    (degree := 5) (polynomial := tm61) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex14) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf117 : ProofObject Hnet sq115 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq116 pf113 sq118 pf116
    3 tm0 (.const 1) f334
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf118 : ProofObject Hnet sq120 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm63
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf119 : ProofObject Hnet sq114 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f332
    sq115 pf117 sq120 pf118
    rfl rfl rfl rfl))

def pf120 : ProofObject Hnet sq125 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf121 : ProofObject Hnet sq124 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq125 pf120 f16 rfl rfl))

def pf122 : ProofObject Hnet sq125 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf123 : ProofObject Hnet sq127 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq125 pf122 f0 rfl rfl))

def pf124 : ProofObject Hnet sq126 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq127) (regionProof := pf123)
    (termX := (.var 2)) (simplex := sx15) (S := ex15)
    (degree := 5) (polynomial := tm65) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex15) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf125 : ProofObject Hnet sq123 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq124 pf121 sq126 pf124
    3 tm0 (.const 1) f340
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf126 : ProofObject Hnet sq128 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm67
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf127 : ProofObject Hnet sq122 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f338
    sq123 pf125 sq128 pf126
    rfl rfl rfl rfl))

def pf128 : ProofObject Hnet sq133 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf129 : ProofObject Hnet sq132 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq133 pf128 f17 rfl rfl))

def pf130 : ProofObject Hnet sq133 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf131 : ProofObject Hnet sq135 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq133 pf130 f0 rfl rfl))

def pf132 : ProofObject Hnet sq134 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq135) (regionProof := pf131)
    (termX := (.var 2)) (simplex := sx16) (S := ex16)
    (degree := 5) (polynomial := tm69) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex16) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf133 : ProofObject Hnet sq131 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq132 pf129 sq134 pf132
    3 tm0 (.const 1) f346
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf134 : ProofObject Hnet sq136 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm71
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf135 : ProofObject Hnet sq130 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f344
    sq131 pf133 sq136 pf134
    rfl rfl rfl rfl))

def pf136 : ProofObject Hnet sq141 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf137 : ProofObject Hnet sq140 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq141 pf136 f18 rfl rfl))

def pf138 : ProofObject Hnet sq141 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf139 : ProofObject Hnet sq143 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq141 pf138 f0 rfl rfl))

def pf140 : ProofObject Hnet sq142 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq143) (regionProof := pf139)
    (termX := (.var 2)) (simplex := sx17) (S := ex17)
    (degree := 5) (polynomial := tm73) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex17) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf141 : ProofObject Hnet sq139 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq140 pf137 sq142 pf140
    3 tm0 (.const 1) f352
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf142 : ProofObject Hnet sq144 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm75
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf143 : ProofObject Hnet sq138 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f350
    sq139 pf141 sq144 pf142
    rfl rfl rfl rfl))

def pf144 : ProofObject Hnet sq149 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf145 : ProofObject Hnet sq148 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq149 pf144 f19 rfl rfl))

def pf146 : ProofObject Hnet sq149 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf147 : ProofObject Hnet sq151 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq149 pf146 f0 rfl rfl))

def pf148 : ProofObject Hnet sq150 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq151) (regionProof := pf147)
    (termX := (.var 2)) (simplex := sx18) (S := ex18)
    (degree := 5) (polynomial := tm77) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex18) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf149 : ProofObject Hnet sq147 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq148 pf145 sq150 pf148
    3 tm0 (.const 1) f358
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf150 : ProofObject Hnet sq152 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm79
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf151 : ProofObject Hnet sq146 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f356
    sq147 pf149 sq152 pf150
    rfl rfl rfl rfl))

def pf152 : ProofObject Hnet sq157 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf153 : ProofObject Hnet sq156 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq157 pf152 f20 rfl rfl))

def pf154 : ProofObject Hnet sq157 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf155 : ProofObject Hnet sq159 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq157 pf154 f0 rfl rfl))

def pf156 : ProofObject Hnet sq158 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq159) (regionProof := pf155)
    (termX := (.var 2)) (simplex := sx19) (S := ex19)
    (degree := 5) (polynomial := tm81) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex19) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf157 : ProofObject Hnet sq155 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq156 pf153 sq158 pf156
    3 tm0 (.const 1) f364
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf158 : ProofObject Hnet sq160 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm83
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf159 : ProofObject Hnet sq154 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f362
    sq155 pf157 sq160 pf158
    rfl rfl rfl rfl))

def pf160 : ProofObject Hnet sq165 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf161 : ProofObject Hnet sq164 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq165 pf160 f21 rfl rfl))

def pf162 : ProofObject Hnet sq165 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf163 : ProofObject Hnet sq167 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq165 pf162 f0 rfl rfl))

def pf164 : ProofObject Hnet sq166 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq167) (regionProof := pf163)
    (termX := (.var 2)) (simplex := sx20) (S := ex20)
    (degree := 5) (polynomial := tm85) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex20) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf165 : ProofObject Hnet sq163 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq164 pf161 sq166 pf164
    3 tm0 (.const 1) f370
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf166 : ProofObject Hnet sq168 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm87
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf167 : ProofObject Hnet sq162 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f368
    sq163 pf165 sq168 pf166
    rfl rfl rfl rfl))

def pf168 : ProofObject Hnet sq173 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf169 : ProofObject Hnet sq172 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq173 pf168 f22 rfl rfl))

def pf170 : ProofObject Hnet sq173 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf171 : ProofObject Hnet sq175 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq173 pf170 f0 rfl rfl))

def pf172 : ProofObject Hnet sq174 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq175) (regionProof := pf171)
    (termX := (.var 2)) (simplex := sx21) (S := ex21)
    (degree := 5) (polynomial := tm89) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex21) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf173 : ProofObject Hnet sq171 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq172 pf169 sq174 pf172
    3 tm0 (.const 1) f376
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf174 : ProofObject Hnet sq176 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm91
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf175 : ProofObject Hnet sq170 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f374
    sq171 pf173 sq176 pf174
    rfl rfl rfl rfl))

def pf176 : ProofObject Hnet sq181 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf177 : ProofObject Hnet sq180 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq181 pf176 f23 rfl rfl))

def pf178 : ProofObject Hnet sq181 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf179 : ProofObject Hnet sq183 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq181 pf178 f0 rfl rfl))

def pf180 : ProofObject Hnet sq182 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq183) (regionProof := pf179)
    (termX := (.var 2)) (simplex := sx22) (S := ex22)
    (degree := 5) (polynomial := tm93) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex22) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf181 : ProofObject Hnet sq179 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq180 pf177 sq182 pf180
    3 tm0 (.const 1) f382
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf182 : ProofObject Hnet sq184 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm95
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf183 : ProofObject Hnet sq178 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f380
    sq179 pf181 sq184 pf182
    rfl rfl rfl rfl))

def pf184 : ProofObject Hnet sq189 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf185 : ProofObject Hnet sq188 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq189 pf184 f24 rfl rfl))

def pf186 : ProofObject Hnet sq189 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf187 : ProofObject Hnet sq191 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq189 pf186 f0 rfl rfl))

def pf188 : ProofObject Hnet sq190 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq191) (regionProof := pf187)
    (termX := (.var 2)) (simplex := sx23) (S := ex23)
    (degree := 5) (polynomial := tm97) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex23) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf189 : ProofObject Hnet sq187 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq188 pf185 sq190 pf188
    3 tm0 (.const 1) f388
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf190 : ProofObject Hnet sq192 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm99
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf191 : ProofObject Hnet sq186 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f386
    sq187 pf189 sq192 pf190
    rfl rfl rfl rfl))

def pf192 : ProofObject Hnet sq197 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf193 : ProofObject Hnet sq196 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq197 pf192 f25 rfl rfl))

def pf194 : ProofObject Hnet sq197 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf195 : ProofObject Hnet sq199 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq197 pf194 f0 rfl rfl))

def pf196 : ProofObject Hnet sq198 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq199) (regionProof := pf195)
    (termX := (.var 2)) (simplex := sx24) (S := ex24)
    (degree := 5) (polynomial := tm101) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex24) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf197 : ProofObject Hnet sq195 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq196 pf193 sq198 pf196
    3 tm0 (.const 1) f394
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf198 : ProofObject Hnet sq200 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm103
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf199 : ProofObject Hnet sq194 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f392
    sq195 pf197 sq200 pf198
    rfl rfl rfl rfl))

def pf200 : ProofObject Hnet sq205 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf201 : ProofObject Hnet sq204 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq205 pf200 f26 rfl rfl))

def pf202 : ProofObject Hnet sq205 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf203 : ProofObject Hnet sq207 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq205 pf202 f0 rfl rfl))

def pf204 : ProofObject Hnet sq206 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq207) (regionProof := pf203)
    (termX := (.var 2)) (simplex := sx25) (S := ex25)
    (degree := 5) (polynomial := tm105) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex25) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf205 : ProofObject Hnet sq203 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq204 pf201 sq206 pf204
    3 tm0 (.const 1) f400
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf206 : ProofObject Hnet sq208 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm107
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf207 : ProofObject Hnet sq202 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f398
    sq203 pf205 sq208 pf206
    rfl rfl rfl rfl))

def pf208 : ProofObject Hnet sq213 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf209 : ProofObject Hnet sq212 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq213 pf208 f27 rfl rfl))

def pf210 : ProofObject Hnet sq213 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf211 : ProofObject Hnet sq215 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq213 pf210 f0 rfl rfl))

def pf212 : ProofObject Hnet sq214 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq215) (regionProof := pf211)
    (termX := (.var 2)) (simplex := sx26) (S := ex26)
    (degree := 5) (polynomial := tm109) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex26) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf213 : ProofObject Hnet sq211 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq212 pf209 sq214 pf212
    3 tm0 (.const 1) f406
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf214 : ProofObject Hnet sq216 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm111
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf215 : ProofObject Hnet sq210 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f404
    sq211 pf213 sq216 pf214
    rfl rfl rfl rfl))

def pf216 : ProofObject Hnet sq221 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf217 : ProofObject Hnet sq220 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq221 pf216 f28 rfl rfl))

def pf218 : ProofObject Hnet sq221 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf219 : ProofObject Hnet sq223 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq221 pf218 f0 rfl rfl))

def pf220 : ProofObject Hnet sq222 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq223) (regionProof := pf219)
    (termX := (.var 2)) (simplex := sx27) (S := ex27)
    (degree := 5) (polynomial := tm113) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex27) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf221 : ProofObject Hnet sq219 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq220 pf217 sq222 pf220
    3 tm0 (.const 1) f412
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf222 : ProofObject Hnet sq224 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm115
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf223 : ProofObject Hnet sq218 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f410
    sq219 pf221 sq224 pf222
    rfl rfl rfl rfl))

def pf224 : ProofObject Hnet sq229 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf225 : ProofObject Hnet sq228 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq229 pf224 f29 rfl rfl))

def pf226 : ProofObject Hnet sq229 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf227 : ProofObject Hnet sq231 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq229 pf226 f0 rfl rfl))

def pf228 : ProofObject Hnet sq230 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq231) (regionProof := pf227)
    (termX := (.var 2)) (simplex := sx28) (S := ex28)
    (degree := 5) (polynomial := tm117) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex28) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf229 : ProofObject Hnet sq227 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq228 pf225 sq230 pf228
    3 tm0 (.const 1) f418
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf230 : ProofObject Hnet sq232 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm119
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf231 : ProofObject Hnet sq226 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f416
    sq227 pf229 sq232 pf230
    rfl rfl rfl rfl))

def pf232 : ProofObject Hnet sq237 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf233 : ProofObject Hnet sq236 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq237 pf232 f30 rfl rfl))

def pf234 : ProofObject Hnet sq237 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf235 : ProofObject Hnet sq239 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq237 pf234 f0 rfl rfl))

def pf236 : ProofObject Hnet sq238 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq239) (regionProof := pf235)
    (termX := (.var 2)) (simplex := sx29) (S := ex29)
    (degree := 5) (polynomial := tm121) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex29) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf237 : ProofObject Hnet sq235 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq236 pf233 sq238 pf236
    3 tm0 (.const 1) f424
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf238 : ProofObject Hnet sq240 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm123
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf239 : ProofObject Hnet sq234 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f422
    sq235 pf237 sq240 pf238
    rfl rfl rfl rfl))

def pf240 : ProofObject Hnet sq245 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf241 : ProofObject Hnet sq244 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq245 pf240 f31 rfl rfl))

def pf242 : ProofObject Hnet sq245 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf243 : ProofObject Hnet sq247 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq245 pf242 f0 rfl rfl))

def pf244 : ProofObject Hnet sq246 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq247) (regionProof := pf243)
    (termX := (.var 2)) (simplex := sx30) (S := ex30)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex30) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf245 : ProofObject Hnet sq243 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq244 pf241 sq246 pf244
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf246 : ProofObject Hnet sq248 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf247 : ProofObject Hnet sq242 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq243 pf245 sq248 pf246
    rfl rfl rfl rfl))

def pf248 : ProofObject Hnet sq253 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf249 : ProofObject Hnet sq252 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq253 pf248 f32 rfl rfl))

def pf250 : ProofObject Hnet sq253 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf251 : ProofObject Hnet sq255 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq253 pf250 f0 rfl rfl))

def pf252 : ProofObject Hnet sq254 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq255) (regionProof := pf251)
    (termX := (.var 2)) (simplex := sx31) (S := ex31)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex31) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf253 : ProofObject Hnet sq251 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq252 pf249 sq254 pf252
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf254 : ProofObject Hnet sq256 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf255 : ProofObject Hnet sq250 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq251 pf253 sq256 pf254
    rfl rfl rfl rfl))

def pf256 : ProofObject Hnet sq261 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf257 : ProofObject Hnet sq260 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq261 pf256 f33 rfl rfl))

def pf258 : ProofObject Hnet sq261 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf259 : ProofObject Hnet sq263 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq261 pf258 f0 rfl rfl))

def pf260 : ProofObject Hnet sq262 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq263) (regionProof := pf259)
    (termX := (.var 2)) (simplex := sx32) (S := ex32)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex32) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf261 : ProofObject Hnet sq259 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq260 pf257 sq262 pf260
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf262 : ProofObject Hnet sq264 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf263 : ProofObject Hnet sq258 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq259 pf261 sq264 pf262
    rfl rfl rfl rfl))

def pf264 : ProofObject Hnet sq269 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf265 : ProofObject Hnet sq268 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq269 pf264 f34 rfl rfl))

def pf266 : ProofObject Hnet sq269 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf267 : ProofObject Hnet sq271 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq269 pf266 f0 rfl rfl))

def pf268 : ProofObject Hnet sq270 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq271) (regionProof := pf267)
    (termX := (.var 2)) (simplex := sx33) (S := ex33)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex33) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf269 : ProofObject Hnet sq267 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq268 pf265 sq270 pf268
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf270 : ProofObject Hnet sq272 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf271 : ProofObject Hnet sq266 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq267 pf269 sq272 pf270
    rfl rfl rfl rfl))

def pf272 : ProofObject Hnet sq277 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf273 : ProofObject Hnet sq276 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq277 pf272 f35 rfl rfl))

def pf274 : ProofObject Hnet sq277 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf275 : ProofObject Hnet sq279 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq277 pf274 f0 rfl rfl))

def pf276 : ProofObject Hnet sq278 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq279) (regionProof := pf275)
    (termX := (.var 2)) (simplex := sx34) (S := ex34)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex34) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf277 : ProofObject Hnet sq275 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq276 pf273 sq278 pf276
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf278 : ProofObject Hnet sq280 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf279 : ProofObject Hnet sq274 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq275 pf277 sq280 pf278
    rfl rfl rfl rfl))

def pf280 : ProofObject Hnet sq285 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf281 : ProofObject Hnet sq284 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq285 pf280 f36 rfl rfl))

def pf282 : ProofObject Hnet sq285 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf283 : ProofObject Hnet sq287 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq285 pf282 f0 rfl rfl))

def pf284 : ProofObject Hnet sq286 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq287) (regionProof := pf283)
    (termX := (.var 2)) (simplex := sx35) (S := ex35)
    (degree := 5) (polynomial := tm125) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex35) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf285 : ProofObject Hnet sq283 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq284 pf281 sq286 pf284
    3 tm0 (.const 1) f430
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf286 : ProofObject Hnet sq288 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm127
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf287 : ProofObject Hnet sq282 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f428
    sq283 pf285 sq288 pf286
    rfl rfl rfl rfl))

def pf288 : ProofObject Hnet sq293 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf289 : ProofObject Hnet sq292 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq293 pf288 f37 rfl rfl))

def pf290 : ProofObject Hnet sq293 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf291 : ProofObject Hnet sq295 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq293 pf290 f0 rfl rfl))

def pf292 : ProofObject Hnet sq294 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq295) (regionProof := pf291)
    (termX := (.var 2)) (simplex := sx36) (S := ex36)
    (degree := 5) (polynomial := tm129) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex36) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf293 : ProofObject Hnet sq291 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq292 pf289 sq294 pf292
    3 tm0 (.const 1) f451
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf294 : ProofObject Hnet sq296 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm131
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf295 : ProofObject Hnet sq290 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f449
    sq291 pf293 sq296 pf294
    rfl rfl rfl rfl))

def pf296 : ProofObject Hnet sq301 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf297 : ProofObject Hnet sq300 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq301 pf296 f38 rfl rfl))

def pf298 : ProofObject Hnet sq301 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf299 : ProofObject Hnet sq303 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq301 pf298 f0 rfl rfl))

def pf300 : ProofObject Hnet sq302 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq303) (regionProof := pf299)
    (termX := (.var 2)) (simplex := sx37) (S := ex37)
    (degree := 5) (polynomial := tm133) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex37) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf301 : ProofObject Hnet sq299 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq300 pf297 sq302 pf300
    3 tm0 (.const 1) f457
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf302 : ProofObject Hnet sq304 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm135
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf303 : ProofObject Hnet sq298 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f455
    sq299 pf301 sq304 pf302
    rfl rfl rfl rfl))

def pf304 : ProofObject Hnet sq309 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf305 : ProofObject Hnet sq308 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq309 pf304 f39 rfl rfl))

def pf306 : ProofObject Hnet sq309 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf307 : ProofObject Hnet sq311 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq309 pf306 f0 rfl rfl))

def pf308 : ProofObject Hnet sq310 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq311) (regionProof := pf307)
    (termX := (.var 2)) (simplex := sx38) (S := ex38)
    (degree := 5) (polynomial := tm137) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex38) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf309 : ProofObject Hnet sq307 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq308 pf305 sq310 pf308
    3 tm0 (.const 1) f463
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf310 : ProofObject Hnet sq312 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm139
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf311 : ProofObject Hnet sq306 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f461
    sq307 pf309 sq312 pf310
    rfl rfl rfl rfl))

def pf312 : ProofObject Hnet sq317 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf313 : ProofObject Hnet sq316 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq317 pf312 f40 rfl rfl))

def pf314 : ProofObject Hnet sq317 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf315 : ProofObject Hnet sq319 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq317 pf314 f0 rfl rfl))

def pf316 : ProofObject Hnet sq318 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq319) (regionProof := pf315)
    (termX := (.var 2)) (simplex := sx39) (S := ex39)
    (degree := 5) (polynomial := tm141) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex39) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf317 : ProofObject Hnet sq315 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq316 pf313 sq318 pf316
    3 tm0 (.const 1) f469
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf318 : ProofObject Hnet sq320 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm143
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf319 : ProofObject Hnet sq314 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f467
    sq315 pf317 sq320 pf318
    rfl rfl rfl rfl))

def pf320 : ProofObject Hnet sq325 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf321 : ProofObject Hnet sq324 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq325 pf320 f41 rfl rfl))

def pf322 : ProofObject Hnet sq325 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf323 : ProofObject Hnet sq327 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq325 pf322 f0 rfl rfl))

def pf324 : ProofObject Hnet sq326 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq327) (regionProof := pf323)
    (termX := (.var 2)) (simplex := sx40) (S := ex40)
    (degree := 5) (polynomial := tm145) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex40) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf325 : ProofObject Hnet sq323 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq324 pf321 sq326 pf324
    3 tm0 (.const 1) f475
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf326 : ProofObject Hnet sq328 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm147
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf327 : ProofObject Hnet sq322 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f473
    sq323 pf325 sq328 pf326
    rfl rfl rfl rfl))

def pf328 : ProofObject Hnet sq333 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf329 : ProofObject Hnet sq332 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq333 pf328 f42 rfl rfl))

def pf330 : ProofObject Hnet sq333 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf331 : ProofObject Hnet sq335 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq333 pf330 f0 rfl rfl))

def pf332 : ProofObject Hnet sq334 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq335) (regionProof := pf331)
    (termX := (.var 2)) (simplex := sx41) (S := ex41)
    (degree := 5) (polynomial := tm149) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex41) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf333 : ProofObject Hnet sq331 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq332 pf329 sq334 pf332
    3 tm0 (.const 1) f481
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf334 : ProofObject Hnet sq336 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm151
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf335 : ProofObject Hnet sq330 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f479
    sq331 pf333 sq336 pf334
    rfl rfl rfl rfl))

def pf336 : ProofObject Hnet sq341 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf337 : ProofObject Hnet sq340 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq341 pf336 f43 rfl rfl))

def pf338 : ProofObject Hnet sq341 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf339 : ProofObject Hnet sq343 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq341 pf338 f0 rfl rfl))

def pf340 : ProofObject Hnet sq342 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq343) (regionProof := pf339)
    (termX := (.var 2)) (simplex := sx42) (S := ex42)
    (degree := 5) (polynomial := tm153) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex42) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf341 : ProofObject Hnet sq339 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq340 pf337 sq342 pf340
    3 tm0 (.const 1) f487
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf342 : ProofObject Hnet sq344 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm155
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf343 : ProofObject Hnet sq338 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f485
    sq339 pf341 sq344 pf342
    rfl rfl rfl rfl))

def pf344 : ProofObject Hnet sq349 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf345 : ProofObject Hnet sq348 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq349 pf344 f44 rfl rfl))

def pf346 : ProofObject Hnet sq349 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf347 : ProofObject Hnet sq351 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq349 pf346 f0 rfl rfl))

def pf348 : ProofObject Hnet sq350 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq351) (regionProof := pf347)
    (termX := (.var 2)) (simplex := sx43) (S := ex43)
    (degree := 5) (polynomial := tm157) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex43) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf349 : ProofObject Hnet sq347 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq348 pf345 sq350 pf348
    3 tm0 (.const 1) f493
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf350 : ProofObject Hnet sq352 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm159
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf351 : ProofObject Hnet sq346 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f491
    sq347 pf349 sq352 pf350
    rfl rfl rfl rfl))

def pf352 : ProofObject Hnet sq357 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf353 : ProofObject Hnet sq356 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq357 pf352 f45 rfl rfl))

def pf354 : ProofObject Hnet sq357 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf355 : ProofObject Hnet sq359 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq357 pf354 f0 rfl rfl))

def pf356 : ProofObject Hnet sq358 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq359) (regionProof := pf355)
    (termX := (.var 2)) (simplex := sx44) (S := ex44)
    (degree := 5) (polynomial := tm161) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex44) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf357 : ProofObject Hnet sq355 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq356 pf353 sq358 pf356
    3 tm0 (.const 1) f499
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf358 : ProofObject Hnet sq360 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm163
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf359 : ProofObject Hnet sq354 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f497
    sq355 pf357 sq360 pf358
    rfl rfl rfl rfl))

def pf360 : ProofObject Hnet sq365 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf361 : ProofObject Hnet sq364 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq365 pf360 f46 rfl rfl))

def pf362 : ProofObject Hnet sq365 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf363 : ProofObject Hnet sq367 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq365 pf362 f0 rfl rfl))

def pf364 : ProofObject Hnet sq366 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq367) (regionProof := pf363)
    (termX := (.var 2)) (simplex := sx45) (S := ex45)
    (degree := 5) (polynomial := tm165) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex45) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf365 : ProofObject Hnet sq363 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq364 pf361 sq366 pf364
    3 tm0 (.const 1) f505
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf366 : ProofObject Hnet sq368 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm167
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf367 : ProofObject Hnet sq362 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f503
    sq363 pf365 sq368 pf366
    rfl rfl rfl rfl))

def pf368 : ProofObject Hnet sq373 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf369 : ProofObject Hnet sq372 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq373 pf368 f47 rfl rfl))

def pf370 : ProofObject Hnet sq373 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf371 : ProofObject Hnet sq375 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq373 pf370 f0 rfl rfl))

def pf372 : ProofObject Hnet sq374 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq375) (regionProof := pf371)
    (termX := (.var 2)) (simplex := sx46) (S := ex46)
    (degree := 5) (polynomial := tm169) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex46) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf373 : ProofObject Hnet sq371 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq372 pf369 sq374 pf372
    3 tm0 (.const 1) f511
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf374 : ProofObject Hnet sq376 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm171
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf375 : ProofObject Hnet sq370 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f509
    sq371 pf373 sq376 pf374
    rfl rfl rfl rfl))

def pf376 : ProofObject Hnet sq381 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf377 : ProofObject Hnet sq380 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq381 pf376 f48 rfl rfl))

def pf378 : ProofObject Hnet sq381 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf379 : ProofObject Hnet sq383 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq381 pf378 f0 rfl rfl))

def pf380 : ProofObject Hnet sq382 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq383) (regionProof := pf379)
    (termX := (.var 2)) (simplex := sx47) (S := ex47)
    (degree := 5) (polynomial := tm173) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex47) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf381 : ProofObject Hnet sq379 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq380 pf377 sq382 pf380
    3 tm0 (.const 1) f517
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf382 : ProofObject Hnet sq384 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm175
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf383 : ProofObject Hnet sq378 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f515
    sq379 pf381 sq384 pf382
    rfl rfl rfl rfl))

def pf384 : ProofObject Hnet sq389 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf385 : ProofObject Hnet sq388 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq389 pf384 f49 rfl rfl))

def pf386 : ProofObject Hnet sq389 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf387 : ProofObject Hnet sq391 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq389 pf386 f0 rfl rfl))

def pf388 : ProofObject Hnet sq390 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq391) (regionProof := pf387)
    (termX := (.var 2)) (simplex := sx48) (S := ex48)
    (degree := 5) (polynomial := tm177) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex48) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf389 : ProofObject Hnet sq387 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq388 pf385 sq390 pf388
    3 tm0 (.const 1) f523
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf390 : ProofObject Hnet sq392 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm179
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf391 : ProofObject Hnet sq386 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f521
    sq387 pf389 sq392 pf390
    rfl rfl rfl rfl))

def pf392 : ProofObject Hnet sq397 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf393 : ProofObject Hnet sq396 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq397 pf392 f50 rfl rfl))

def pf394 : ProofObject Hnet sq397 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf395 : ProofObject Hnet sq399 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq397 pf394 f0 rfl rfl))

def pf396 : ProofObject Hnet sq398 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq399) (regionProof := pf395)
    (termX := (.var 2)) (simplex := sx49) (S := ex49)
    (degree := 5) (polynomial := tm181) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex49) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf397 : ProofObject Hnet sq395 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq396 pf393 sq398 pf396
    3 tm0 (.const 1) f529
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf398 : ProofObject Hnet sq400 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm183
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf399 : ProofObject Hnet sq394 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f527
    sq395 pf397 sq400 pf398
    rfl rfl rfl rfl))

def pf400 : ProofObject Hnet sq405 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf401 : ProofObject Hnet sq404 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq405 pf400 f51 rfl rfl))

def pf402 : ProofObject Hnet sq405 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf403 : ProofObject Hnet sq407 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq405 pf402 f0 rfl rfl))

def pf404 : ProofObject Hnet sq406 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq407) (regionProof := pf403)
    (termX := (.var 2)) (simplex := sx50) (S := ex50)
    (degree := 5) (polynomial := tm185) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex50) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf405 : ProofObject Hnet sq403 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq404 pf401 sq406 pf404
    3 tm0 (.const 1) f535
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf406 : ProofObject Hnet sq408 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm187
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf407 : ProofObject Hnet sq402 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f533
    sq403 pf405 sq408 pf406
    rfl rfl rfl rfl))

def pf408 : ProofObject Hnet sq413 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf409 : ProofObject Hnet sq412 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq413 pf408 f52 rfl rfl))

def pf410 : ProofObject Hnet sq413 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf411 : ProofObject Hnet sq415 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq413 pf410 f0 rfl rfl))

def pf412 : ProofObject Hnet sq414 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq415) (regionProof := pf411)
    (termX := (.var 2)) (simplex := sx51) (S := ex51)
    (degree := 5) (polynomial := tm189) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex51) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf413 : ProofObject Hnet sq411 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq412 pf409 sq414 pf412
    3 tm0 (.const 1) f541
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf414 : ProofObject Hnet sq416 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm191
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf415 : ProofObject Hnet sq410 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f539
    sq411 pf413 sq416 pf414
    rfl rfl rfl rfl))

def pf416 : ProofObject Hnet sq421 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf417 : ProofObject Hnet sq420 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq421 pf416 f53 rfl rfl))

def pf418 : ProofObject Hnet sq421 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf419 : ProofObject Hnet sq423 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq421 pf418 f0 rfl rfl))

def pf420 : ProofObject Hnet sq422 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq423) (regionProof := pf419)
    (termX := (.var 2)) (simplex := sx52) (S := ex52)
    (degree := 5) (polynomial := tm193) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex52) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf421 : ProofObject Hnet sq419 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq420 pf417 sq422 pf420
    3 tm0 (.const 1) f547
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf422 : ProofObject Hnet sq424 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm195
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf423 : ProofObject Hnet sq418 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f545
    sq419 pf421 sq424 pf422
    rfl rfl rfl rfl))

def pf424 : ProofObject Hnet sq429 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf425 : ProofObject Hnet sq428 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq429 pf424 f54 rfl rfl))

def pf426 : ProofObject Hnet sq429 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf427 : ProofObject Hnet sq431 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq429 pf426 f0 rfl rfl))

def pf428 : ProofObject Hnet sq430 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq431) (regionProof := pf427)
    (termX := (.var 2)) (simplex := sx53) (S := ex53)
    (degree := 5) (polynomial := tm197) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex53) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf429 : ProofObject Hnet sq427 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq428 pf425 sq430 pf428
    3 tm0 (.const 1) f553
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf430 : ProofObject Hnet sq432 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm199
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf431 : ProofObject Hnet sq426 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f551
    sq427 pf429 sq432 pf430
    rfl rfl rfl rfl))

def pf432 : ProofObject Hnet sq437 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf433 : ProofObject Hnet sq436 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq437 pf432 f55 rfl rfl))

def pf434 : ProofObject Hnet sq437 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf435 : ProofObject Hnet sq439 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq437 pf434 f0 rfl rfl))

def pf436 : ProofObject Hnet sq438 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq439) (regionProof := pf435)
    (termX := (.var 2)) (simplex := sx54) (S := ex54)
    (degree := 5) (polynomial := tm201) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex54) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf437 : ProofObject Hnet sq435 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq436 pf433 sq438 pf436
    3 tm0 (.const 1) f559
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf438 : ProofObject Hnet sq440 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm203
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf439 : ProofObject Hnet sq434 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f557
    sq435 pf437 sq440 pf438
    rfl rfl rfl rfl))

def pf440 : ProofObject Hnet sq445 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf441 : ProofObject Hnet sq444 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq445 pf440 f56 rfl rfl))

def pf442 : ProofObject Hnet sq445 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf443 : ProofObject Hnet sq447 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq445 pf442 f0 rfl rfl))

def pf444 : ProofObject Hnet sq446 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq447) (regionProof := pf443)
    (termX := (.var 2)) (simplex := sx55) (S := ex55)
    (degree := 5) (polynomial := tm205) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex55) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf445 : ProofObject Hnet sq443 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq444 pf441 sq446 pf444
    3 tm0 (.const 1) f565
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf446 : ProofObject Hnet sq448 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm207
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf447 : ProofObject Hnet sq442 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f563
    sq443 pf445 sq448 pf446
    rfl rfl rfl rfl))

def pf448 : ProofObject Hnet sq453 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf449 : ProofObject Hnet sq452 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq453 pf448 f57 rfl rfl))

def pf450 : ProofObject Hnet sq453 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf451 : ProofObject Hnet sq455 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq453 pf450 f0 rfl rfl))

def pf452 : ProofObject Hnet sq454 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq455) (regionProof := pf451)
    (termX := (.var 2)) (simplex := sx56) (S := ex56)
    (degree := 5) (polynomial := tm209) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex56) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf453 : ProofObject Hnet sq451 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq452 pf449 sq454 pf452
    3 tm0 (.const 1) f571
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf454 : ProofObject Hnet sq456 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm211
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf455 : ProofObject Hnet sq450 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f569
    sq451 pf453 sq456 pf454
    rfl rfl rfl rfl))

def pf456 : ProofObject Hnet sq461 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf457 : ProofObject Hnet sq460 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq461 pf456 f58 rfl rfl))

def pf458 : ProofObject Hnet sq461 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf459 : ProofObject Hnet sq463 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq461 pf458 f0 rfl rfl))

def pf460 : ProofObject Hnet sq462 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq463) (regionProof := pf459)
    (termX := (.var 2)) (simplex := sx57) (S := ex57)
    (degree := 5) (polynomial := tm213) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex57) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf461 : ProofObject Hnet sq459 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq460 pf457 sq462 pf460
    3 tm0 (.const 1) f577
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf462 : ProofObject Hnet sq464 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm215
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf463 : ProofObject Hnet sq458 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f575
    sq459 pf461 sq464 pf462
    rfl rfl rfl rfl))

def pf464 : ProofObject Hnet sq469 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf465 : ProofObject Hnet sq468 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq469 pf464 f59 rfl rfl))

def pf466 : ProofObject Hnet sq469 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf467 : ProofObject Hnet sq471 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq469 pf466 f0 rfl rfl))

def pf468 : ProofObject Hnet sq470 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq471) (regionProof := pf467)
    (termX := (.var 2)) (simplex := sx58) (S := ex58)
    (degree := 5) (polynomial := tm217) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex58) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf469 : ProofObject Hnet sq467 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq468 pf465 sq470 pf468
    3 tm0 (.const 1) f583
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf470 : ProofObject Hnet sq472 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm219
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf471 : ProofObject Hnet sq466 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f581
    sq467 pf469 sq472 pf470
    rfl rfl rfl rfl))

def pf472 : ProofObject Hnet sq477 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf473 : ProofObject Hnet sq476 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq477 pf472 f60 rfl rfl))

def pf474 : ProofObject Hnet sq477 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf475 : ProofObject Hnet sq479 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq477 pf474 f0 rfl rfl))

def pf476 : ProofObject Hnet sq478 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq479) (regionProof := pf475)
    (termX := (.var 2)) (simplex := sx59) (S := ex59)
    (degree := 5) (polynomial := tm221) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex59) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf477 : ProofObject Hnet sq475 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq476 pf473 sq478 pf476
    3 tm0 (.const 1) f589
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf478 : ProofObject Hnet sq480 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm223
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf479 : ProofObject Hnet sq474 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f587
    sq475 pf477 sq480 pf478
    rfl rfl rfl rfl))

def pf480 : ProofObject Hnet sq485 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf481 : ProofObject Hnet sq484 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq485 pf480 f61 rfl rfl))

def pf482 : ProofObject Hnet sq485 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf483 : ProofObject Hnet sq487 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq485 pf482 f0 rfl rfl))

def pf484 : ProofObject Hnet sq486 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq487) (regionProof := pf483)
    (termX := (.var 2)) (simplex := sx60) (S := ex60)
    (degree := 5) (polynomial := tm225) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex60) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf485 : ProofObject Hnet sq483 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq484 pf481 sq486 pf484
    3 tm0 (.const 1) f595
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf486 : ProofObject Hnet sq488 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm227
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf487 : ProofObject Hnet sq482 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f593
    sq483 pf485 sq488 pf486
    rfl rfl rfl rfl))

def pf488 : ProofObject Hnet sq493 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf489 : ProofObject Hnet sq492 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq493 pf488 f62 rfl rfl))

def pf490 : ProofObject Hnet sq493 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf491 : ProofObject Hnet sq495 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq493 pf490 f0 rfl rfl))

def pf492 : ProofObject Hnet sq494 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq495) (regionProof := pf491)
    (termX := (.var 2)) (simplex := sx61) (S := ex61)
    (degree := 5) (polynomial := tm229) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex61) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf493 : ProofObject Hnet sq491 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq492 pf489 sq494 pf492
    3 tm0 (.const 1) f601
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf494 : ProofObject Hnet sq496 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm231
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf495 : ProofObject Hnet sq490 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f599
    sq491 pf493 sq496 pf494
    rfl rfl rfl rfl))

def pf496 : ProofObject Hnet sq501 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf497 : ProofObject Hnet sq500 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq501 pf496 f63 rfl rfl))

def pf498 : ProofObject Hnet sq501 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf499 : ProofObject Hnet sq503 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq501 pf498 f0 rfl rfl))

def pf500 : ProofObject Hnet sq502 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq503) (regionProof := pf499)
    (termX := (.var 2)) (simplex := sx62) (S := ex62)
    (degree := 5) (polynomial := tm233) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex62) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf501 : ProofObject Hnet sq499 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq500 pf497 sq502 pf500
    3 tm0 (.const 1) f607
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf502 : ProofObject Hnet sq504 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm235
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf503 : ProofObject Hnet sq498 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f605
    sq499 pf501 sq504 pf502
    rfl rfl rfl rfl))

def pf504 : ProofObject Hnet sq509 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf505 : ProofObject Hnet sq508 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq509 pf504 f64 rfl rfl))

def pf506 : ProofObject Hnet sq509 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf507 : ProofObject Hnet sq511 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq509 pf506 f0 rfl rfl))

def pf508 : ProofObject Hnet sq510 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq511) (regionProof := pf507)
    (termX := (.var 2)) (simplex := sx63) (S := ex63)
    (degree := 5) (polynomial := tm237) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex63) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf509 : ProofObject Hnet sq507 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq508 pf505 sq510 pf508
    3 tm0 (.const 1) f613
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf510 : ProofObject Hnet sq512 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm239
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf511 : ProofObject Hnet sq506 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f611
    sq507 pf509 sq512 pf510
    rfl rfl rfl rfl))

def pf512 : ProofObject Hnet sq517 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf513 : ProofObject Hnet sq516 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq517 pf512 f65 rfl rfl))

def pf514 : ProofObject Hnet sq517 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf515 : ProofObject Hnet sq519 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq517 pf514 f0 rfl rfl))

def pf516 : ProofObject Hnet sq518 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq519) (regionProof := pf515)
    (termX := (.var 2)) (simplex := sx64) (S := ex64)
    (degree := 5) (polynomial := tm241) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex64) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf517 : ProofObject Hnet sq515 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq516 pf513 sq518 pf516
    3 tm0 (.const 1) f619
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf518 : ProofObject Hnet sq520 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm243
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf519 : ProofObject Hnet sq514 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f617
    sq515 pf517 sq520 pf518
    rfl rfl rfl rfl))

def pf520 : ProofObject Hnet sq525 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf521 : ProofObject Hnet sq524 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq525 pf520 f66 rfl rfl))

def pf522 : ProofObject Hnet sq525 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf523 : ProofObject Hnet sq527 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq525 pf522 f0 rfl rfl))

def pf524 : ProofObject Hnet sq526 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq527) (regionProof := pf523)
    (termX := (.var 2)) (simplex := sx65) (S := ex65)
    (degree := 5) (polynomial := tm245) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex65) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf525 : ProofObject Hnet sq523 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq524 pf521 sq526 pf524
    3 tm0 (.const 1) f625
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf526 : ProofObject Hnet sq528 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm247
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf527 : ProofObject Hnet sq522 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f623
    sq523 pf525 sq528 pf526
    rfl rfl rfl rfl))

def pf528 : ProofObject Hnet sq533 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf529 : ProofObject Hnet sq532 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq533 pf528 f67 rfl rfl))

def pf530 : ProofObject Hnet sq533 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf531 : ProofObject Hnet sq535 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq533 pf530 f0 rfl rfl))

def pf532 : ProofObject Hnet sq534 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq535) (regionProof := pf531)
    (termX := (.var 2)) (simplex := sx66) (S := ex66)
    (degree := 5) (polynomial := tm249) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex66) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf533 : ProofObject Hnet sq531 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq532 pf529 sq534 pf532
    3 tm0 (.const 1) f631
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf534 : ProofObject Hnet sq536 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm251
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf535 : ProofObject Hnet sq530 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f629
    sq531 pf533 sq536 pf534
    rfl rfl rfl rfl))

def pf536 : ProofObject Hnet sq541 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf537 : ProofObject Hnet sq540 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq541 pf536 f68 rfl rfl))

def pf538 : ProofObject Hnet sq541 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf539 : ProofObject Hnet sq543 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq541 pf538 f0 rfl rfl))

def pf540 : ProofObject Hnet sq542 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq543) (regionProof := pf539)
    (termX := (.var 2)) (simplex := sx67) (S := ex67)
    (degree := 5) (polynomial := tm253) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex67) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf541 : ProofObject Hnet sq539 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq540 pf537 sq542 pf540
    3 tm0 (.const 1) f637
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf542 : ProofObject Hnet sq544 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm255
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf543 : ProofObject Hnet sq538 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f635
    sq539 pf541 sq544 pf542
    rfl rfl rfl rfl))

def pf544 : ProofObject Hnet sq549 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf545 : ProofObject Hnet sq548 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq549 pf544 f69 rfl rfl))

def pf546 : ProofObject Hnet sq549 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf547 : ProofObject Hnet sq551 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq549 pf546 f0 rfl rfl))

def pf548 : ProofObject Hnet sq550 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq551) (regionProof := pf547)
    (termX := (.var 2)) (simplex := sx68) (S := ex68)
    (degree := 5) (polynomial := tm257) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex68) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf549 : ProofObject Hnet sq547 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq548 pf545 sq550 pf548
    3 tm0 (.const 1) f643
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf550 : ProofObject Hnet sq552 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm259
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf551 : ProofObject Hnet sq546 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f641
    sq547 pf549 sq552 pf550
    rfl rfl rfl rfl))

def pf552 : ProofObject Hnet sq557 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf553 : ProofObject Hnet sq556 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq557 pf552 f70 rfl rfl))

def pf554 : ProofObject Hnet sq557 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf555 : ProofObject Hnet sq559 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq557 pf554 f0 rfl rfl))

def pf556 : ProofObject Hnet sq558 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq559) (regionProof := pf555)
    (termX := (.var 2)) (simplex := sx69) (S := ex69)
    (degree := 5) (polynomial := tm261) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex69) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf557 : ProofObject Hnet sq555 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq556 pf553 sq558 pf556
    3 tm0 (.const 1) f649
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf558 : ProofObject Hnet sq560 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm263
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf559 : ProofObject Hnet sq554 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f647
    sq555 pf557 sq560 pf558
    rfl rfl rfl rfl))

def pf560 : ProofObject Hnet sq565 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf561 : ProofObject Hnet sq564 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq565 pf560 f71 rfl rfl))

def pf562 : ProofObject Hnet sq565 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf563 : ProofObject Hnet sq567 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq565 pf562 f0 rfl rfl))

def pf564 : ProofObject Hnet sq566 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq567) (regionProof := pf563)
    (termX := (.var 2)) (simplex := sx70) (S := ex70)
    (degree := 5) (polynomial := tm265) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex70) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf565 : ProofObject Hnet sq563 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq564 pf561 sq566 pf564
    3 tm0 (.const 1) f655
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf566 : ProofObject Hnet sq568 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm267
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf567 : ProofObject Hnet sq562 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f653
    sq563 pf565 sq568 pf566
    rfl rfl rfl rfl))

def pf568 : ProofObject Hnet sq573 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf569 : ProofObject Hnet sq572 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq573 pf568 f72 rfl rfl))

def pf570 : ProofObject Hnet sq573 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf571 : ProofObject Hnet sq575 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq573 pf570 f0 rfl rfl))

def pf572 : ProofObject Hnet sq574 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq575) (regionProof := pf571)
    (termX := (.var 2)) (simplex := sx71) (S := ex71)
    (degree := 5) (polynomial := tm269) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex71) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf573 : ProofObject Hnet sq571 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq572 pf569 sq574 pf572
    3 tm0 (.const 1) f661
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf574 : ProofObject Hnet sq576 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm271
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf575 : ProofObject Hnet sq570 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f659
    sq571 pf573 sq576 pf574
    rfl rfl rfl rfl))

def pf576 : ProofObject Hnet sq581 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf577 : ProofObject Hnet sq580 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq581 pf576 f73 rfl rfl))

def pf578 : ProofObject Hnet sq581 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf579 : ProofObject Hnet sq583 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq581 pf578 f0 rfl rfl))

def pf580 : ProofObject Hnet sq582 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq583) (regionProof := pf579)
    (termX := (.var 2)) (simplex := sx72) (S := ex72)
    (degree := 5) (polynomial := tm273) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex72) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf581 : ProofObject Hnet sq579 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq580 pf577 sq582 pf580
    3 tm0 (.const 1) f667
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf582 : ProofObject Hnet sq584 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm275
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf583 : ProofObject Hnet sq578 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f665
    sq579 pf581 sq584 pf582
    rfl rfl rfl rfl))

def pf584 : ProofObject Hnet sq589 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf585 : ProofObject Hnet sq588 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq589 pf584 f74 rfl rfl))

def pf586 : ProofObject Hnet sq589 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf587 : ProofObject Hnet sq591 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq589 pf586 f0 rfl rfl))

def pf588 : ProofObject Hnet sq590 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq591) (regionProof := pf587)
    (termX := (.var 2)) (simplex := sx73) (S := ex73)
    (degree := 5) (polynomial := tm277) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex73) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf589 : ProofObject Hnet sq587 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq588 pf585 sq590 pf588
    3 tm0 (.const 1) f673
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf590 : ProofObject Hnet sq592 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm279
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf591 : ProofObject Hnet sq586 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f671
    sq587 pf589 sq592 pf590
    rfl rfl rfl rfl))

def pf592 : ProofObject Hnet sq597 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf593 : ProofObject Hnet sq596 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq597 pf592 f75 rfl rfl))

def pf594 : ProofObject Hnet sq597 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf595 : ProofObject Hnet sq599 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq597 pf594 f0 rfl rfl))

def pf596 : ProofObject Hnet sq598 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq599) (regionProof := pf595)
    (termX := (.var 2)) (simplex := sx74) (S := ex74)
    (degree := 5) (polynomial := tm281) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex74) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf597 : ProofObject Hnet sq595 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq596 pf593 sq598 pf596
    3 tm0 (.const 1) f679
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf598 : ProofObject Hnet sq600 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm283
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf599 : ProofObject Hnet sq594 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f677
    sq595 pf597 sq600 pf598
    rfl rfl rfl rfl))

def pf600 : ProofObject Hnet sq605 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf601 : ProofObject Hnet sq604 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq605 pf600 f76 rfl rfl))

def pf602 : ProofObject Hnet sq605 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf603 : ProofObject Hnet sq607 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq605 pf602 f0 rfl rfl))

def pf604 : ProofObject Hnet sq606 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq607) (regionProof := pf603)
    (termX := (.var 2)) (simplex := sx75) (S := ex75)
    (degree := 5) (polynomial := tm285) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex75) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf605 : ProofObject Hnet sq603 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq604 pf601 sq606 pf604
    3 tm0 (.const 1) f685
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf606 : ProofObject Hnet sq608 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm287
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf607 : ProofObject Hnet sq602 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f683
    sq603 pf605 sq608 pf606
    rfl rfl rfl rfl))

def pf608 : ProofObject Hnet sq613 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf609 : ProofObject Hnet sq612 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq613 pf608 f77 rfl rfl))

def pf610 : ProofObject Hnet sq613 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf611 : ProofObject Hnet sq615 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq613 pf610 f0 rfl rfl))

def pf612 : ProofObject Hnet sq614 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq615) (regionProof := pf611)
    (termX := (.var 2)) (simplex := sx76) (S := ex76)
    (degree := 5) (polynomial := tm289) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex76) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf613 : ProofObject Hnet sq611 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq612 pf609 sq614 pf612
    3 tm0 (.const 1) f691
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf614 : ProofObject Hnet sq616 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm291
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf615 : ProofObject Hnet sq610 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f689
    sq611 pf613 sq616 pf614
    rfl rfl rfl rfl))

def pf616 : ProofObject Hnet sq621 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf617 : ProofObject Hnet sq620 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq621 pf616 f78 rfl rfl))

def pf618 : ProofObject Hnet sq621 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf619 : ProofObject Hnet sq623 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq621 pf618 f0 rfl rfl))

def pf620 : ProofObject Hnet sq622 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq623) (regionProof := pf619)
    (termX := (.var 2)) (simplex := sx77) (S := ex77)
    (degree := 5) (polynomial := tm293) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex77) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf621 : ProofObject Hnet sq619 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq620 pf617 sq622 pf620
    3 tm0 (.const 1) f697
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf622 : ProofObject Hnet sq624 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm295
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf623 : ProofObject Hnet sq618 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f695
    sq619 pf621 sq624 pf622
    rfl rfl rfl rfl))

def pf624 : ProofObject Hnet sq629 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf625 : ProofObject Hnet sq628 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq629 pf624 f79 rfl rfl))

def pf626 : ProofObject Hnet sq629 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf627 : ProofObject Hnet sq631 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq629 pf626 f0 rfl rfl))

def pf628 : ProofObject Hnet sq630 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq631) (regionProof := pf627)
    (termX := (.var 2)) (simplex := sx78) (S := ex78)
    (degree := 5) (polynomial := tm297) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex78) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf629 : ProofObject Hnet sq627 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq628 pf625 sq630 pf628
    3 tm0 (.const 1) f703
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf630 : ProofObject Hnet sq632 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm299
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf631 : ProofObject Hnet sq626 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f701
    sq627 pf629 sq632 pf630
    rfl rfl rfl rfl))

def pf632 : ProofObject Hnet sq637 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf633 : ProofObject Hnet sq636 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq637 pf632 f80 rfl rfl))

def pf634 : ProofObject Hnet sq637 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf635 : ProofObject Hnet sq639 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq637 pf634 f0 rfl rfl))

def pf636 : ProofObject Hnet sq638 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq639) (regionProof := pf635)
    (termX := (.var 2)) (simplex := sx79) (S := ex79)
    (degree := 5) (polynomial := tm301) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex79) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf637 : ProofObject Hnet sq635 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq636 pf633 sq638 pf636
    3 tm0 (.const 1) f709
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf638 : ProofObject Hnet sq640 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm303
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf639 : ProofObject Hnet sq634 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f707
    sq635 pf637 sq640 pf638
    rfl rfl rfl rfl))

def pf640 : ProofObject Hnet sq645 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf641 : ProofObject Hnet sq644 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq645 pf640 f81 rfl rfl))

def pf642 : ProofObject Hnet sq645 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf643 : ProofObject Hnet sq647 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq645 pf642 f0 rfl rfl))

def pf644 : ProofObject Hnet sq646 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq647) (regionProof := pf643)
    (termX := (.var 2)) (simplex := sx80) (S := ex80)
    (degree := 5) (polynomial := tm305) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex80) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf645 : ProofObject Hnet sq643 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq644 pf641 sq646 pf644
    3 tm0 (.const 1) f715
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf646 : ProofObject Hnet sq648 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm307
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf647 : ProofObject Hnet sq642 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f713
    sq643 pf645 sq648 pf646
    rfl rfl rfl rfl))

def pf648 : ProofObject Hnet sq653 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf649 : ProofObject Hnet sq652 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq653 pf648 f82 rfl rfl))

def pf650 : ProofObject Hnet sq653 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf651 : ProofObject Hnet sq655 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq653 pf650 f0 rfl rfl))

def pf652 : ProofObject Hnet sq654 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq655) (regionProof := pf651)
    (termX := (.var 2)) (simplex := sx81) (S := ex81)
    (degree := 5) (polynomial := tm309) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex81) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf653 : ProofObject Hnet sq651 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq652 pf649 sq654 pf652
    3 tm0 (.const 1) f721
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf654 : ProofObject Hnet sq656 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm311
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf655 : ProofObject Hnet sq650 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f719
    sq651 pf653 sq656 pf654
    rfl rfl rfl rfl))

def pf656 : ProofObject Hnet sq661 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf657 : ProofObject Hnet sq660 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq661 pf656 f83 rfl rfl))

def pf658 : ProofObject Hnet sq661 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf659 : ProofObject Hnet sq663 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq661 pf658 f0 rfl rfl))

def pf660 : ProofObject Hnet sq662 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq663) (regionProof := pf659)
    (termX := (.var 2)) (simplex := sx82) (S := ex82)
    (degree := 5) (polynomial := tm313) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex82) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf661 : ProofObject Hnet sq659 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq660 pf657 sq662 pf660
    3 tm0 (.const 1) f727
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf662 : ProofObject Hnet sq664 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm315
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf663 : ProofObject Hnet sq658 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f725
    sq659 pf661 sq664 pf662
    rfl rfl rfl rfl))

def pf664 : ProofObject Hnet sq668 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf665 : ProofObject Hnet sq667 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq668 pf664 f84 rfl rfl))

def pf666 : ProofObject Hnet sq668 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf667 : ProofObject Hnet sq670 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq668 pf666 f0 rfl rfl))

def pf668 : ProofObject Hnet sq669 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq670) (regionProof := pf667)
    (termX := (.var 2)) (simplex := sx83) (S := ex83)
    (degree := 5) (polynomial := tm317) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨2, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex83) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf669 : ProofObject Hnet sq666 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq667 pf665 sq669 pf668
    3 tm0 (.const 1) f732
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf670 : ProofObject Hnet sq671 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm319
    tm3
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf671 : ProofObject Hnet sq665 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f730
    sq666 pf669 sq671 pf670
    rfl rfl rfl rfl))

theorem v0 : (sq658).semanticallyValid Hnet := (pf663).sound

theorem v1 : (sq665).semanticallyValid Hnet := (pf671).sound

def st0 : OrECtxStep where
  seq := sq657
  leftPremise := sq658
  rightPremise := sq665
  path := .right (.here)
  d₁ := f83
  d₂ := f84
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v2 : (sq657).semanticallyValid Hnet :=
  sound_orECtx st0 v0 v1

theorem v3 : (sq650).semanticallyValid Hnet := (pf655).sound

def st1 : OrECtxStep where
  seq := sq649
  leftPremise := sq650
  rightPremise := sq657
  path := .right (.here)
  d₁ := f82
  d₂ := f85
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v4 : (sq649).semanticallyValid Hnet :=
  sound_orECtx st1 v3 v2

theorem v5 : (sq642).semanticallyValid Hnet := (pf647).sound

def st2 : OrECtxStep where
  seq := sq641
  leftPremise := sq642
  rightPremise := sq649
  path := .right (.here)
  d₁ := f81
  d₂ := f86
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v6 : (sq641).semanticallyValid Hnet :=
  sound_orECtx st2 v5 v4

theorem v7 : (sq634).semanticallyValid Hnet := (pf639).sound

def st3 : OrECtxStep where
  seq := sq633
  leftPremise := sq634
  rightPremise := sq641
  path := .right (.here)
  d₁ := f80
  d₂ := f87
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v8 : (sq633).semanticallyValid Hnet :=
  sound_orECtx st3 v7 v6

theorem v9 : (sq626).semanticallyValid Hnet := (pf631).sound

def st4 : OrECtxStep where
  seq := sq625
  leftPremise := sq626
  rightPremise := sq633
  path := .right (.here)
  d₁ := f79
  d₂ := f88
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v10 : (sq625).semanticallyValid Hnet :=
  sound_orECtx st4 v9 v8

theorem v11 : (sq618).semanticallyValid Hnet := (pf623).sound

def st5 : OrECtxStep where
  seq := sq617
  leftPremise := sq618
  rightPremise := sq625
  path := .right (.here)
  d₁ := f78
  d₂ := f89
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v12 : (sq617).semanticallyValid Hnet :=
  sound_orECtx st5 v11 v10

theorem v13 : (sq610).semanticallyValid Hnet := (pf615).sound

def st6 : OrECtxStep where
  seq := sq609
  leftPremise := sq610
  rightPremise := sq617
  path := .right (.here)
  d₁ := f77
  d₂ := f90
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v14 : (sq609).semanticallyValid Hnet :=
  sound_orECtx st6 v13 v12

theorem v15 : (sq602).semanticallyValid Hnet := (pf607).sound

def st7 : OrECtxStep where
  seq := sq601
  leftPremise := sq602
  rightPremise := sq609
  path := .right (.here)
  d₁ := f76
  d₂ := f91
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v16 : (sq601).semanticallyValid Hnet :=
  sound_orECtx st7 v15 v14

theorem v17 : (sq594).semanticallyValid Hnet := (pf599).sound

def st8 : OrECtxStep where
  seq := sq593
  leftPremise := sq594
  rightPremise := sq601
  path := .right (.here)
  d₁ := f75
  d₂ := f92
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v18 : (sq593).semanticallyValid Hnet :=
  sound_orECtx st8 v17 v16

theorem v19 : (sq586).semanticallyValid Hnet := (pf591).sound

def st9 : OrECtxStep where
  seq := sq585
  leftPremise := sq586
  rightPremise := sq593
  path := .right (.here)
  d₁ := f74
  d₂ := f93
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v20 : (sq585).semanticallyValid Hnet :=
  sound_orECtx st9 v19 v18

theorem v21 : (sq578).semanticallyValid Hnet := (pf583).sound

def st10 : OrECtxStep where
  seq := sq577
  leftPremise := sq578
  rightPremise := sq585
  path := .right (.here)
  d₁ := f73
  d₂ := f94
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v22 : (sq577).semanticallyValid Hnet :=
  sound_orECtx st10 v21 v20

theorem v23 : (sq570).semanticallyValid Hnet := (pf575).sound

def st11 : OrECtxStep where
  seq := sq569
  leftPremise := sq570
  rightPremise := sq577
  path := .right (.here)
  d₁ := f72
  d₂ := f95
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v24 : (sq569).semanticallyValid Hnet :=
  sound_orECtx st11 v23 v22

theorem v25 : (sq562).semanticallyValid Hnet := (pf567).sound

def st12 : OrECtxStep where
  seq := sq561
  leftPremise := sq562
  rightPremise := sq569
  path := .right (.here)
  d₁ := f71
  d₂ := f96
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v26 : (sq561).semanticallyValid Hnet :=
  sound_orECtx st12 v25 v24

theorem v27 : (sq554).semanticallyValid Hnet := (pf559).sound

def st13 : OrECtxStep where
  seq := sq553
  leftPremise := sq554
  rightPremise := sq561
  path := .right (.here)
  d₁ := f70
  d₂ := f97
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v28 : (sq553).semanticallyValid Hnet :=
  sound_orECtx st13 v27 v26

theorem v29 : (sq546).semanticallyValid Hnet := (pf551).sound

def st14 : OrECtxStep where
  seq := sq545
  leftPremise := sq546
  rightPremise := sq553
  path := .right (.here)
  d₁ := f69
  d₂ := f98
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v30 : (sq545).semanticallyValid Hnet :=
  sound_orECtx st14 v29 v28

theorem v31 : (sq538).semanticallyValid Hnet := (pf543).sound

def st15 : OrECtxStep where
  seq := sq537
  leftPremise := sq538
  rightPremise := sq545
  path := .right (.here)
  d₁ := f68
  d₂ := f99
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v32 : (sq537).semanticallyValid Hnet :=
  sound_orECtx st15 v31 v30

theorem v33 : (sq530).semanticallyValid Hnet := (pf535).sound

def st16 : OrECtxStep where
  seq := sq529
  leftPremise := sq530
  rightPremise := sq537
  path := .right (.here)
  d₁ := f67
  d₂ := f100
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v34 : (sq529).semanticallyValid Hnet :=
  sound_orECtx st16 v33 v32

theorem v35 : (sq522).semanticallyValid Hnet := (pf527).sound

def st17 : OrECtxStep where
  seq := sq521
  leftPremise := sq522
  rightPremise := sq529
  path := .right (.here)
  d₁ := f66
  d₂ := f101
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v36 : (sq521).semanticallyValid Hnet :=
  sound_orECtx st17 v35 v34

theorem v37 : (sq514).semanticallyValid Hnet := (pf519).sound

def st18 : OrECtxStep where
  seq := sq513
  leftPremise := sq514
  rightPremise := sq521
  path := .right (.here)
  d₁ := f65
  d₂ := f102
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v38 : (sq513).semanticallyValid Hnet :=
  sound_orECtx st18 v37 v36

theorem v39 : (sq506).semanticallyValid Hnet := (pf511).sound

def st19 : OrECtxStep where
  seq := sq505
  leftPremise := sq506
  rightPremise := sq513
  path := .right (.here)
  d₁ := f64
  d₂ := f103
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v40 : (sq505).semanticallyValid Hnet :=
  sound_orECtx st19 v39 v38

theorem v41 : (sq498).semanticallyValid Hnet := (pf503).sound

def st20 : OrECtxStep where
  seq := sq497
  leftPremise := sq498
  rightPremise := sq505
  path := .right (.here)
  d₁ := f63
  d₂ := f104
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v42 : (sq497).semanticallyValid Hnet :=
  sound_orECtx st20 v41 v40

theorem v43 : (sq490).semanticallyValid Hnet := (pf495).sound

def st21 : OrECtxStep where
  seq := sq489
  leftPremise := sq490
  rightPremise := sq497
  path := .right (.here)
  d₁ := f62
  d₂ := f105
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v44 : (sq489).semanticallyValid Hnet :=
  sound_orECtx st21 v43 v42

theorem v45 : (sq482).semanticallyValid Hnet := (pf487).sound

def st22 : OrECtxStep where
  seq := sq481
  leftPremise := sq482
  rightPremise := sq489
  path := .right (.here)
  d₁ := f61
  d₂ := f106
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v46 : (sq481).semanticallyValid Hnet :=
  sound_orECtx st22 v45 v44

theorem v47 : (sq474).semanticallyValid Hnet := (pf479).sound

def st23 : OrECtxStep where
  seq := sq473
  leftPremise := sq474
  rightPremise := sq481
  path := .right (.here)
  d₁ := f60
  d₂ := f107
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v48 : (sq473).semanticallyValid Hnet :=
  sound_orECtx st23 v47 v46

theorem v49 : (sq466).semanticallyValid Hnet := (pf471).sound

def st24 : OrECtxStep where
  seq := sq465
  leftPremise := sq466
  rightPremise := sq473
  path := .right (.here)
  d₁ := f59
  d₂ := f108
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v50 : (sq465).semanticallyValid Hnet :=
  sound_orECtx st24 v49 v48

theorem v51 : (sq458).semanticallyValid Hnet := (pf463).sound

def st25 : OrECtxStep where
  seq := sq457
  leftPremise := sq458
  rightPremise := sq465
  path := .right (.here)
  d₁ := f58
  d₂ := f109
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v52 : (sq457).semanticallyValid Hnet :=
  sound_orECtx st25 v51 v50

theorem v53 : (sq450).semanticallyValid Hnet := (pf455).sound

def st26 : OrECtxStep where
  seq := sq449
  leftPremise := sq450
  rightPremise := sq457
  path := .right (.here)
  d₁ := f57
  d₂ := f110
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v54 : (sq449).semanticallyValid Hnet :=
  sound_orECtx st26 v53 v52

theorem v55 : (sq442).semanticallyValid Hnet := (pf447).sound

def st27 : OrECtxStep where
  seq := sq441
  leftPremise := sq442
  rightPremise := sq449
  path := .right (.here)
  d₁ := f56
  d₂ := f111
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v56 : (sq441).semanticallyValid Hnet :=
  sound_orECtx st27 v55 v54

theorem v57 : (sq434).semanticallyValid Hnet := (pf439).sound

def st28 : OrECtxStep where
  seq := sq433
  leftPremise := sq434
  rightPremise := sq441
  path := .right (.here)
  d₁ := f55
  d₂ := f112
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v58 : (sq433).semanticallyValid Hnet :=
  sound_orECtx st28 v57 v56

theorem v59 : (sq426).semanticallyValid Hnet := (pf431).sound

def st29 : OrECtxStep where
  seq := sq425
  leftPremise := sq426
  rightPremise := sq433
  path := .right (.here)
  d₁ := f54
  d₂ := f113
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v60 : (sq425).semanticallyValid Hnet :=
  sound_orECtx st29 v59 v58

theorem v61 : (sq418).semanticallyValid Hnet := (pf423).sound

def st30 : OrECtxStep where
  seq := sq417
  leftPremise := sq418
  rightPremise := sq425
  path := .right (.here)
  d₁ := f53
  d₂ := f114
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v62 : (sq417).semanticallyValid Hnet :=
  sound_orECtx st30 v61 v60

theorem v63 : (sq410).semanticallyValid Hnet := (pf415).sound

def st31 : OrECtxStep where
  seq := sq409
  leftPremise := sq410
  rightPremise := sq417
  path := .right (.here)
  d₁ := f52
  d₂ := f115
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v64 : (sq409).semanticallyValid Hnet :=
  sound_orECtx st31 v63 v62

theorem v65 : (sq402).semanticallyValid Hnet := (pf407).sound

def st32 : OrECtxStep where
  seq := sq401
  leftPremise := sq402
  rightPremise := sq409
  path := .right (.here)
  d₁ := f51
  d₂ := f116
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v66 : (sq401).semanticallyValid Hnet :=
  sound_orECtx st32 v65 v64

theorem v67 : (sq394).semanticallyValid Hnet := (pf399).sound

def st33 : OrECtxStep where
  seq := sq393
  leftPremise := sq394
  rightPremise := sq401
  path := .right (.here)
  d₁ := f50
  d₂ := f117
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v68 : (sq393).semanticallyValid Hnet :=
  sound_orECtx st33 v67 v66

theorem v69 : (sq386).semanticallyValid Hnet := (pf391).sound

def st34 : OrECtxStep where
  seq := sq385
  leftPremise := sq386
  rightPremise := sq393
  path := .right (.here)
  d₁ := f49
  d₂ := f118
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v70 : (sq385).semanticallyValid Hnet :=
  sound_orECtx st34 v69 v68

theorem v71 : (sq378).semanticallyValid Hnet := (pf383).sound

def st35 : OrECtxStep where
  seq := sq377
  leftPremise := sq378
  rightPremise := sq385
  path := .right (.here)
  d₁ := f48
  d₂ := f119
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v72 : (sq377).semanticallyValid Hnet :=
  sound_orECtx st35 v71 v70

theorem v73 : (sq370).semanticallyValid Hnet := (pf375).sound

def st36 : OrECtxStep where
  seq := sq369
  leftPremise := sq370
  rightPremise := sq377
  path := .right (.here)
  d₁ := f47
  d₂ := f120
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v74 : (sq369).semanticallyValid Hnet :=
  sound_orECtx st36 v73 v72

theorem v75 : (sq362).semanticallyValid Hnet := (pf367).sound

def st37 : OrECtxStep where
  seq := sq361
  leftPremise := sq362
  rightPremise := sq369
  path := .right (.here)
  d₁ := f46
  d₂ := f121
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v76 : (sq361).semanticallyValid Hnet :=
  sound_orECtx st37 v75 v74

theorem v77 : (sq354).semanticallyValid Hnet := (pf359).sound

def st38 : OrECtxStep where
  seq := sq353
  leftPremise := sq354
  rightPremise := sq361
  path := .right (.here)
  d₁ := f45
  d₂ := f122
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v78 : (sq353).semanticallyValid Hnet :=
  sound_orECtx st38 v77 v76

theorem v79 : (sq346).semanticallyValid Hnet := (pf351).sound

def st39 : OrECtxStep where
  seq := sq345
  leftPremise := sq346
  rightPremise := sq353
  path := .right (.here)
  d₁ := f44
  d₂ := f123
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v80 : (sq345).semanticallyValid Hnet :=
  sound_orECtx st39 v79 v78

theorem v81 : (sq338).semanticallyValid Hnet := (pf343).sound

def st40 : OrECtxStep where
  seq := sq337
  leftPremise := sq338
  rightPremise := sq345
  path := .right (.here)
  d₁ := f43
  d₂ := f124
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v82 : (sq337).semanticallyValid Hnet :=
  sound_orECtx st40 v81 v80

theorem v83 : (sq330).semanticallyValid Hnet := (pf335).sound

def st41 : OrECtxStep where
  seq := sq329
  leftPremise := sq330
  rightPremise := sq337
  path := .right (.here)
  d₁ := f42
  d₂ := f125
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v84 : (sq329).semanticallyValid Hnet :=
  sound_orECtx st41 v83 v82

theorem v85 : (sq322).semanticallyValid Hnet := (pf327).sound

def st42 : OrECtxStep where
  seq := sq321
  leftPremise := sq322
  rightPremise := sq329
  path := .right (.here)
  d₁ := f41
  d₂ := f126
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v86 : (sq321).semanticallyValid Hnet :=
  sound_orECtx st42 v85 v84

theorem v87 : (sq314).semanticallyValid Hnet := (pf319).sound

def st43 : OrECtxStep where
  seq := sq313
  leftPremise := sq314
  rightPremise := sq321
  path := .right (.here)
  d₁ := f40
  d₂ := f127
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v88 : (sq313).semanticallyValid Hnet :=
  sound_orECtx st43 v87 v86

theorem v89 : (sq306).semanticallyValid Hnet := (pf311).sound

def st44 : OrECtxStep where
  seq := sq305
  leftPremise := sq306
  rightPremise := sq313
  path := .right (.here)
  d₁ := f39
  d₂ := f128
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v90 : (sq305).semanticallyValid Hnet :=
  sound_orECtx st44 v89 v88

theorem v91 : (sq298).semanticallyValid Hnet := (pf303).sound

def st45 : OrECtxStep where
  seq := sq297
  leftPremise := sq298
  rightPremise := sq305
  path := .right (.here)
  d₁ := f38
  d₂ := f129
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v92 : (sq297).semanticallyValid Hnet :=
  sound_orECtx st45 v91 v90

theorem v93 : (sq290).semanticallyValid Hnet := (pf295).sound

def st46 : OrECtxStep where
  seq := sq289
  leftPremise := sq290
  rightPremise := sq297
  path := .right (.here)
  d₁ := f37
  d₂ := f130
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v94 : (sq289).semanticallyValid Hnet :=
  sound_orECtx st46 v93 v92

theorem v95 : (sq282).semanticallyValid Hnet := (pf287).sound

def st47 : OrECtxStep where
  seq := sq281
  leftPremise := sq282
  rightPremise := sq289
  path := .right (.here)
  d₁ := f36
  d₂ := f131
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v96 : (sq281).semanticallyValid Hnet :=
  sound_orECtx st47 v95 v94

theorem v97 : (sq274).semanticallyValid Hnet := (pf279).sound

def st48 : OrECtxStep where
  seq := sq273
  leftPremise := sq274
  rightPremise := sq281
  path := .right (.here)
  d₁ := f35
  d₂ := f132
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v98 : (sq273).semanticallyValid Hnet :=
  sound_orECtx st48 v97 v96

theorem v99 : (sq266).semanticallyValid Hnet := (pf271).sound

def st49 : OrECtxStep where
  seq := sq265
  leftPremise := sq266
  rightPremise := sq273
  path := .right (.here)
  d₁ := f34
  d₂ := f133
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v100 : (sq265).semanticallyValid Hnet :=
  sound_orECtx st49 v99 v98

theorem v101 : (sq258).semanticallyValid Hnet := (pf263).sound

def st50 : OrECtxStep where
  seq := sq257
  leftPremise := sq258
  rightPremise := sq265
  path := .right (.here)
  d₁ := f33
  d₂ := f134
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v102 : (sq257).semanticallyValid Hnet :=
  sound_orECtx st50 v101 v100

theorem v103 : (sq250).semanticallyValid Hnet := (pf255).sound

def st51 : OrECtxStep where
  seq := sq249
  leftPremise := sq250
  rightPremise := sq257
  path := .right (.here)
  d₁ := f32
  d₂ := f135
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v104 : (sq249).semanticallyValid Hnet :=
  sound_orECtx st51 v103 v102

theorem v105 : (sq242).semanticallyValid Hnet := (pf247).sound

def st52 : OrECtxStep where
  seq := sq241
  leftPremise := sq242
  rightPremise := sq249
  path := .right (.here)
  d₁ := f31
  d₂ := f136
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v106 : (sq241).semanticallyValid Hnet :=
  sound_orECtx st52 v105 v104

theorem v107 : (sq234).semanticallyValid Hnet := (pf239).sound

def st53 : OrECtxStep where
  seq := sq233
  leftPremise := sq234
  rightPremise := sq241
  path := .right (.here)
  d₁ := f30
  d₂ := f137
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v108 : (sq233).semanticallyValid Hnet :=
  sound_orECtx st53 v107 v106

theorem v109 : (sq226).semanticallyValid Hnet := (pf231).sound

def st54 : OrECtxStep where
  seq := sq225
  leftPremise := sq226
  rightPremise := sq233
  path := .right (.here)
  d₁ := f29
  d₂ := f138
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v110 : (sq225).semanticallyValid Hnet :=
  sound_orECtx st54 v109 v108

theorem v111 : (sq218).semanticallyValid Hnet := (pf223).sound

def st55 : OrECtxStep where
  seq := sq217
  leftPremise := sq218
  rightPremise := sq225
  path := .right (.here)
  d₁ := f28
  d₂ := f139
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v112 : (sq217).semanticallyValid Hnet :=
  sound_orECtx st55 v111 v110

theorem v113 : (sq210).semanticallyValid Hnet := (pf215).sound

def st56 : OrECtxStep where
  seq := sq209
  leftPremise := sq210
  rightPremise := sq217
  path := .right (.here)
  d₁ := f27
  d₂ := f140
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v114 : (sq209).semanticallyValid Hnet :=
  sound_orECtx st56 v113 v112

theorem v115 : (sq202).semanticallyValid Hnet := (pf207).sound

def st57 : OrECtxStep where
  seq := sq201
  leftPremise := sq202
  rightPremise := sq209
  path := .right (.here)
  d₁ := f26
  d₂ := f141
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v116 : (sq201).semanticallyValid Hnet :=
  sound_orECtx st57 v115 v114

theorem v117 : (sq194).semanticallyValid Hnet := (pf199).sound

def st58 : OrECtxStep where
  seq := sq193
  leftPremise := sq194
  rightPremise := sq201
  path := .right (.here)
  d₁ := f25
  d₂ := f142
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v118 : (sq193).semanticallyValid Hnet :=
  sound_orECtx st58 v117 v116

theorem v119 : (sq186).semanticallyValid Hnet := (pf191).sound

def st59 : OrECtxStep where
  seq := sq185
  leftPremise := sq186
  rightPremise := sq193
  path := .right (.here)
  d₁ := f24
  d₂ := f143
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v120 : (sq185).semanticallyValid Hnet :=
  sound_orECtx st59 v119 v118

theorem v121 : (sq178).semanticallyValid Hnet := (pf183).sound

def st60 : OrECtxStep where
  seq := sq177
  leftPremise := sq178
  rightPremise := sq185
  path := .right (.here)
  d₁ := f23
  d₂ := f144
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v122 : (sq177).semanticallyValid Hnet :=
  sound_orECtx st60 v121 v120

theorem v123 : (sq170).semanticallyValid Hnet := (pf175).sound

def st61 : OrECtxStep where
  seq := sq169
  leftPremise := sq170
  rightPremise := sq177
  path := .right (.here)
  d₁ := f22
  d₂ := f145
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v124 : (sq169).semanticallyValid Hnet :=
  sound_orECtx st61 v123 v122

theorem v125 : (sq162).semanticallyValid Hnet := (pf167).sound

def st62 : OrECtxStep where
  seq := sq161
  leftPremise := sq162
  rightPremise := sq169
  path := .right (.here)
  d₁ := f21
  d₂ := f146
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v126 : (sq161).semanticallyValid Hnet :=
  sound_orECtx st62 v125 v124

theorem v127 : (sq154).semanticallyValid Hnet := (pf159).sound

def st63 : OrECtxStep where
  seq := sq153
  leftPremise := sq154
  rightPremise := sq161
  path := .right (.here)
  d₁ := f20
  d₂ := f147
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v128 : (sq153).semanticallyValid Hnet :=
  sound_orECtx st63 v127 v126

theorem v129 : (sq146).semanticallyValid Hnet := (pf151).sound

def st64 : OrECtxStep where
  seq := sq145
  leftPremise := sq146
  rightPremise := sq153
  path := .right (.here)
  d₁ := f19
  d₂ := f148
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v130 : (sq145).semanticallyValid Hnet :=
  sound_orECtx st64 v129 v128

theorem v131 : (sq138).semanticallyValid Hnet := (pf143).sound

def st65 : OrECtxStep where
  seq := sq137
  leftPremise := sq138
  rightPremise := sq145
  path := .right (.here)
  d₁ := f18
  d₂ := f149
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v132 : (sq137).semanticallyValid Hnet :=
  sound_orECtx st65 v131 v130

theorem v133 : (sq130).semanticallyValid Hnet := (pf135).sound

def st66 : OrECtxStep where
  seq := sq129
  leftPremise := sq130
  rightPremise := sq137
  path := .right (.here)
  d₁ := f17
  d₂ := f150
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v134 : (sq129).semanticallyValid Hnet :=
  sound_orECtx st66 v133 v132

theorem v135 : (sq122).semanticallyValid Hnet := (pf127).sound

def st67 : OrECtxStep where
  seq := sq121
  leftPremise := sq122
  rightPremise := sq129
  path := .right (.here)
  d₁ := f16
  d₂ := f151
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v136 : (sq121).semanticallyValid Hnet :=
  sound_orECtx st67 v135 v134

theorem v137 : (sq114).semanticallyValid Hnet := (pf119).sound

def st68 : OrECtxStep where
  seq := sq113
  leftPremise := sq114
  rightPremise := sq121
  path := .right (.here)
  d₁ := f15
  d₂ := f152
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v138 : (sq113).semanticallyValid Hnet :=
  sound_orECtx st68 v137 v136

theorem v139 : (sq106).semanticallyValid Hnet := (pf111).sound

def st69 : OrECtxStep where
  seq := sq105
  leftPremise := sq106
  rightPremise := sq113
  path := .right (.here)
  d₁ := f14
  d₂ := f153
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v140 : (sq105).semanticallyValid Hnet :=
  sound_orECtx st69 v139 v138

theorem v141 : (sq98).semanticallyValid Hnet := (pf103).sound

def st70 : OrECtxStep where
  seq := sq97
  leftPremise := sq98
  rightPremise := sq105
  path := .right (.here)
  d₁ := f13
  d₂ := f154
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v142 : (sq97).semanticallyValid Hnet :=
  sound_orECtx st70 v141 v140

theorem v143 : (sq90).semanticallyValid Hnet := (pf95).sound

def st71 : OrECtxStep where
  seq := sq89
  leftPremise := sq90
  rightPremise := sq97
  path := .right (.here)
  d₁ := f12
  d₂ := f155
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v144 : (sq89).semanticallyValid Hnet :=
  sound_orECtx st71 v143 v142

theorem v145 : (sq82).semanticallyValid Hnet := (pf87).sound

def st72 : OrECtxStep where
  seq := sq81
  leftPremise := sq82
  rightPremise := sq89
  path := .right (.here)
  d₁ := f11
  d₂ := f156
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v146 : (sq81).semanticallyValid Hnet :=
  sound_orECtx st72 v145 v144

theorem v147 : (sq74).semanticallyValid Hnet := (pf79).sound

def st73 : OrECtxStep where
  seq := sq73
  leftPremise := sq74
  rightPremise := sq81
  path := .right (.here)
  d₁ := f10
  d₂ := f157
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v148 : (sq73).semanticallyValid Hnet :=
  sound_orECtx st73 v147 v146

theorem v149 : (sq66).semanticallyValid Hnet := (pf71).sound

def st74 : OrECtxStep where
  seq := sq65
  leftPremise := sq66
  rightPremise := sq73
  path := .right (.here)
  d₁ := f9
  d₂ := f158
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v150 : (sq65).semanticallyValid Hnet :=
  sound_orECtx st74 v149 v148

theorem v151 : (sq58).semanticallyValid Hnet := (pf63).sound

def st75 : OrECtxStep where
  seq := sq57
  leftPremise := sq58
  rightPremise := sq65
  path := .right (.here)
  d₁ := f8
  d₂ := f159
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v152 : (sq57).semanticallyValid Hnet :=
  sound_orECtx st75 v151 v150

theorem v153 : (sq50).semanticallyValid Hnet := (pf55).sound

def st76 : OrECtxStep where
  seq := sq49
  leftPremise := sq50
  rightPremise := sq57
  path := .right (.here)
  d₁ := f7
  d₂ := f160
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v154 : (sq49).semanticallyValid Hnet :=
  sound_orECtx st76 v153 v152

theorem v155 : (sq42).semanticallyValid Hnet := (pf47).sound

def st77 : OrECtxStep where
  seq := sq41
  leftPremise := sq42
  rightPremise := sq49
  path := .right (.here)
  d₁ := f6
  d₂ := f161
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v156 : (sq41).semanticallyValid Hnet :=
  sound_orECtx st77 v155 v154

theorem v157 : (sq34).semanticallyValid Hnet := (pf39).sound

def st78 : OrECtxStep where
  seq := sq33
  leftPremise := sq34
  rightPremise := sq41
  path := .right (.here)
  d₁ := f5
  d₂ := f162
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v158 : (sq33).semanticallyValid Hnet :=
  sound_orECtx st78 v157 v156

theorem v159 : (sq26).semanticallyValid Hnet := (pf31).sound

def st79 : OrECtxStep where
  seq := sq25
  leftPremise := sq26
  rightPremise := sq33
  path := .right (.here)
  d₁ := f4
  d₂ := f163
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v160 : (sq25).semanticallyValid Hnet :=
  sound_orECtx st79 v159 v158

theorem v161 : (sq18).semanticallyValid Hnet := (pf23).sound

def st80 : OrECtxStep where
  seq := sq17
  leftPremise := sq18
  rightPremise := sq25
  path := .right (.here)
  d₁ := f3
  d₂ := f164
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v162 : (sq17).semanticallyValid Hnet :=
  sound_orECtx st80 v161 v160

theorem v163 : (sq10).semanticallyValid Hnet := (pf15).sound

def st81 : OrECtxStep where
  seq := sq9
  leftPremise := sq10
  rightPremise := sq17
  path := .right (.here)
  d₁ := f2
  d₂ := f165
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v164 : (sq9).semanticallyValid Hnet :=
  sound_orECtx st81 v163 v162

theorem v165 : (sq2).semanticallyValid Hnet := (pf7).sound

def st82 : OrECtxStep where
  seq := sq1
  leftPremise := sq2
  rightPremise := sq9
  path := .right (.here)
  d₁ := f1
  d₂ := f166
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v166 : (sq1).semanticallyValid Hnet :=
  sound_orECtx st82 v165 v164

def pf672 : ProofObject Hnet sq676 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf673 : ProofObject Hnet sq675 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq676 pf672 f170 rfl rfl))

def pf674 : ProofObject Hnet sq676 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf675 : ProofObject Hnet sq678 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq676 pf674 f169 rfl rfl))

def pf676 : ProofObject Hnet sq677 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq678) (regionProof := pf675)
    (termX := (.var 0)) (simplex := sx84) (S := ex84)
    (degree := 5) (polynomial := tm322) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex84) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf677 : ProofObject Hnet sq674 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq675 pf673 sq677 pf676
    1 tm1 (.const 1) f738
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf678 : ProofObject Hnet sq679 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm324
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf679 : ProofObject Hnet sq673 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f736
    sq674 pf677 sq679 pf678
    rfl rfl rfl rfl))

def pf680 : ProofObject Hnet sq684 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf681 : ProofObject Hnet sq683 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq684 pf680 f171 rfl rfl))

def pf682 : ProofObject Hnet sq684 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf683 : ProofObject Hnet sq686 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq684 pf682 f169 rfl rfl))

def pf684 : ProofObject Hnet sq685 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq686) (regionProof := pf683)
    (termX := (.var 0)) (simplex := sx85) (S := ex85)
    (degree := 5) (polynomial := tm326) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex85) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf685 : ProofObject Hnet sq682 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq683 pf681 sq685 pf684
    1 tm1 (.const 1) f744
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf686 : ProofObject Hnet sq687 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm328
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf687 : ProofObject Hnet sq681 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f742
    sq682 pf685 sq687 pf686
    rfl rfl rfl rfl))

def pf688 : ProofObject Hnet sq692 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf689 : ProofObject Hnet sq691 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq692 pf688 f172 rfl rfl))

def pf690 : ProofObject Hnet sq692 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf691 : ProofObject Hnet sq694 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq692 pf690 f169 rfl rfl))

def pf692 : ProofObject Hnet sq693 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq694) (regionProof := pf691)
    (termX := (.var 0)) (simplex := sx86) (S := ex86)
    (degree := 5) (polynomial := tm330) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex86) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf693 : ProofObject Hnet sq690 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq691 pf689 sq693 pf692
    1 tm1 (.const 1) f750
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf694 : ProofObject Hnet sq695 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm332
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf695 : ProofObject Hnet sq689 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f748
    sq690 pf693 sq695 pf694
    rfl rfl rfl rfl))

def pf696 : ProofObject Hnet sq700 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf697 : ProofObject Hnet sq699 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq700 pf696 f173 rfl rfl))

def pf698 : ProofObject Hnet sq700 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf699 : ProofObject Hnet sq702 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq700 pf698 f169 rfl rfl))

def pf700 : ProofObject Hnet sq701 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq702) (regionProof := pf699)
    (termX := (.var 0)) (simplex := sx87) (S := ex87)
    (degree := 5) (polynomial := tm334) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex87) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf701 : ProofObject Hnet sq698 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq699 pf697 sq701 pf700
    1 tm1 (.const 1) f756
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf702 : ProofObject Hnet sq703 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm336
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf703 : ProofObject Hnet sq697 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f754
    sq698 pf701 sq703 pf702
    rfl rfl rfl rfl))

def pf704 : ProofObject Hnet sq708 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf705 : ProofObject Hnet sq707 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq708 pf704 f174 rfl rfl))

def pf706 : ProofObject Hnet sq708 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf707 : ProofObject Hnet sq710 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq708 pf706 f169 rfl rfl))

def pf708 : ProofObject Hnet sq709 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq710) (regionProof := pf707)
    (termX := (.var 0)) (simplex := sx88) (S := ex88)
    (degree := 5) (polynomial := tm338) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex88) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf709 : ProofObject Hnet sq706 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq707 pf705 sq709 pf708
    1 tm1 (.const 1) f762
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf710 : ProofObject Hnet sq711 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm340
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf711 : ProofObject Hnet sq705 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f760
    sq706 pf709 sq711 pf710
    rfl rfl rfl rfl))

def pf712 : ProofObject Hnet sq716 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf713 : ProofObject Hnet sq715 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq716 pf712 f175 rfl rfl))

def pf714 : ProofObject Hnet sq716 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf715 : ProofObject Hnet sq718 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq716 pf714 f169 rfl rfl))

def pf716 : ProofObject Hnet sq717 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq718) (regionProof := pf715)
    (termX := (.var 0)) (simplex := sx89) (S := ex89)
    (degree := 5) (polynomial := tm342) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex89) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf717 : ProofObject Hnet sq714 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq715 pf713 sq717 pf716
    1 tm1 (.const 1) f768
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf718 : ProofObject Hnet sq719 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm344
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf719 : ProofObject Hnet sq713 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f766
    sq714 pf717 sq719 pf718
    rfl rfl rfl rfl))

def pf720 : ProofObject Hnet sq724 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf721 : ProofObject Hnet sq723 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq724 pf720 f176 rfl rfl))

def pf722 : ProofObject Hnet sq724 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf723 : ProofObject Hnet sq726 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq724 pf722 f169 rfl rfl))

def pf724 : ProofObject Hnet sq725 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq726) (regionProof := pf723)
    (termX := (.var 0)) (simplex := sx90) (S := ex90)
    (degree := 5) (polynomial := tm346) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex90) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf725 : ProofObject Hnet sq722 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq723 pf721 sq725 pf724
    1 tm1 (.const 1) f774
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf726 : ProofObject Hnet sq727 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm348
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf727 : ProofObject Hnet sq721 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f772
    sq722 pf725 sq727 pf726
    rfl rfl rfl rfl))

def pf728 : ProofObject Hnet sq732 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf729 : ProofObject Hnet sq731 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq732 pf728 f177 rfl rfl))

def pf730 : ProofObject Hnet sq732 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf731 : ProofObject Hnet sq734 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq732 pf730 f169 rfl rfl))

def pf732 : ProofObject Hnet sq733 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq734) (regionProof := pf731)
    (termX := (.var 0)) (simplex := sx91) (S := ex91)
    (degree := 5) (polynomial := tm350) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex91) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf733 : ProofObject Hnet sq730 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq731 pf729 sq733 pf732
    1 tm1 (.const 1) f780
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf734 : ProofObject Hnet sq735 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm352
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf735 : ProofObject Hnet sq729 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f778
    sq730 pf733 sq735 pf734
    rfl rfl rfl rfl))

def pf736 : ProofObject Hnet sq740 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf737 : ProofObject Hnet sq739 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq740 pf736 f178 rfl rfl))

def pf738 : ProofObject Hnet sq740 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf739 : ProofObject Hnet sq742 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq740 pf738 f169 rfl rfl))

def pf740 : ProofObject Hnet sq741 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq742) (regionProof := pf739)
    (termX := (.var 0)) (simplex := sx92) (S := ex92)
    (degree := 5) (polynomial := tm354) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex92) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf741 : ProofObject Hnet sq738 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq739 pf737 sq741 pf740
    1 tm1 (.const 1) f786
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf742 : ProofObject Hnet sq743 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm356
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf743 : ProofObject Hnet sq737 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f784
    sq738 pf741 sq743 pf742
    rfl rfl rfl rfl))

def pf744 : ProofObject Hnet sq748 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf745 : ProofObject Hnet sq747 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq748 pf744 f179 rfl rfl))

def pf746 : ProofObject Hnet sq748 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf747 : ProofObject Hnet sq750 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq748 pf746 f169 rfl rfl))

def pf748 : ProofObject Hnet sq749 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq750) (regionProof := pf747)
    (termX := (.var 0)) (simplex := sx93) (S := ex93)
    (degree := 5) (polynomial := tm358) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex93) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf749 : ProofObject Hnet sq746 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq747 pf745 sq749 pf748
    1 tm1 (.const 1) f792
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf750 : ProofObject Hnet sq751 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm360
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf751 : ProofObject Hnet sq745 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f790
    sq746 pf749 sq751 pf750
    rfl rfl rfl rfl))

def pf752 : ProofObject Hnet sq756 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf753 : ProofObject Hnet sq755 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq756 pf752 f180 rfl rfl))

def pf754 : ProofObject Hnet sq756 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf755 : ProofObject Hnet sq758 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq756 pf754 f169 rfl rfl))

def pf756 : ProofObject Hnet sq757 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq758) (regionProof := pf755)
    (termX := (.var 0)) (simplex := sx94) (S := ex94)
    (degree := 5) (polynomial := tm362) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex94) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf757 : ProofObject Hnet sq754 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq755 pf753 sq757 pf756
    1 tm1 (.const 1) f798
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf758 : ProofObject Hnet sq759 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm364
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf759 : ProofObject Hnet sq753 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f796
    sq754 pf757 sq759 pf758
    rfl rfl rfl rfl))

def pf760 : ProofObject Hnet sq764 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf761 : ProofObject Hnet sq763 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq764 pf760 f181 rfl rfl))

def pf762 : ProofObject Hnet sq764 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf763 : ProofObject Hnet sq766 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq764 pf762 f169 rfl rfl))

def pf764 : ProofObject Hnet sq765 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq766) (regionProof := pf763)
    (termX := (.var 0)) (simplex := sx95) (S := ex95)
    (degree := 5) (polynomial := tm366) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex95) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf765 : ProofObject Hnet sq762 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq763 pf761 sq765 pf764
    1 tm1 (.const 1) f804
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf766 : ProofObject Hnet sq767 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm368
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf767 : ProofObject Hnet sq761 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f802
    sq762 pf765 sq767 pf766
    rfl rfl rfl rfl))

def pf768 : ProofObject Hnet sq772 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf769 : ProofObject Hnet sq771 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq772 pf768 f182 rfl rfl))

def pf770 : ProofObject Hnet sq772 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf771 : ProofObject Hnet sq774 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq772 pf770 f169 rfl rfl))

def pf772 : ProofObject Hnet sq773 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq774) (regionProof := pf771)
    (termX := (.var 0)) (simplex := sx96) (S := ex96)
    (degree := 5) (polynomial := tm370) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex96) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf773 : ProofObject Hnet sq770 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq771 pf769 sq773 pf772
    1 tm1 (.const 1) f810
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf774 : ProofObject Hnet sq775 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm372
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf775 : ProofObject Hnet sq769 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f808
    sq770 pf773 sq775 pf774
    rfl rfl rfl rfl))

def pf776 : ProofObject Hnet sq780 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf777 : ProofObject Hnet sq779 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq780 pf776 f183 rfl rfl))

def pf778 : ProofObject Hnet sq780 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf779 : ProofObject Hnet sq782 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq780 pf778 f169 rfl rfl))

def pf780 : ProofObject Hnet sq781 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq782) (regionProof := pf779)
    (termX := (.var 0)) (simplex := sx97) (S := ex97)
    (degree := 5) (polynomial := tm374) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex97) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf781 : ProofObject Hnet sq778 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq779 pf777 sq781 pf780
    1 tm1 (.const 1) f816
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf782 : ProofObject Hnet sq783 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm376
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf783 : ProofObject Hnet sq777 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f814
    sq778 pf781 sq783 pf782
    rfl rfl rfl rfl))

def pf784 : ProofObject Hnet sq788 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf785 : ProofObject Hnet sq787 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq788 pf784 f184 rfl rfl))

def pf786 : ProofObject Hnet sq788 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf787 : ProofObject Hnet sq790 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq788 pf786 f169 rfl rfl))

def pf788 : ProofObject Hnet sq789 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq790) (regionProof := pf787)
    (termX := (.var 0)) (simplex := sx98) (S := ex98)
    (degree := 8) (polynomial := tm378) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex98) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf789 : ProofObject Hnet sq786 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq787 pf785 sq789 pf788
    1 tm1 (.const 1) f822
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf790 : ProofObject Hnet sq791 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm380
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf791 : ProofObject Hnet sq785 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f820
    sq786 pf789 sq791 pf790
    rfl rfl rfl rfl))

def pf792 : ProofObject Hnet sq796 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf793 : ProofObject Hnet sq795 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq796 pf792 f185 rfl rfl))

def pf794 : ProofObject Hnet sq796 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf795 : ProofObject Hnet sq798 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq796 pf794 f169 rfl rfl))

def pf796 : ProofObject Hnet sq797 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq798) (regionProof := pf795)
    (termX := (.var 0)) (simplex := sx99) (S := ex99)
    (degree := 5) (polynomial := tm382) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex99) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf797 : ProofObject Hnet sq794 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq795 pf793 sq797 pf796
    1 tm1 (.const 1) f828
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf798 : ProofObject Hnet sq799 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm384
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf799 : ProofObject Hnet sq793 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f826
    sq794 pf797 sq799 pf798
    rfl rfl rfl rfl))

def pf800 : ProofObject Hnet sq804 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf801 : ProofObject Hnet sq803 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq804 pf800 f186 rfl rfl))

def pf802 : ProofObject Hnet sq804 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf803 : ProofObject Hnet sq806 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq804 pf802 f169 rfl rfl))

def pf804 : ProofObject Hnet sq805 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq806) (regionProof := pf803)
    (termX := (.var 0)) (simplex := sx100) (S := ex100)
    (degree := 5) (polynomial := tm386) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex100) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf805 : ProofObject Hnet sq802 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq803 pf801 sq805 pf804
    1 tm1 (.const 1) f834
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf806 : ProofObject Hnet sq807 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm388
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf807 : ProofObject Hnet sq801 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f832
    sq802 pf805 sq807 pf806
    rfl rfl rfl rfl))

def pf808 : ProofObject Hnet sq812 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf809 : ProofObject Hnet sq811 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq812 pf808 f187 rfl rfl))

def pf810 : ProofObject Hnet sq812 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf811 : ProofObject Hnet sq814 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq812 pf810 f169 rfl rfl))

def pf812 : ProofObject Hnet sq813 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq814) (regionProof := pf811)
    (termX := (.var 0)) (simplex := sx101) (S := ex101)
    (degree := 5) (polynomial := tm390) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex101) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf813 : ProofObject Hnet sq810 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq811 pf809 sq813 pf812
    1 tm1 (.const 1) f840
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf814 : ProofObject Hnet sq815 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm392
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf815 : ProofObject Hnet sq809 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f838
    sq810 pf813 sq815 pf814
    rfl rfl rfl rfl))

def pf816 : ProofObject Hnet sq820 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf817 : ProofObject Hnet sq819 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq820 pf816 f188 rfl rfl))

def pf818 : ProofObject Hnet sq820 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf819 : ProofObject Hnet sq822 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq820 pf818 f169 rfl rfl))

def pf820 : ProofObject Hnet sq821 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq822) (regionProof := pf819)
    (termX := (.var 0)) (simplex := sx102) (S := ex102)
    (degree := 5) (polynomial := tm394) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex102) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf821 : ProofObject Hnet sq818 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq819 pf817 sq821 pf820
    1 tm1 (.const 1) f846
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf822 : ProofObject Hnet sq823 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm396
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf823 : ProofObject Hnet sq817 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f844
    sq818 pf821 sq823 pf822
    rfl rfl rfl rfl))

def pf824 : ProofObject Hnet sq828 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf825 : ProofObject Hnet sq827 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq828 pf824 f189 rfl rfl))

def pf826 : ProofObject Hnet sq828 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf827 : ProofObject Hnet sq830 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq828 pf826 f169 rfl rfl))

def pf828 : ProofObject Hnet sq829 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq830) (regionProof := pf827)
    (termX := (.var 0)) (simplex := sx103) (S := ex103)
    (degree := 5) (polynomial := tm398) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex103) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf829 : ProofObject Hnet sq826 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq827 pf825 sq829 pf828
    1 tm1 (.const 1) f852
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf830 : ProofObject Hnet sq831 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm400
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf831 : ProofObject Hnet sq825 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f850
    sq826 pf829 sq831 pf830
    rfl rfl rfl rfl))

def pf832 : ProofObject Hnet sq836 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf833 : ProofObject Hnet sq835 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq836 pf832 f190 rfl rfl))

def pf834 : ProofObject Hnet sq836 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf835 : ProofObject Hnet sq838 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq836 pf834 f169 rfl rfl))

def pf836 : ProofObject Hnet sq837 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq838) (regionProof := pf835)
    (termX := (.var 0)) (simplex := sx104) (S := ex104)
    (degree := 5) (polynomial := tm402) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex104) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf837 : ProofObject Hnet sq834 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq835 pf833 sq837 pf836
    1 tm1 (.const 1) f858
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf838 : ProofObject Hnet sq839 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm404
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf839 : ProofObject Hnet sq833 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f856
    sq834 pf837 sq839 pf838
    rfl rfl rfl rfl))

def pf840 : ProofObject Hnet sq844 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf841 : ProofObject Hnet sq843 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq844 pf840 f191 rfl rfl))

def pf842 : ProofObject Hnet sq844 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf843 : ProofObject Hnet sq846 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq844 pf842 f169 rfl rfl))

def pf844 : ProofObject Hnet sq845 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq846) (regionProof := pf843)
    (termX := (.var 0)) (simplex := sx105) (S := ex105)
    (degree := 8) (polynomial := tm406) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex105) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf845 : ProofObject Hnet sq842 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq843 pf841 sq845 pf844
    1 tm1 (.const 1) f864
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf846 : ProofObject Hnet sq847 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm408
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf847 : ProofObject Hnet sq841 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f862
    sq842 pf845 sq847 pf846
    rfl rfl rfl rfl))

def pf848 : ProofObject Hnet sq852 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf849 : ProofObject Hnet sq851 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq852 pf848 f192 rfl rfl))

def pf850 : ProofObject Hnet sq852 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf851 : ProofObject Hnet sq854 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq852 pf850 f169 rfl rfl))

def pf852 : ProofObject Hnet sq853 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq854) (regionProof := pf851)
    (termX := (.var 0)) (simplex := sx106) (S := ex106)
    (degree := 5) (polynomial := tm410) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex106) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf853 : ProofObject Hnet sq850 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq851 pf849 sq853 pf852
    1 tm1 (.const 1) f870
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf854 : ProofObject Hnet sq855 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm412
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf855 : ProofObject Hnet sq849 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f868
    sq850 pf853 sq855 pf854
    rfl rfl rfl rfl))

def pf856 : ProofObject Hnet sq860 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf857 : ProofObject Hnet sq859 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq860 pf856 f193 rfl rfl))

def pf858 : ProofObject Hnet sq860 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf859 : ProofObject Hnet sq862 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq860 pf858 f169 rfl rfl))

def pf860 : ProofObject Hnet sq861 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq862) (regionProof := pf859)
    (termX := (.var 0)) (simplex := sx107) (S := ex107)
    (degree := 5) (polynomial := tm414) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex107) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf861 : ProofObject Hnet sq858 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq859 pf857 sq861 pf860
    1 tm1 (.const 1) f876
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf862 : ProofObject Hnet sq863 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm416
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf863 : ProofObject Hnet sq857 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f874
    sq858 pf861 sq863 pf862
    rfl rfl rfl rfl))

def pf864 : ProofObject Hnet sq868 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf865 : ProofObject Hnet sq867 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq868 pf864 f194 rfl rfl))

def pf866 : ProofObject Hnet sq868 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf867 : ProofObject Hnet sq870 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq868 pf866 f169 rfl rfl))

def pf868 : ProofObject Hnet sq869 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq870) (regionProof := pf867)
    (termX := (.var 0)) (simplex := sx108) (S := ex108)
    (degree := 5) (polynomial := tm418) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex108) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf869 : ProofObject Hnet sq866 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq867 pf865 sq869 pf868
    1 tm1 (.const 1) f882
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf870 : ProofObject Hnet sq871 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm420
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf871 : ProofObject Hnet sq865 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f880
    sq866 pf869 sq871 pf870
    rfl rfl rfl rfl))

def pf872 : ProofObject Hnet sq876 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf873 : ProofObject Hnet sq875 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq876 pf872 f195 rfl rfl))

def pf874 : ProofObject Hnet sq876 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf875 : ProofObject Hnet sq878 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq876 pf874 f169 rfl rfl))

def pf876 : ProofObject Hnet sq877 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq878) (regionProof := pf875)
    (termX := (.var 0)) (simplex := sx109) (S := ex109)
    (degree := 5) (polynomial := tm422) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex109) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf877 : ProofObject Hnet sq874 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq875 pf873 sq877 pf876
    1 tm1 (.const 1) f888
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf878 : ProofObject Hnet sq879 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm424
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf879 : ProofObject Hnet sq873 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f886
    sq874 pf877 sq879 pf878
    rfl rfl rfl rfl))

def pf880 : ProofObject Hnet sq884 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf881 : ProofObject Hnet sq883 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq884 pf880 f196 rfl rfl))

def pf882 : ProofObject Hnet sq884 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf883 : ProofObject Hnet sq886 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq884 pf882 f169 rfl rfl))

def pf884 : ProofObject Hnet sq885 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq886) (regionProof := pf883)
    (termX := (.var 0)) (simplex := sx110) (S := ex110)
    (degree := 5) (polynomial := tm426) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex110) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf885 : ProofObject Hnet sq882 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq883 pf881 sq885 pf884
    1 tm1 (.const 1) f894
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf886 : ProofObject Hnet sq887 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm428
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf887 : ProofObject Hnet sq881 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f892
    sq882 pf885 sq887 pf886
    rfl rfl rfl rfl))

def pf888 : ProofObject Hnet sq892 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf889 : ProofObject Hnet sq891 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq892 pf888 f197 rfl rfl))

def pf890 : ProofObject Hnet sq892 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf891 : ProofObject Hnet sq894 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq892 pf890 f169 rfl rfl))

def pf892 : ProofObject Hnet sq893 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq894) (regionProof := pf891)
    (termX := (.var 0)) (simplex := sx111) (S := ex111)
    (degree := 5) (polynomial := tm430) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex111) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf893 : ProofObject Hnet sq890 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq891 pf889 sq893 pf892
    1 tm1 (.const 1) f900
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf894 : ProofObject Hnet sq895 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm432
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf895 : ProofObject Hnet sq889 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f898
    sq890 pf893 sq895 pf894
    rfl rfl rfl rfl))

def pf896 : ProofObject Hnet sq900 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf897 : ProofObject Hnet sq899 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq900 pf896 f198 rfl rfl))

def pf898 : ProofObject Hnet sq900 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf899 : ProofObject Hnet sq902 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq900 pf898 f169 rfl rfl))

def pf900 : ProofObject Hnet sq901 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq902) (regionProof := pf899)
    (termX := (.var 0)) (simplex := sx112) (S := ex112)
    (degree := 5) (polynomial := tm434) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex112) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf901 : ProofObject Hnet sq898 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq899 pf897 sq901 pf900
    1 tm1 (.const 1) f906
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf902 : ProofObject Hnet sq903 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm436
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf903 : ProofObject Hnet sq897 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f904
    sq898 pf901 sq903 pf902
    rfl rfl rfl rfl))

def pf904 : ProofObject Hnet sq908 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf905 : ProofObject Hnet sq907 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq908 pf904 f199 rfl rfl))

def pf906 : ProofObject Hnet sq908 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf907 : ProofObject Hnet sq910 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq908 pf906 f169 rfl rfl))

def pf908 : ProofObject Hnet sq909 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq910) (regionProof := pf907)
    (termX := (.var 0)) (simplex := sx113) (S := ex113)
    (degree := 5) (polynomial := tm438) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex113) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf909 : ProofObject Hnet sq906 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq907 pf905 sq909 pf908
    1 tm1 (.const 1) f912
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf910 : ProofObject Hnet sq911 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm440
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf911 : ProofObject Hnet sq905 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f910
    sq906 pf909 sq911 pf910
    rfl rfl rfl rfl))

def pf912 : ProofObject Hnet sq916 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf913 : ProofObject Hnet sq915 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq916 pf912 f200 rfl rfl))

def pf914 : ProofObject Hnet sq916 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf915 : ProofObject Hnet sq918 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq916 pf914 f169 rfl rfl))

def pf916 : ProofObject Hnet sq917 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq918) (regionProof := pf915)
    (termX := (.var 0)) (simplex := sx114) (S := ex114)
    (degree := 5) (polynomial := tm442) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex114) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf917 : ProofObject Hnet sq914 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq915 pf913 sq917 pf916
    1 tm1 (.const 1) f918
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf918 : ProofObject Hnet sq919 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm444
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf919 : ProofObject Hnet sq913 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f916
    sq914 pf917 sq919 pf918
    rfl rfl rfl rfl))

def pf920 : ProofObject Hnet sq924 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf921 : ProofObject Hnet sq923 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq924 pf920 f201 rfl rfl))

def pf922 : ProofObject Hnet sq924 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf923 : ProofObject Hnet sq926 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq924 pf922 f169 rfl rfl))

def pf924 : ProofObject Hnet sq925 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq926) (regionProof := pf923)
    (termX := (.var 0)) (simplex := sx115) (S := ex115)
    (degree := 5) (polynomial := tm446) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex115) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf925 : ProofObject Hnet sq922 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq923 pf921 sq925 pf924
    1 tm1 (.const 1) f924
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf926 : ProofObject Hnet sq927 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm448
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf927 : ProofObject Hnet sq921 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f922
    sq922 pf925 sq927 pf926
    rfl rfl rfl rfl))

def pf928 : ProofObject Hnet sq932 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf929 : ProofObject Hnet sq931 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq932 pf928 f202 rfl rfl))

def pf930 : ProofObject Hnet sq932 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf931 : ProofObject Hnet sq934 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq932 pf930 f169 rfl rfl))

def pf932 : ProofObject Hnet sq933 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq934) (regionProof := pf931)
    (termX := (.var 0)) (simplex := sx116) (S := ex116)
    (degree := 5) (polynomial := tm450) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex116) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf933 : ProofObject Hnet sq930 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq931 pf929 sq933 pf932
    1 tm1 (.const 1) f930
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf934 : ProofObject Hnet sq935 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm452
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf935 : ProofObject Hnet sq929 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f928
    sq930 pf933 sq935 pf934
    rfl rfl rfl rfl))

def pf936 : ProofObject Hnet sq940 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf937 : ProofObject Hnet sq939 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq940 pf936 f203 rfl rfl))

def pf938 : ProofObject Hnet sq940 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf939 : ProofObject Hnet sq942 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq940 pf938 f169 rfl rfl))

def pf940 : ProofObject Hnet sq941 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq942) (regionProof := pf939)
    (termX := (.var 0)) (simplex := sx117) (S := ex117)
    (degree := 5) (polynomial := tm454) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex117) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf941 : ProofObject Hnet sq938 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq939 pf937 sq941 pf940
    1 tm1 (.const 1) f936
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf942 : ProofObject Hnet sq943 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm456
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf943 : ProofObject Hnet sq937 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f934
    sq938 pf941 sq943 pf942
    rfl rfl rfl rfl))

def pf944 : ProofObject Hnet sq948 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf945 : ProofObject Hnet sq947 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq948 pf944 f204 rfl rfl))

def pf946 : ProofObject Hnet sq948 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf947 : ProofObject Hnet sq950 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq948 pf946 f169 rfl rfl))

def pf948 : ProofObject Hnet sq949 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq950) (regionProof := pf947)
    (termX := (.var 0)) (simplex := sx118) (S := ex118)
    (degree := 5) (polynomial := tm458) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex118) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf949 : ProofObject Hnet sq946 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq947 pf945 sq949 pf948
    1 tm1 (.const 1) f942
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf950 : ProofObject Hnet sq951 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm460
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf951 : ProofObject Hnet sq945 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f940
    sq946 pf949 sq951 pf950
    rfl rfl rfl rfl))

def pf952 : ProofObject Hnet sq955 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf953 : ProofObject Hnet sq954 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq955 pf952 f205 rfl rfl))

def pf954 : ProofObject Hnet sq955 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf955 : ProofObject Hnet sq957 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq955 pf954 f169 rfl rfl))

def pf956 : ProofObject Hnet sq956 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq957) (regionProof := pf955)
    (termX := (.var 0)) (simplex := sx119) (S := ex119)
    (degree := 5) (polynomial := tm462) (predicate := f249)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex119) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf957 : ProofObject Hnet sq953 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq954 pf953 sq956 pf956
    1 tm1 (.const 1) f947
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf958 : ProofObject Hnet sq958 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm464
    tm320
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf959 : ProofObject Hnet sq952 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f945
    sq953 pf957 sq958 pf958
    rfl rfl rfl rfl))

theorem v167 : (sq945).semanticallyValid Hnet := (pf951).sound

theorem v168 : (sq952).semanticallyValid Hnet := (pf959).sound

def st83 : OrECtxStep where
  seq := sq944
  leftPremise := sq945
  rightPremise := sq952
  path := .right (.here)
  d₁ := f204
  d₂ := f205
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v169 : (sq944).semanticallyValid Hnet :=
  sound_orECtx st83 v167 v168

theorem v170 : (sq937).semanticallyValid Hnet := (pf943).sound

def st84 : OrECtxStep where
  seq := sq936
  leftPremise := sq937
  rightPremise := sq944
  path := .right (.here)
  d₁ := f203
  d₂ := f206
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v171 : (sq936).semanticallyValid Hnet :=
  sound_orECtx st84 v170 v169

theorem v172 : (sq929).semanticallyValid Hnet := (pf935).sound

def st85 : OrECtxStep where
  seq := sq928
  leftPremise := sq929
  rightPremise := sq936
  path := .right (.here)
  d₁ := f202
  d₂ := f207
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v173 : (sq928).semanticallyValid Hnet :=
  sound_orECtx st85 v172 v171

theorem v174 : (sq921).semanticallyValid Hnet := (pf927).sound

def st86 : OrECtxStep where
  seq := sq920
  leftPremise := sq921
  rightPremise := sq928
  path := .right (.here)
  d₁ := f201
  d₂ := f208
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v175 : (sq920).semanticallyValid Hnet :=
  sound_orECtx st86 v174 v173

theorem v176 : (sq913).semanticallyValid Hnet := (pf919).sound

def st87 : OrECtxStep where
  seq := sq912
  leftPremise := sq913
  rightPremise := sq920
  path := .right (.here)
  d₁ := f200
  d₂ := f209
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v177 : (sq912).semanticallyValid Hnet :=
  sound_orECtx st87 v176 v175

theorem v178 : (sq905).semanticallyValid Hnet := (pf911).sound

def st88 : OrECtxStep where
  seq := sq904
  leftPremise := sq905
  rightPremise := sq912
  path := .right (.here)
  d₁ := f199
  d₂ := f210
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v179 : (sq904).semanticallyValid Hnet :=
  sound_orECtx st88 v178 v177

theorem v180 : (sq897).semanticallyValid Hnet := (pf903).sound

def st89 : OrECtxStep where
  seq := sq896
  leftPremise := sq897
  rightPremise := sq904
  path := .right (.here)
  d₁ := f198
  d₂ := f211
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v181 : (sq896).semanticallyValid Hnet :=
  sound_orECtx st89 v180 v179

theorem v182 : (sq889).semanticallyValid Hnet := (pf895).sound

def st90 : OrECtxStep where
  seq := sq888
  leftPremise := sq889
  rightPremise := sq896
  path := .right (.here)
  d₁ := f197
  d₂ := f212
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v183 : (sq888).semanticallyValid Hnet :=
  sound_orECtx st90 v182 v181

theorem v184 : (sq881).semanticallyValid Hnet := (pf887).sound

def st91 : OrECtxStep where
  seq := sq880
  leftPremise := sq881
  rightPremise := sq888
  path := .right (.here)
  d₁ := f196
  d₂ := f213
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v185 : (sq880).semanticallyValid Hnet :=
  sound_orECtx st91 v184 v183

theorem v186 : (sq873).semanticallyValid Hnet := (pf879).sound

def st92 : OrECtxStep where
  seq := sq872
  leftPremise := sq873
  rightPremise := sq880
  path := .right (.here)
  d₁ := f195
  d₂ := f214
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v187 : (sq872).semanticallyValid Hnet :=
  sound_orECtx st92 v186 v185

theorem v188 : (sq865).semanticallyValid Hnet := (pf871).sound

def st93 : OrECtxStep where
  seq := sq864
  leftPremise := sq865
  rightPremise := sq872
  path := .right (.here)
  d₁ := f194
  d₂ := f215
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v189 : (sq864).semanticallyValid Hnet :=
  sound_orECtx st93 v188 v187

theorem v190 : (sq857).semanticallyValid Hnet := (pf863).sound

def st94 : OrECtxStep where
  seq := sq856
  leftPremise := sq857
  rightPremise := sq864
  path := .right (.here)
  d₁ := f193
  d₂ := f216
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v191 : (sq856).semanticallyValid Hnet :=
  sound_orECtx st94 v190 v189

theorem v192 : (sq849).semanticallyValid Hnet := (pf855).sound

def st95 : OrECtxStep where
  seq := sq848
  leftPremise := sq849
  rightPremise := sq856
  path := .right (.here)
  d₁ := f192
  d₂ := f217
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v193 : (sq848).semanticallyValid Hnet :=
  sound_orECtx st95 v192 v191

theorem v194 : (sq841).semanticallyValid Hnet := (pf847).sound

def st96 : OrECtxStep where
  seq := sq840
  leftPremise := sq841
  rightPremise := sq848
  path := .right (.here)
  d₁ := f191
  d₂ := f218
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v195 : (sq840).semanticallyValid Hnet :=
  sound_orECtx st96 v194 v193

theorem v196 : (sq833).semanticallyValid Hnet := (pf839).sound

def st97 : OrECtxStep where
  seq := sq832
  leftPremise := sq833
  rightPremise := sq840
  path := .right (.here)
  d₁ := f190
  d₂ := f219
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v197 : (sq832).semanticallyValid Hnet :=
  sound_orECtx st97 v196 v195

theorem v198 : (sq825).semanticallyValid Hnet := (pf831).sound

def st98 : OrECtxStep where
  seq := sq824
  leftPremise := sq825
  rightPremise := sq832
  path := .right (.here)
  d₁ := f189
  d₂ := f220
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v199 : (sq824).semanticallyValid Hnet :=
  sound_orECtx st98 v198 v197

theorem v200 : (sq817).semanticallyValid Hnet := (pf823).sound

def st99 : OrECtxStep where
  seq := sq816
  leftPremise := sq817
  rightPremise := sq824
  path := .right (.here)
  d₁ := f188
  d₂ := f221
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v201 : (sq816).semanticallyValid Hnet :=
  sound_orECtx st99 v200 v199

theorem v202 : (sq809).semanticallyValid Hnet := (pf815).sound

def st100 : OrECtxStep where
  seq := sq808
  leftPremise := sq809
  rightPremise := sq816
  path := .right (.here)
  d₁ := f187
  d₂ := f222
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v203 : (sq808).semanticallyValid Hnet :=
  sound_orECtx st100 v202 v201

theorem v204 : (sq801).semanticallyValid Hnet := (pf807).sound

def st101 : OrECtxStep where
  seq := sq800
  leftPremise := sq801
  rightPremise := sq808
  path := .right (.here)
  d₁ := f186
  d₂ := f223
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v205 : (sq800).semanticallyValid Hnet :=
  sound_orECtx st101 v204 v203

theorem v206 : (sq793).semanticallyValid Hnet := (pf799).sound

def st102 : OrECtxStep where
  seq := sq792
  leftPremise := sq793
  rightPremise := sq800
  path := .right (.here)
  d₁ := f185
  d₂ := f224
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v207 : (sq792).semanticallyValid Hnet :=
  sound_orECtx st102 v206 v205

theorem v208 : (sq785).semanticallyValid Hnet := (pf791).sound

def st103 : OrECtxStep where
  seq := sq784
  leftPremise := sq785
  rightPremise := sq792
  path := .right (.here)
  d₁ := f184
  d₂ := f225
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v209 : (sq784).semanticallyValid Hnet :=
  sound_orECtx st103 v208 v207

theorem v210 : (sq777).semanticallyValid Hnet := (pf783).sound

def st104 : OrECtxStep where
  seq := sq776
  leftPremise := sq777
  rightPremise := sq784
  path := .right (.here)
  d₁ := f183
  d₂ := f226
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v211 : (sq776).semanticallyValid Hnet :=
  sound_orECtx st104 v210 v209

theorem v212 : (sq769).semanticallyValid Hnet := (pf775).sound

def st105 : OrECtxStep where
  seq := sq768
  leftPremise := sq769
  rightPremise := sq776
  path := .right (.here)
  d₁ := f182
  d₂ := f227
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v213 : (sq768).semanticallyValid Hnet :=
  sound_orECtx st105 v212 v211

theorem v214 : (sq761).semanticallyValid Hnet := (pf767).sound

def st106 : OrECtxStep where
  seq := sq760
  leftPremise := sq761
  rightPremise := sq768
  path := .right (.here)
  d₁ := f181
  d₂ := f228
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v215 : (sq760).semanticallyValid Hnet :=
  sound_orECtx st106 v214 v213

theorem v216 : (sq753).semanticallyValid Hnet := (pf759).sound

def st107 : OrECtxStep where
  seq := sq752
  leftPremise := sq753
  rightPremise := sq760
  path := .right (.here)
  d₁ := f180
  d₂ := f229
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v217 : (sq752).semanticallyValid Hnet :=
  sound_orECtx st107 v216 v215

theorem v218 : (sq745).semanticallyValid Hnet := (pf751).sound

def st108 : OrECtxStep where
  seq := sq744
  leftPremise := sq745
  rightPremise := sq752
  path := .right (.here)
  d₁ := f179
  d₂ := f230
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v219 : (sq744).semanticallyValid Hnet :=
  sound_orECtx st108 v218 v217

theorem v220 : (sq737).semanticallyValid Hnet := (pf743).sound

def st109 : OrECtxStep where
  seq := sq736
  leftPremise := sq737
  rightPremise := sq744
  path := .right (.here)
  d₁ := f178
  d₂ := f231
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v221 : (sq736).semanticallyValid Hnet :=
  sound_orECtx st109 v220 v219

theorem v222 : (sq729).semanticallyValid Hnet := (pf735).sound

def st110 : OrECtxStep where
  seq := sq728
  leftPremise := sq729
  rightPremise := sq736
  path := .right (.here)
  d₁ := f177
  d₂ := f232
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v223 : (sq728).semanticallyValid Hnet :=
  sound_orECtx st110 v222 v221

theorem v224 : (sq721).semanticallyValid Hnet := (pf727).sound

def st111 : OrECtxStep where
  seq := sq720
  leftPremise := sq721
  rightPremise := sq728
  path := .right (.here)
  d₁ := f176
  d₂ := f233
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v225 : (sq720).semanticallyValid Hnet :=
  sound_orECtx st111 v224 v223

theorem v226 : (sq713).semanticallyValid Hnet := (pf719).sound

def st112 : OrECtxStep where
  seq := sq712
  leftPremise := sq713
  rightPremise := sq720
  path := .right (.here)
  d₁ := f175
  d₂ := f234
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v227 : (sq712).semanticallyValid Hnet :=
  sound_orECtx st112 v226 v225

theorem v228 : (sq705).semanticallyValid Hnet := (pf711).sound

def st113 : OrECtxStep where
  seq := sq704
  leftPremise := sq705
  rightPremise := sq712
  path := .right (.here)
  d₁ := f174
  d₂ := f235
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v229 : (sq704).semanticallyValid Hnet :=
  sound_orECtx st113 v228 v227

theorem v230 : (sq697).semanticallyValid Hnet := (pf703).sound

def st114 : OrECtxStep where
  seq := sq696
  leftPremise := sq697
  rightPremise := sq704
  path := .right (.here)
  d₁ := f173
  d₂ := f236
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v231 : (sq696).semanticallyValid Hnet :=
  sound_orECtx st114 v230 v229

theorem v232 : (sq689).semanticallyValid Hnet := (pf695).sound

def st115 : OrECtxStep where
  seq := sq688
  leftPremise := sq689
  rightPremise := sq696
  path := .right (.here)
  d₁ := f172
  d₂ := f237
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v233 : (sq688).semanticallyValid Hnet :=
  sound_orECtx st115 v232 v231

theorem v234 : (sq681).semanticallyValid Hnet := (pf687).sound

def st116 : OrECtxStep where
  seq := sq680
  leftPremise := sq681
  rightPremise := sq688
  path := .right (.here)
  d₁ := f171
  d₂ := f238
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v235 : (sq680).semanticallyValid Hnet :=
  sound_orECtx st116 v234 v233

theorem v236 : (sq673).semanticallyValid Hnet := (pf679).sound

def st117 : OrECtxStep where
  seq := sq672
  leftPremise := sq673
  rightPremise := sq680
  path := .right (.here)
  d₁ := f170
  d₂ := f239
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v237 : (sq672).semanticallyValid Hnet :=
  sound_orECtx st117 v236 v235

def pf960 : ProofObject Hnet sq959 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    (.const 0)
    (.const 0)
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

theorem v238 : (sq959).semanticallyValid Hnet := (pf960).sound

def pf961 : ProofObject Hnet sq959 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    (.const 0)
    (.const 0)
    92
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

theorem v239 : (sq959).semanticallyValid Hnet := (pf961).sound

def st118 : SyzygyStep Hnet where
  seq := sq0
  components := [sq1, sq672, sq959, sq959]
  combination := tm465
  conclusion := tm2
  preContains := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals unfold premiseContains
    all_goals decide +kernel
  conclShape := ⟨[], by decide +kernel⟩
  conclFin := by decide +kernel
  wiresPos := by decide +kernel
  compPostWiresPos := by decide +kernel
  valid := by decide +kernel
  postForm := Or.inl rfl

theorem v240 : (sq0).semanticallyValid Hnet :=
  sound_syzygy st118 (by

    have hlit : ∀ c ∈ [sq1, sq672, sq959, sq959], c.semanticallyValid Hnet := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact v166
      · exact v237
      · exact v238
      · exact v239
    exact hlit)

theorem DpCompositeSmallGain_valid : (sq0).semanticallyValid Hnet := v240

#print axioms DpCompositeSmallGain_valid

end PPLC.Handshake.DpCompositeSmallGain
