import Qtsl.Soundness
import Qtsl.Decide
import Qtsl.Admissible

/-!
# Cart–pole core-decrease certificate (generated)

Generated from certificate bytes by the untrusted export tool — a wrong
translation is refused by Lean, never silently accepted. Do not edit by
hand. Interned pools and `ProofObject` definitions for the primitive
subtrees; side conditions by `decide +kernel`; the endpoint is the
`_valid` theorem and its axiom closure.
-/

namespace PPLC.Handshake.CartpoleCoreDecrease

open PPLC

set_option maxRecDepth 4096

set_option maxHeartbeats 40000000

def cx0coords : List (List Rat) :=
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-578037/960310), (215941/277950), (464329/172299)],
   [(-397227/657548), (215941/277950), (2080453/808878)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-578037/960310), (215941/277950), (464329/172299)],
   [(-578037/960310), (446971/498550), (464329/172299)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-251352/519859), (215941/277950), (1386004/677643)],
   [(-397227/657548), (215941/277950), (2080453/808878)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-251352/519859), (215941/277950), (1386004/677643)],
   [(-251352/519859), (446971/498550), (1386004/677643)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-292703/608120), (446971/498550), (161807/74627)],
   [(-578037/960310), (446971/498550), (464329/172299)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(-292703/608120), (215941/277950), (161807/74627)],
   [(-292703/608120), (446971/498550), (161807/74627)],
   [(-251352/519859), (446971/498550), (1386004/677643)],
   [(-397227/657548), (446971/498550), (2080453/808878)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(40358/982645), (52037/53150), (227193/816596)],
   [(-8957/206550), (52037/53150), (388600/602447)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(40358/982645), (52037/53150), (227193/816596)],
   [(40358/982645), 1, (227193/816596)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(-37887/878395), (52037/53150), (44917/81464)],
   [(-8957/206550), (52037/53150), (388600/602447)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(-37887/878395), (52037/53150), (44917/81464)],
   [(-37887/878395), 1, (44917/81464)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(18970/459283), 1, (167417/907134)],
   [(40358/982645), 1, (227193/816596)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(18970/459283), (52037/53150), (167417/907134)],
   [(18970/459283), 1, (167417/907134)],
   [(-37887/878395), 1, (44917/81464)],
   [(-8957/206550), 1, (388600/602447)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(131547/921332), (107667/111025), (-26501/140000)],
   [(22047/361955), (107667/111025), (26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(131547/921332), (107667/111025), (-26501/140000)],
   [(131547/921332), 1, (-26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(28343/704232), (107667/111025), (26501/140000)],
   [(22047/361955), (107667/111025), (26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(28343/704232), (107667/111025), (26501/140000)],
   [(28343/704232), 1, (26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(110478/904705), 1, (-26501/140000)],
   [(131547/921332), 1, (-26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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
  [[(110478/904705), (107667/111025), (-26501/140000)],
   [(110478/904705), 1, (-26501/140000)],
   [(28343/704232), 1, (26501/140000)],
   [(22047/361955), 1, (26501/140000)]]

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

def Hnet : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[3], Dtype.Q⟩ else if w = 1 then some ⟨[1], Dtype.Q⟩ else none
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

def sx6 : Simplex :=
  ⟨cx6, fun _ => true, by decide +kernel⟩

def ex6 : ExtensionSet :=
  ⟨sx6, fun _ => false, by decide +kernel, by decide +kernel⟩

def f7 : Formula :=
  .inRegion (.var 0) sx6 ex6

def sx7 : Simplex :=
  ⟨cx7, fun _ => true, by decide +kernel⟩

def ex7 : ExtensionSet :=
  ⟨sx7, fun _ => false, by decide +kernel, by decide +kernel⟩

def f8 : Formula :=
  .inRegion (.var 0) sx7 ex7

def sx8 : Simplex :=
  ⟨cx8, fun _ => true, by decide +kernel⟩

def ex8 : ExtensionSet :=
  ⟨sx8, fun _ => false, by decide +kernel, by decide +kernel⟩

def f9 : Formula :=
  .inRegion (.var 0) sx8 ex8

def sx9 : Simplex :=
  ⟨cx9, fun _ => true, by decide +kernel⟩

def ex9 : ExtensionSet :=
  ⟨sx9, fun _ => false, by decide +kernel, by decide +kernel⟩

def f10 : Formula :=
  .inRegion (.var 0) sx9 ex9

def sx10 : Simplex :=
  ⟨cx10, fun _ => true, by decide +kernel⟩

def ex10 : ExtensionSet :=
  ⟨sx10, fun _ => false, by decide +kernel, by decide +kernel⟩

def f11 : Formula :=
  .inRegion (.var 0) sx10 ex10

def sx11 : Simplex :=
  ⟨cx11, fun _ => true, by decide +kernel⟩

def ex11 : ExtensionSet :=
  ⟨sx11, fun _ => false, by decide +kernel, by decide +kernel⟩

def f12 : Formula :=
  .inRegion (.var 0) sx11 ex11

def sx12 : Simplex :=
  ⟨cx12, fun _ => true, by decide +kernel⟩

def ex12 : ExtensionSet :=
  ⟨sx12, fun _ => false, by decide +kernel, by decide +kernel⟩

def f13 : Formula :=
  .inRegion (.var 0) sx12 ex12

def sx13 : Simplex :=
  ⟨cx13, fun _ => true, by decide +kernel⟩

def ex13 : ExtensionSet :=
  ⟨sx13, fun _ => false, by decide +kernel, by decide +kernel⟩

def f14 : Formula :=
  .inRegion (.var 0) sx13 ex13

def sx14 : Simplex :=
  ⟨cx14, fun _ => true, by decide +kernel⟩

def ex14 : ExtensionSet :=
  ⟨sx14, fun _ => false, by decide +kernel, by decide +kernel⟩

def f15 : Formula :=
  .inRegion (.var 0) sx14 ex14

def sx15 : Simplex :=
  ⟨cx15, fun _ => true, by decide +kernel⟩

def ex15 : ExtensionSet :=
  ⟨sx15, fun _ => false, by decide +kernel, by decide +kernel⟩

def f16 : Formula :=
  .inRegion (.var 0) sx15 ex15

def sx16 : Simplex :=
  ⟨cx16, fun _ => true, by decide +kernel⟩

def ex16 : ExtensionSet :=
  ⟨sx16, fun _ => false, by decide +kernel, by decide +kernel⟩

def f17 : Formula :=
  .inRegion (.var 0) sx16 ex16

def sx17 : Simplex :=
  ⟨cx17, fun _ => true, by decide +kernel⟩

def ex17 : ExtensionSet :=
  ⟨sx17, fun _ => false, by decide +kernel, by decide +kernel⟩

def f18 : Formula :=
  .inRegion (.var 0) sx17 ex17

def f19 : Formula :=
  .or f17 f18

def f20 : Formula :=
  .or f16 f19

def f21 : Formula :=
  .or f15 f20

def f22 : Formula :=
  .or f14 f21

def f23 : Formula :=
  .or f13 f22

def f24 : Formula :=
  .or f12 f23

def f25 : Formula :=
  .or f11 f24

def f26 : Formula :=
  .or f10 f25

def f27 : Formula :=
  .or f9 f26

def f28 : Formula :=
  .or f8 f27

def f29 : Formula :=
  .or f7 f28

def f30 : Formula :=
  .or f6 f29

def f31 : Formula :=
  .or f5 f30

def f32 : Formula :=
  .or f4 f31

def f33 : Formula :=
  .or f3 f32

def f34 : Formula :=
  .or f2 f33

def f35 : Formula :=
  .or f1 f34

def f36 : Formula :=
  .and f0 f35

def f37 : Formula :=
  .and f36 spH

def tm1 : Term :=
  (.add (.mul (.const (-11358359200)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-33059019845)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-916552960)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const 3753967616) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const 16319844352) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)))))))

def f38 : Formula :=
  .atom .le tm1 (.const 0)

def sq0 : Sequent := ⟨f37, f38⟩

def f39 : Formula :=
  .and f0 f1

def f40 : Formula :=
  .and f39 spH

def sq1 : Sequent := ⟨f40, f38⟩

def tm2 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-9212116415/736798)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17816083539/755332)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-39880974396/925475)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3470091493/919463)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (113003629/680228)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1987638632/619331)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (9160848555/474422)) (.idx (.var 0) 0)) (.add (.mul (.const (1886685575/996086)) (.idx (.var 0) 1)) (.add (.mul (.const (3626475869/661239)) (.idx (.var 0) 2)) (.const (-990977063/488209))))))))))) (.sub (.const 1) (.const 1))))

def f41 : Formula :=
  .atom .le tm2 (.const 0)

def sq2 : Sequent := ⟨f40, f41⟩

def sq3 : Sequent := ⟨f40, f0⟩

def sq4 : Sequent := ⟨f40, f39⟩

def f42 : Formula :=
  .and f39 .tt

def sq5 : Sequent := ⟨f40, f42⟩

def tm3 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-9212116415/736798)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17816083539/755332)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-39880974396/925475)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3470091493/919463)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (113003629/680228)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1987638632/619331)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (9160848555/474422)) (.idx (.var 0) 0)) (.add (.mul (.const (1886685575/996086)) (.idx (.var 0) 1)) (.add (.mul (.const (3626475869/661239)) (.idx (.var 0) 2)) (.const (-990977063/488209))))))))))) (.sub tm0 (.const 1))))

def f43 : Formula :=
  .atom .le tm3 (.const 0)

def sq6 : Sequent := ⟨f40, f43⟩

def sq7 : Sequent := ⟨f40, f1⟩

def f44 : Formula :=
  .atom .le (.var predicateHole) (.const 0)

def tm4 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-9212116415/736798)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17816083539/755332)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-39880974396/925475)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3470091493/919463)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (113003629/680228)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1987638632/619331)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (9160848555/474422)) (.idx (.var 0) 0)) (.add (.mul (.const (1886685575/996086)) (.idx (.var 0) 1)) (.add (.mul (.const (3626475869/661239)) (.idx (.var 0) 2)) (.const (-990977063/488209))))))))))) (.sub (.var 1) (.const 1))))

def f45 : Formula :=
  .atom .le tm4 (.const 0)

def f46 : Formula :=
  .and f40 f41

def sq8 : Sequent := ⟨f46, f38⟩

def tm5 : Term :=
  (.add (.mul (.const 83886080) tm2) (.const 0))

def f47 : Formula :=
  .and f0 f34

def f48 : Formula :=
  .and f47 spH

def sq9 : Sequent := ⟨f48, f38⟩

def f49 : Formula :=
  .and f0 f2

def f50 : Formula :=
  .and f49 spH

def sq10 : Sequent := ⟨f50, f38⟩

def tm6 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-17357827671/408805)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3056196860/166203)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-47353696250/910027)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-7140019160/867423)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-5932788006/881359)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8106911/5149)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (20625851142/905215)) (.idx (.var 0) 0)) (.add (.mul (.const (4754466739/606461)) (.idx (.var 0) 1)) (.add (.mul (.const (648472980/147701)) (.idx (.var 0) 2)) (.const (-1774028165/763622))))))))))) (.sub (.const 1) (.const 1))))

def f51 : Formula :=
  .atom .le tm6 (.const 0)

def sq11 : Sequent := ⟨f50, f51⟩

def sq12 : Sequent := ⟨f50, f0⟩

def sq13 : Sequent := ⟨f50, f49⟩

def f52 : Formula :=
  .and f49 .tt

def sq14 : Sequent := ⟨f50, f52⟩

def tm7 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-17357827671/408805)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3056196860/166203)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-47353696250/910027)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-7140019160/867423)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-5932788006/881359)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8106911/5149)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (20625851142/905215)) (.idx (.var 0) 0)) (.add (.mul (.const (4754466739/606461)) (.idx (.var 0) 1)) (.add (.mul (.const (648472980/147701)) (.idx (.var 0) 2)) (.const (-1774028165/763622))))))))))) (.sub tm0 (.const 1))))

def f53 : Formula :=
  .atom .le tm7 (.const 0)

def sq15 : Sequent := ⟨f50, f53⟩

def sq16 : Sequent := ⟨f50, f2⟩

def tm8 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-17357827671/408805)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-3056196860/166203)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-47353696250/910027)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-7140019160/867423)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-5932788006/881359)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-8106911/5149)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (20625851142/905215)) (.idx (.var 0) 0)) (.add (.mul (.const (4754466739/606461)) (.idx (.var 0) 1)) (.add (.mul (.const (648472980/147701)) (.idx (.var 0) 2)) (.const (-1774028165/763622))))))))))) (.sub (.var 1) (.const 1))))

def f54 : Formula :=
  .atom .le tm8 (.const 0)

def f55 : Formula :=
  .and f50 f51

def sq17 : Sequent := ⟨f55, f38⟩

def tm9 : Term :=
  (.add (.mul (.const 83886080) tm6) (.const 0))

def f56 : Formula :=
  .and f0 f33

def f57 : Formula :=
  .and f56 spH

def sq18 : Sequent := ⟨f57, f38⟩

def f58 : Formula :=
  .and f0 f3

def f59 : Formula :=
  .and f58 spH

def sq19 : Sequent := ⟨f59, f38⟩

def tm10 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10701194209/764846)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-2977968480/220799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19512803873/592029)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1034631581/334696)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-169418990/713711)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-779301517/567392)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (4267741117/589928)) (.idx (.var 0) 0)) (.add (.mul (.const (-28617763/553299)) (.idx (.var 0) 1)) (.add (.mul (.const (1599081527/972625)) (.idx (.var 0) 2)) (.const (75361467/808405))))))))))) (.sub (.const 1) (.const 1))))

def f60 : Formula :=
  .atom .le tm10 (.const 0)

def sq20 : Sequent := ⟨f59, f60⟩

def sq21 : Sequent := ⟨f59, f0⟩

def sq22 : Sequent := ⟨f59, f58⟩

def f61 : Formula :=
  .and f58 .tt

def sq23 : Sequent := ⟨f59, f61⟩

def tm11 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10701194209/764846)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-2977968480/220799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19512803873/592029)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1034631581/334696)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-169418990/713711)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-779301517/567392)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (4267741117/589928)) (.idx (.var 0) 0)) (.add (.mul (.const (-28617763/553299)) (.idx (.var 0) 1)) (.add (.mul (.const (1599081527/972625)) (.idx (.var 0) 2)) (.const (75361467/808405))))))))))) (.sub tm0 (.const 1))))

def f62 : Formula :=
  .atom .le tm11 (.const 0)

def sq24 : Sequent := ⟨f59, f62⟩

def sq25 : Sequent := ⟨f59, f3⟩

def tm12 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10701194209/764846)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-2977968480/220799)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-19512803873/592029)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-1034631581/334696)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-169418990/713711)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-779301517/567392)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (4267741117/589928)) (.idx (.var 0) 0)) (.add (.mul (.const (-28617763/553299)) (.idx (.var 0) 1)) (.add (.mul (.const (1599081527/972625)) (.idx (.var 0) 2)) (.const (75361467/808405))))))))))) (.sub (.var 1) (.const 1))))

def f63 : Formula :=
  .atom .le tm12 (.const 0)

def f64 : Formula :=
  .and f59 f60

def sq26 : Sequent := ⟨f64, f38⟩

def tm13 : Term :=
  (.add (.mul (.const 83886080) tm10) (.const 0))

def f65 : Formula :=
  .and f0 f32

def f66 : Formula :=
  .and f65 spH

def sq27 : Sequent := ⟨f66, f38⟩

def f67 : Formula :=
  .and f0 f4

def f68 : Formula :=
  .and f67 spH

def sq28 : Sequent := ⟨f68, f38⟩

def tm14 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1559214560/80123)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-28278170251/675890)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-76547066693/816830)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3599907805/855053)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (463789/618798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4633600348/989321)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1973304951/155978)) (.idx (.var 0) 0)) (.add (.mul (.const (-447498697/559040)) (.idx (.var 0) 1)) (.add (.mul (.const (2244104419/806325)) (.idx (.var 0) 2)) (.const (89358151/161201))))))))))) (.sub (.const 1) (.const 1))))

def f69 : Formula :=
  .atom .le tm14 (.const 0)

def sq29 : Sequent := ⟨f68, f69⟩

def sq30 : Sequent := ⟨f68, f0⟩

def sq31 : Sequent := ⟨f68, f67⟩

def f70 : Formula :=
  .and f67 .tt

def sq32 : Sequent := ⟨f68, f70⟩

def tm15 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1559214560/80123)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-28278170251/675890)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-76547066693/816830)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3599907805/855053)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (463789/618798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4633600348/989321)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1973304951/155978)) (.idx (.var 0) 0)) (.add (.mul (.const (-447498697/559040)) (.idx (.var 0) 1)) (.add (.mul (.const (2244104419/806325)) (.idx (.var 0) 2)) (.const (89358151/161201))))))))))) (.sub tm0 (.const 1))))

def f71 : Formula :=
  .atom .le tm15 (.const 0)

def sq33 : Sequent := ⟨f68, f71⟩

def sq34 : Sequent := ⟨f68, f4⟩

def tm16 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1559214560/80123)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-28278170251/675890)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-76547066693/816830)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-3599907805/855053)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (463789/618798)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4633600348/989321)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (1973304951/155978)) (.idx (.var 0) 0)) (.add (.mul (.const (-447498697/559040)) (.idx (.var 0) 1)) (.add (.mul (.const (2244104419/806325)) (.idx (.var 0) 2)) (.const (89358151/161201))))))))))) (.sub (.var 1) (.const 1))))

def f72 : Formula :=
  .atom .le tm16 (.const 0)

def f73 : Formula :=
  .and f68 f69

def sq35 : Sequent := ⟨f73, f38⟩

def tm17 : Term :=
  (.add (.mul (.const 83886080) tm14) (.const 0))

def f74 : Formula :=
  .and f0 f31

def f75 : Formula :=
  .and f74 spH

def sq36 : Sequent := ⟨f75, f38⟩

def f76 : Formula :=
  .and f0 f5

def f77 : Formula :=
  .and f76 spH

def sq37 : Sequent := ⟨f77, f38⟩

def tm18 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-7029682751/928392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32519419757/862335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-71992620711/992248)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-629701978/296277)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (84139/325497)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-213243283/43624)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (17824718349/999370)) (.idx (.var 0) 0)) (.add (.mul (.const (280922158/291763)) (.idx (.var 0) 1)) (.add (.mul (.const (2909460581/617022)) (.idx (.var 0) 2)) (.const (-1102160898/915469))))))))))) (.sub (.const 1) (.const 1))))

def f78 : Formula :=
  .atom .le tm18 (.const 0)

def sq38 : Sequent := ⟨f77, f78⟩

def sq39 : Sequent := ⟨f77, f0⟩

def sq40 : Sequent := ⟨f77, f76⟩

def f79 : Formula :=
  .and f76 .tt

def sq41 : Sequent := ⟨f77, f79⟩

def tm19 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-7029682751/928392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32519419757/862335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-71992620711/992248)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-629701978/296277)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (84139/325497)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-213243283/43624)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (17824718349/999370)) (.idx (.var 0) 0)) (.add (.mul (.const (280922158/291763)) (.idx (.var 0) 1)) (.add (.mul (.const (2909460581/617022)) (.idx (.var 0) 2)) (.const (-1102160898/915469))))))))))) (.sub tm0 (.const 1))))

def f80 : Formula :=
  .atom .le tm19 (.const 0)

def sq42 : Sequent := ⟨f77, f80⟩

def sq43 : Sequent := ⟨f77, f5⟩

def tm20 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-7029682751/928392)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32519419757/862335)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-71992620711/992248)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-629701978/296277)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (84139/325497)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-213243283/43624)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (17824718349/999370)) (.idx (.var 0) 0)) (.add (.mul (.const (280922158/291763)) (.idx (.var 0) 1)) (.add (.mul (.const (2909460581/617022)) (.idx (.var 0) 2)) (.const (-1102160898/915469))))))))))) (.sub (.var 1) (.const 1))))

def f81 : Formula :=
  .atom .le tm20 (.const 0)

def f82 : Formula :=
  .and f77 f78

def sq44 : Sequent := ⟨f82, f38⟩

def tm21 : Term :=
  (.add (.mul (.const 83886080) tm18) (.const 0))

def f83 : Formula :=
  .and f0 f30

def f84 : Formula :=
  .and f83 spH

def sq45 : Sequent := ⟨f84, f38⟩

def f85 : Formula :=
  .and f0 f6

def f86 : Formula :=
  .and f85 spH

def sq46 : Sequent := ⟨f86, f38⟩

def tm22 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10501885393/506234)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17724334321/930713)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-46173085559/877199)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-404331576/101413)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-630065298/265441)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1019494363/622251)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (6449585089/897800)) (.idx (.var 0) 0)) (.add (.mul (.const (1730079677/696494)) (.idx (.var 0) 1)) (.add (.mul (.const (958535719/839894)) (.idx (.var 0) 2)) (.const (-342511961/640022))))))))))) (.sub (.const 1) (.const 1))))

def f87 : Formula :=
  .atom .le tm22 (.const 0)

def sq47 : Sequent := ⟨f86, f87⟩

def sq48 : Sequent := ⟨f86, f0⟩

def sq49 : Sequent := ⟨f86, f85⟩

def f88 : Formula :=
  .and f85 .tt

def sq50 : Sequent := ⟨f86, f88⟩

def tm23 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10501885393/506234)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17724334321/930713)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-46173085559/877199)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-404331576/101413)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-630065298/265441)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1019494363/622251)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (6449585089/897800)) (.idx (.var 0) 0)) (.add (.mul (.const (1730079677/696494)) (.idx (.var 0) 1)) (.add (.mul (.const (958535719/839894)) (.idx (.var 0) 2)) (.const (-342511961/640022))))))))))) (.sub tm0 (.const 1))))

def f89 : Formula :=
  .atom .le tm23 (.const 0)

def sq51 : Sequent := ⟨f86, f89⟩

def sq52 : Sequent := ⟨f86, f6⟩

def tm24 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-10501885393/506234)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-17724334321/930713)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-46173085559/877199)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-404331576/101413)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-630065298/265441)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1019494363/622251)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (6449585089/897800)) (.idx (.var 0) 0)) (.add (.mul (.const (1730079677/696494)) (.idx (.var 0) 1)) (.add (.mul (.const (958535719/839894)) (.idx (.var 0) 2)) (.const (-342511961/640022))))))))))) (.sub (.var 1) (.const 1))))

def f90 : Formula :=
  .atom .le tm24 (.const 0)

def f91 : Formula :=
  .and f86 f87

def sq53 : Sequent := ⟨f91, f38⟩

def tm25 : Term :=
  (.add (.mul (.const 83886080) tm22) (.const 0))

def f92 : Formula :=
  .and f0 f29

def f93 : Formula :=
  .and f92 spH

def sq54 : Sequent := ⟨f93, f38⟩

def f94 : Formula :=
  .and f0 f7

def f95 : Formula :=
  .and f94 spH

def sq55 : Sequent := ⟨f95, f38⟩

def tm26 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-661437301/685256)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-258014919119/945687)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-15411236884/50611)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (521541591576/888617)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (11338106183/878101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (68016689360/231973)) (.idx (.var 0) 2)) (.const (462795352782/997219))))))))))) (.sub (.const 1) (.const 1))))

def f96 : Formula :=
  .atom .le tm26 (.const 0)

def sq56 : Sequent := ⟨f95, f96⟩

def sq57 : Sequent := ⟨f95, f0⟩

def sq58 : Sequent := ⟨f95, f94⟩

def f97 : Formula :=
  .and f94 .tt

def sq59 : Sequent := ⟨f95, f97⟩

def tm27 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-661437301/685256)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-258014919119/945687)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-15411236884/50611)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (521541591576/888617)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (11338106183/878101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (68016689360/231973)) (.idx (.var 0) 2)) (.const (462795352782/997219))))))))))) (.sub tm0 (.const 1))))

def f98 : Formula :=
  .atom .le tm27 (.const 0)

def sq60 : Sequent := ⟨f95, f98⟩

def sq61 : Sequent := ⟨f95, f7⟩

def tm28 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-661437301/685256)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-258014919119/945687)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-15411236884/50611)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (521541591576/888617)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (11338106183/878101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (68016689360/231973)) (.idx (.var 0) 2)) (.const (462795352782/997219))))))))))) (.sub (.var 1) (.const 1))))

def f99 : Formula :=
  .atom .le tm28 (.const 0)

def f100 : Formula :=
  .and f95 f96

def sq62 : Sequent := ⟨f100, f38⟩

def tm29 : Term :=
  (.add (.mul (.const 83886080) tm26) (.const 0))

def f101 : Formula :=
  .and f0 f28

def f102 : Formula :=
  .and f101 spH

def sq63 : Sequent := ⟨f102, f38⟩

def f103 : Formula :=
  .and f0 f8

def f104 : Formula :=
  .and f103 spH

def sq64 : Sequent := ⟨f104, f38⟩

def tm30 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7409402106/14521)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (395135635927/852597)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-279502578629/506082)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (58361761484/95649)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (12541397811/133900)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (732854468779/820322)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (137863165435/284322)) (.idx (.var 0) 2)) (.const (23167093622/51517))))))))))) (.sub (.const 1) (.const 1))))

def f105 : Formula :=
  .atom .le tm30 (.const 0)

def sq65 : Sequent := ⟨f104, f105⟩

def sq66 : Sequent := ⟨f104, f0⟩

def sq67 : Sequent := ⟨f104, f103⟩

def f106 : Formula :=
  .and f103 .tt

def sq68 : Sequent := ⟨f104, f106⟩

def tm31 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7409402106/14521)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (395135635927/852597)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-279502578629/506082)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (58361761484/95649)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (12541397811/133900)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (732854468779/820322)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (137863165435/284322)) (.idx (.var 0) 2)) (.const (23167093622/51517))))))))))) (.sub tm0 (.const 1))))

def f107 : Formula :=
  .atom .le tm31 (.const 0)

def sq69 : Sequent := ⟨f104, f107⟩

def sq70 : Sequent := ⟨f104, f8⟩

def tm32 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (7409402106/14521)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (395135635927/852597)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-279502578629/506082)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (58361761484/95649)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (12541397811/133900)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (732854468779/820322)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (137863165435/284322)) (.idx (.var 0) 2)) (.const (23167093622/51517))))))))))) (.sub (.var 1) (.const 1))))

def f108 : Formula :=
  .atom .le tm32 (.const 0)

def f109 : Formula :=
  .and f104 f105

def sq71 : Sequent := ⟨f109, f38⟩

def tm33 : Term :=
  (.add (.mul (.const 83886080) tm30) (.const 0))

def f110 : Formula :=
  .and f0 f27

def f111 : Formula :=
  .and f110 spH

def sq72 : Sequent := ⟨f111, f38⟩

def f112 : Formula :=
  .and f0 f9

def f113 : Formula :=
  .and f112 spH

def sq73 : Sequent := ⟨f113, f38⟩

def tm34 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (71915534756/879533)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-100742781505/230848)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-175163318797/575242)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (101623539770/173149)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (32824548576/975361)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (701928502647/715505)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (85883972356/318043)) (.idx (.var 0) 2)) (.const (96742108525/205793))))))))))) (.sub (.const 1) (.const 1))))

def f114 : Formula :=
  .atom .le tm34 (.const 0)

def sq74 : Sequent := ⟨f113, f114⟩

def sq75 : Sequent := ⟨f113, f0⟩

def sq76 : Sequent := ⟨f113, f112⟩

def f115 : Formula :=
  .and f112 .tt

def sq77 : Sequent := ⟨f113, f115⟩

def tm35 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (71915534756/879533)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-100742781505/230848)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-175163318797/575242)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (101623539770/173149)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (32824548576/975361)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (701928502647/715505)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (85883972356/318043)) (.idx (.var 0) 2)) (.const (96742108525/205793))))))))))) (.sub tm0 (.const 1))))

def f116 : Formula :=
  .atom .le tm35 (.const 0)

def sq78 : Sequent := ⟨f113, f116⟩

def sq79 : Sequent := ⟨f113, f9⟩

def tm36 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (71915534756/879533)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-100742781505/230848)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-175163318797/575242)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (101623539770/173149)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (32824548576/975361)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (701928502647/715505)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (85883972356/318043)) (.idx (.var 0) 2)) (.const (96742108525/205793))))))))))) (.sub (.var 1) (.const 1))))

def f117 : Formula :=
  .atom .le tm36 (.const 0)

def f118 : Formula :=
  .and f113 f114

def sq80 : Sequent := ⟨f118, f38⟩

def tm37 : Term :=
  (.add (.mul (.const 83886080) tm34) (.const 0))

def f119 : Formula :=
  .and f0 f26

def f120 : Formula :=
  .and f119 spH

def sq81 : Sequent := ⟨f120, f38⟩

def f121 : Formula :=
  .and f0 f10

def f122 : Formula :=
  .and f121 spH

def sq82 : Sequent := ⟨f122, f38⟩

def tm38 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-792284635151/924681)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-409970635214/855021)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-172975014909/625132)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (338301749277/583532)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33577418773/643715)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (309147689765/972418)) (.idx (.var 0) 2)) (.const (247326271696/536751))))))))))) (.sub (.const 1) (.const 1))))

def f123 : Formula :=
  .atom .le tm38 (.const 0)

def sq83 : Sequent := ⟨f122, f123⟩

def sq84 : Sequent := ⟨f122, f0⟩

def sq85 : Sequent := ⟨f122, f121⟩

def f124 : Formula :=
  .and f121 .tt

def sq86 : Sequent := ⟨f122, f124⟩

def tm39 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-792284635151/924681)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-409970635214/855021)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-172975014909/625132)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (338301749277/583532)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33577418773/643715)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (309147689765/972418)) (.idx (.var 0) 2)) (.const (247326271696/536751))))))))))) (.sub tm0 (.const 1))))

def f125 : Formula :=
  .atom .le tm39 (.const 0)

def sq87 : Sequent := ⟨f122, f125⟩

def sq88 : Sequent := ⟨f122, f10⟩

def tm40 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-792284635151/924681)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-409970635214/855021)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-172975014909/625132)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (338301749277/583532)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33577418773/643715)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (309147689765/972418)) (.idx (.var 0) 2)) (.const (247326271696/536751))))))))))) (.sub (.var 1) (.const 1))))

def f126 : Formula :=
  .atom .le tm40 (.const 0)

def f127 : Formula :=
  .and f122 f123

def sq89 : Sequent := ⟨f127, f38⟩

def tm41 : Term :=
  (.add (.mul (.const 83886080) tm38) (.const 0))

def f128 : Formula :=
  .and f0 f25

def f129 : Formula :=
  .and f128 spH

def sq90 : Sequent := ⟨f129, f38⟩

def f130 : Formula :=
  .and f0 f11

def f131 : Formula :=
  .and f130 spH

def sq91 : Sequent := ⟨f131, f38⟩

def tm42 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-661752555389/725655)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-134651753219/857299)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-948708116735/912307)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (261893/997501)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (5989023447/931099)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (202698970395/882893)) (.idx (.var 0) 1)) (.add (.mul (.const 1048576) (.idx (.var 0) 2)) (.const (-16794180739/71751))))))))))) (.sub (.const 1) (.const 1))))

def f132 : Formula :=
  .atom .le tm42 (.const 0)

def sq92 : Sequent := ⟨f131, f132⟩

def sq93 : Sequent := ⟨f131, f0⟩

def sq94 : Sequent := ⟨f131, f130⟩

def f133 : Formula :=
  .and f130 .tt

def sq95 : Sequent := ⟨f131, f133⟩

def tm43 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-661752555389/725655)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-134651753219/857299)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-948708116735/912307)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (261893/997501)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (5989023447/931099)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (202698970395/882893)) (.idx (.var 0) 1)) (.add (.mul (.const 1048576) (.idx (.var 0) 2)) (.const (-16794180739/71751))))))))))) (.sub tm0 (.const 1))))

def f134 : Formula :=
  .atom .le tm43 (.const 0)

def sq96 : Sequent := ⟨f131, f134⟩

def sq97 : Sequent := ⟨f131, f11⟩

def tm44 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-661752555389/725655)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-134651753219/857299)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-948708116735/912307)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (261893/997501)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (5989023447/931099)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (202698970395/882893)) (.idx (.var 0) 1)) (.add (.mul (.const 1048576) (.idx (.var 0) 2)) (.const (-16794180739/71751))))))))))) (.sub (.var 1) (.const 1))))

def f135 : Formula :=
  .atom .le tm44 (.const 0)

def f136 : Formula :=
  .and f131 f132

def sq98 : Sequent := ⟨f136, f38⟩

def tm45 : Term :=
  (.add (.mul (.const 83886080) tm42) (.const 0))

def f137 : Formula :=
  .and f0 f24

def f138 : Formula :=
  .and f137 spH

def sq99 : Sequent := ⟨f138, f38⟩

def f139 : Formula :=
  .and f0 f12

def f140 : Formula :=
  .and f139 spH

def sq100 : Sequent := ⟨f140, f38⟩

def tm46 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-108097819633/300567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-623451466219/808637)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (251865988563/959360)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (340961748911/713007)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33379836269/801348)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-54908633193/61070)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-168675864239/740629)) (.idx (.var 0) 2)) (.const (558778076585/992049))))))))))) (.sub (.const 1) (.const 1))))

def f141 : Formula :=
  .atom .le tm46 (.const 0)

def sq101 : Sequent := ⟨f140, f141⟩

def sq102 : Sequent := ⟨f140, f0⟩

def sq103 : Sequent := ⟨f140, f139⟩

def f142 : Formula :=
  .and f139 .tt

def sq104 : Sequent := ⟨f140, f142⟩

def tm47 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-108097819633/300567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-623451466219/808637)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (251865988563/959360)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (340961748911/713007)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33379836269/801348)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-54908633193/61070)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-168675864239/740629)) (.idx (.var 0) 2)) (.const (558778076585/992049))))))))))) (.sub tm0 (.const 1))))

def f143 : Formula :=
  .atom .le tm47 (.const 0)

def sq105 : Sequent := ⟨f140, f143⟩

def sq106 : Sequent := ⟨f140, f12⟩

def tm48 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const 1048576) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-108097819633/300567)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-623451466219/808637)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (251865988563/959360)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (340961748911/713007)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-33379836269/801348)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-54908633193/61070)) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-168675864239/740629)) (.idx (.var 0) 2)) (.const (558778076585/992049))))))))))) (.sub (.var 1) (.const 1))))

def f144 : Formula :=
  .atom .le tm48 (.const 0)

def f145 : Formula :=
  .and f140 f141

def sq107 : Sequent := ⟨f145, f38⟩

def tm49 : Term :=
  (.add (.mul (.const 83886080) tm46) (.const 0))

def f146 : Formula :=
  .and f0 f23

def f147 : Formula :=
  .and f146 spH

def sq108 : Sequent := ⟨f147, f38⟩

def f148 : Formula :=
  .and f0 f13

def f149 : Formula :=
  .and f148 spH

def sq109 : Sequent := ⟨f149, f38⟩

def tm50 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-496792555145/632394)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-550305052847/834442)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-83641964757/391945)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (498690420040/875573)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-74995257541/987491)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (220269341509/776056)) (.idx (.var 0) 2)) (.const (376979076646/812623))))))))))) (.sub (.const 1) (.const 1))))

def f150 : Formula :=
  .atom .le tm50 (.const 0)

def sq110 : Sequent := ⟨f149, f150⟩

def sq111 : Sequent := ⟨f149, f0⟩

def sq112 : Sequent := ⟨f149, f148⟩

def f151 : Formula :=
  .and f148 .tt

def sq113 : Sequent := ⟨f149, f151⟩

def tm51 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-496792555145/632394)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-550305052847/834442)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-83641964757/391945)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (498690420040/875573)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-74995257541/987491)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (220269341509/776056)) (.idx (.var 0) 2)) (.const (376979076646/812623))))))))))) (.sub tm0 (.const 1))))

def f152 : Formula :=
  .atom .le tm51 (.const 0)

def sq114 : Sequent := ⟨f149, f152⟩

def sq115 : Sequent := ⟨f149, f13⟩

def tm52 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-496792555145/632394)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-550305052847/834442)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-1048576)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-83641964757/391945)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (498690420040/875573)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-74995257541/987491)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (220269341509/776056)) (.idx (.var 0) 2)) (.const (376979076646/812623))))))))))) (.sub (.var 1) (.const 1))))

def f153 : Formula :=
  .atom .le tm52 (.const 0)

def f154 : Formula :=
  .and f149 f150

def sq116 : Sequent := ⟨f154, f38⟩

def tm53 : Term :=
  (.add (.mul (.const 83886080) tm50) (.const 0))

def f155 : Formula :=
  .and f0 f22

def f156 : Formula :=
  .and f155 spH

def sq117 : Sequent := ⟨f156, f38⟩

def f157 : Formula :=
  .and f0 f14

def f158 : Formula :=
  .and f157 spH

def sq118 : Sequent := ⟨f158, f38⟩

def tm54 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (43978272062/486779)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8880586239/387586)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-2591225907/257413)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (6025803682/257741)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-25861635160/453857)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4442120719/998101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-8637324497/95916)) (.idx (.var 0) 0)) (.add (.mul (.const (97847910745/937698)) (.idx (.var 0) 1)) (.add (.mul (.const (-13666481360/635447)) (.idx (.var 0) 2)) (.const (-46422367583/981542))))))))))) (.sub (.const 1) (.const 1))))

def f159 : Formula :=
  .atom .le tm54 (.const 0)

def sq119 : Sequent := ⟨f158, f159⟩

def sq120 : Sequent := ⟨f158, f0⟩

def sq121 : Sequent := ⟨f158, f157⟩

def f160 : Formula :=
  .and f157 .tt

def sq122 : Sequent := ⟨f158, f160⟩

def tm55 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (43978272062/486779)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8880586239/387586)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-2591225907/257413)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (6025803682/257741)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-25861635160/453857)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4442120719/998101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-8637324497/95916)) (.idx (.var 0) 0)) (.add (.mul (.const (97847910745/937698)) (.idx (.var 0) 1)) (.add (.mul (.const (-13666481360/635447)) (.idx (.var 0) 2)) (.const (-46422367583/981542))))))))))) (.sub tm0 (.const 1))))

def f161 : Formula :=
  .atom .le tm55 (.const 0)

def sq123 : Sequent := ⟨f158, f161⟩

def sq124 : Sequent := ⟨f158, f14⟩

def tm56 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (43978272062/486779)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-8880586239/387586)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-2591225907/257413)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (6025803682/257741)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (-25861635160/453857)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-4442120719/998101)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-8637324497/95916)) (.idx (.var 0) 0)) (.add (.mul (.const (97847910745/937698)) (.idx (.var 0) 1)) (.add (.mul (.const (-13666481360/635447)) (.idx (.var 0) 2)) (.const (-46422367583/981542))))))))))) (.sub (.var 1) (.const 1))))

def f162 : Formula :=
  .atom .le tm56 (.const 0)

def f163 : Formula :=
  .and f158 f159

def sq125 : Sequent := ⟨f163, f38⟩

def tm57 : Term :=
  (.add (.mul (.const 83886080) tm54) (.const 0))

def f164 : Formula :=
  .and f0 f21

def f165 : Formula :=
  .and f164 spH

def sq126 : Sequent := ⟨f165, f38⟩

def f166 : Formula :=
  .and f0 f15

def f167 : Formula :=
  .and f166 spH

def sq127 : Sequent := ⟨f167, f38⟩

def tm58 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-677955361481/748247)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32699973314/53305)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-79535278489/606697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (273999176/1395)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (393785011000/746393)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-113528412401/897386)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-78613371669/724205)) (.idx (.var 0) 2)) (.const (26502304331/52191))))))))))) (.sub (.const 1) (.const 1))))

def f168 : Formula :=
  .atom .le tm58 (.const 0)

def sq128 : Sequent := ⟨f167, f168⟩

def sq129 : Sequent := ⟨f167, f0⟩

def sq130 : Sequent := ⟨f167, f166⟩

def f169 : Formula :=
  .and f166 .tt

def sq131 : Sequent := ⟨f167, f169⟩

def tm59 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-677955361481/748247)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32699973314/53305)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-79535278489/606697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (273999176/1395)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (393785011000/746393)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-113528412401/897386)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-78613371669/724205)) (.idx (.var 0) 2)) (.const (26502304331/52191))))))))))) (.sub tm0 (.const 1))))

def f170 : Formula :=
  .atom .le tm59 (.const 0)

def sq132 : Sequent := ⟨f167, f170⟩

def sq133 : Sequent := ⟨f167, f15⟩

def tm60 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-677955361481/748247)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-32699973314/53305)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-79535278489/606697)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (273999176/1395)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (393785011000/746393)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-113528412401/897386)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (-78613371669/724205)) (.idx (.var 0) 2)) (.const (26502304331/52191))))))))))) (.sub (.var 1) (.const 1))))

def f171 : Formula :=
  .atom .le tm60 (.const 0)

def f172 : Formula :=
  .and f167 f168

def sq134 : Sequent := ⟨f172, f38⟩

def tm61 : Term :=
  (.add (.mul (.const 83886080) tm58) (.const 0))

def f173 : Formula :=
  .and f0 f20

def f174 : Formula :=
  .and f173 spH

def sq135 : Sequent := ⟨f174, f38⟩

def f175 : Formula :=
  .and f0 f16

def f176 : Formula :=
  .and f175 spH

def sq136 : Sequent := ⟨f176, f38⟩

def tm62 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-772552344829/840111)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-14873296987/35144)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-28870375411/73557)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-209091920879/720904)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (110249707007/193317)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-46435252425/667943)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (100768501446/298907)) (.idx (.var 0) 2)) (.const (453416429051/963643))))))))))) (.sub (.const 1) (.const 1))))

def f177 : Formula :=
  .atom .le tm62 (.const 0)

def sq137 : Sequent := ⟨f176, f177⟩

def sq138 : Sequent := ⟨f176, f0⟩

def sq139 : Sequent := ⟨f176, f175⟩

def f178 : Formula :=
  .and f175 .tt

def sq140 : Sequent := ⟨f176, f178⟩

def tm63 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-772552344829/840111)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-14873296987/35144)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-28870375411/73557)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-209091920879/720904)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (110249707007/193317)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-46435252425/667943)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (100768501446/298907)) (.idx (.var 0) 2)) (.const (453416429051/963643))))))))))) (.sub tm0 (.const 1))))

def f179 : Formula :=
  .atom .le tm63 (.const 0)

def sq141 : Sequent := ⟨f176, f179⟩

def sq142 : Sequent := ⟨f176, f16⟩

def tm64 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-772552344829/840111)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-14873296987/35144)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-28870375411/73557)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-209091920879/720904)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (110249707007/193317)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-46435252425/667943)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const 1048576) (.idx (.var 0) 0)) (.add (.mul (.const (-1048576)) (.idx (.var 0) 1)) (.add (.mul (.const (100768501446/298907)) (.idx (.var 0) 2)) (.const (453416429051/963643))))))))))) (.sub (.var 1) (.const 1))))

def f180 : Formula :=
  .atom .le tm64 (.const 0)

def f181 : Formula :=
  .and f176 f177

def sq143 : Sequent := ⟨f181, f38⟩

def tm65 : Term :=
  (.add (.mul (.const 83886080) tm62) (.const 0))

def f182 : Formula :=
  .and f0 f19

def f183 : Formula :=
  .and f182 spH

def sq144 : Sequent := ⟨f183, f38⟩

def f184 : Formula :=
  .and f0 f17

def f185 : Formula :=
  .and f184 spH

def sq145 : Sequent := ⟨f185, f38⟩

def tm66 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (69311919995/781826)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-23286546721/922469)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-9612624910/661489)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (17991295675/903936)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (262148/653189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1012425898/236075)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-26570654040/302447)) (.idx (.var 0) 0)) (.add (.mul (.const (-4216145545/597187)) (.idx (.var 0) 1)) (.add (.mul (.const (-9129485807/507501)) (.idx (.var 0) 2)) (.const (4950150242/695981))))))))))) (.sub (.const 1) (.const 1))))

def f186 : Formula :=
  .atom .le tm66 (.const 0)

def sq146 : Sequent := ⟨f185, f186⟩

def sq147 : Sequent := ⟨f185, f0⟩

def sq148 : Sequent := ⟨f185, f184⟩

def f187 : Formula :=
  .and f184 .tt

def sq149 : Sequent := ⟨f185, f187⟩

def tm67 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (69311919995/781826)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-23286546721/922469)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-9612624910/661489)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (17991295675/903936)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (262148/653189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1012425898/236075)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-26570654040/302447)) (.idx (.var 0) 0)) (.add (.mul (.const (-4216145545/597187)) (.idx (.var 0) 1)) (.add (.mul (.const (-9129485807/507501)) (.idx (.var 0) 2)) (.const (4950150242/695981))))))))))) (.sub tm0 (.const 1))))

def f188 : Formula :=
  .atom .le tm67 (.const 0)

def sq150 : Sequent := ⟨f185, f188⟩

def sq151 : Sequent := ⟨f185, f17⟩

def tm68 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (69311919995/781826)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-23286546721/922469)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-9612624910/661489)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (17991295675/903936)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (262148/653189)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-1012425898/236075)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (-26570654040/302447)) (.idx (.var 0) 0)) (.add (.mul (.const (-4216145545/597187)) (.idx (.var 0) 1)) (.add (.mul (.const (-9129485807/507501)) (.idx (.var 0) 2)) (.const (4950150242/695981))))))))))) (.sub (.var 1) (.const 1))))

def f189 : Formula :=
  .atom .le tm68 (.const 0)

def f190 : Formula :=
  .and f185 f186

def sq152 : Sequent := ⟨f190, f38⟩

def tm69 : Term :=
  (.add (.mul (.const 83886080) tm66) (.const 0))

def f191 : Formula :=
  .and f0 f18

def f192 : Formula :=
  .and f191 spH

def sq153 : Sequent := ⟨f192, f38⟩

def tm70 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-90819800403/329416)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-263385207903/769978)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-444337291391/489519)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-58662170167/963357)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (106431/265192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-31417287166/995923)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (422498160987/984215)) (.idx (.var 0) 0)) (.add (.mul (.const (10525745269/475445)) (.idx (.var 0) 1)) (.add (.mul (.const (65202508528/724687)) (.idx (.var 0) 2)) (.const (-25982148881/907586))))))))))) (.sub (.const 1) (.const 1))))

def f193 : Formula :=
  .atom .le tm70 (.const 0)

def sq154 : Sequent := ⟨f192, f193⟩

def sq155 : Sequent := ⟨f192, f0⟩

def sq156 : Sequent := ⟨f192, f191⟩

def f194 : Formula :=
  .and f191 .tt

def sq157 : Sequent := ⟨f192, f194⟩

def tm71 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-90819800403/329416)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-263385207903/769978)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-444337291391/489519)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-58662170167/963357)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (106431/265192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-31417287166/995923)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (422498160987/984215)) (.idx (.var 0) 0)) (.add (.mul (.const (10525745269/475445)) (.idx (.var 0) 1)) (.add (.mul (.const (65202508528/724687)) (.idx (.var 0) 2)) (.const (-25982148881/907586))))))))))) (.sub tm0 (.const 1))))

def f195 : Formula :=
  .atom .le tm71 (.const 0)

def sq158 : Sequent := ⟨f192, f195⟩

def sq159 : Sequent := ⟨f192, f18⟩

def tm72 : Term :=
  (.add (.add (.mul (.const (-70989745/524288)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 1)) (.idx (.var 0) 2))) (.add (.mul (.const (-6611803969/16777216)) (.mul (.mul (.idx (.var 0) 0) (.idx (.var 0) 0)) (.idx (.var 0) 1))) (.add (.mul (.const (-716057/65536)) (.mul (.mul (.idx (.var 0) 1) (.idx (.var 0) 2)) (.idx (.var 0) 2))) (.add (.mul (.const (57281/1280)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.mul (.const (3984337/20480)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))))))) (.mul (.add (.mul (.const (-90819800403/329416)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 1))) (.add (.mul (.const (-263385207903/769978)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 2))) (.add (.mul (.const (-444337291391/489519)) (.mul (.idx (.var 0) 0) (.idx (.var 0) 0))) (.add (.mul (.const (-58662170167/963357)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 2))) (.add (.mul (.const (106431/265192)) (.mul (.idx (.var 0) 1) (.idx (.var 0) 1))) (.add (.mul (.const (-31417287166/995923)) (.mul (.idx (.var 0) 2) (.idx (.var 0) 2))) (.add (.mul (.const (422498160987/984215)) (.idx (.var 0) 0)) (.add (.mul (.const (10525745269/475445)) (.idx (.var 0) 1)) (.add (.mul (.const (65202508528/724687)) (.idx (.var 0) 2)) (.const (-25982148881/907586))))))))))) (.sub (.var 1) (.const 1))))

def f196 : Formula :=
  .atom .le tm72 (.const 0)

def f197 : Formula :=
  .and f192 f193

def sq160 : Sequent := ⟨f197, f38⟩

def tm73 : Term :=
  (.add (.mul (.const 83886080) tm70) (.const 0))

def pf0 : ProofObject Hnet sq5 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf1 : ProofObject Hnet sq4 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq5 pf0 .tt rfl rfl))

def pf2 : ProofObject Hnet sq3 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq4 pf1 f1 rfl rfl))

def pf3 : ProofObject Hnet sq5 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf4 : ProofObject Hnet sq4 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq5 pf3 .tt rfl rfl))

def pf5 : ProofObject Hnet sq7 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq4 pf4 f0 rfl rfl))

def pf6 : ProofObject Hnet sq6 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq7) (regionProof := pf5)
    (termX := (.var 0)) (simplex := sx0) (S := ex0)
    (degree := 5) (polynomial := tm3) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex0) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf7 : ProofObject Hnet sq2 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq3 pf2 sq6 pf6
    1 tm0 (.const 1) f45
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf8 : ProofObject Hnet sq8 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm5
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf9 : ProofObject Hnet sq1 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f41
    sq2 pf7 sq8 pf8
    rfl rfl rfl rfl))

def pf10 : ProofObject Hnet sq14 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf11 : ProofObject Hnet sq13 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq14 pf10 .tt rfl rfl))

def pf12 : ProofObject Hnet sq12 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq13 pf11 f2 rfl rfl))

def pf13 : ProofObject Hnet sq14 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf14 : ProofObject Hnet sq13 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq14 pf13 .tt rfl rfl))

def pf15 : ProofObject Hnet sq16 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq13 pf14 f0 rfl rfl))

def pf16 : ProofObject Hnet sq15 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq16) (regionProof := pf15)
    (termX := (.var 0)) (simplex := sx1) (S := ex1)
    (degree := 5) (polynomial := tm7) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex1) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf17 : ProofObject Hnet sq11 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq12 pf12 sq15 pf16
    1 tm0 (.const 1) f54
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf18 : ProofObject Hnet sq17 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm9
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf19 : ProofObject Hnet sq10 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f51
    sq11 pf17 sq17 pf18
    rfl rfl rfl rfl))

def pf20 : ProofObject Hnet sq23 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf21 : ProofObject Hnet sq22 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq23 pf20 .tt rfl rfl))

def pf22 : ProofObject Hnet sq21 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq22 pf21 f3 rfl rfl))

def pf23 : ProofObject Hnet sq23 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf24 : ProofObject Hnet sq22 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq23 pf23 .tt rfl rfl))

def pf25 : ProofObject Hnet sq25 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq22 pf24 f0 rfl rfl))

def pf26 : ProofObject Hnet sq24 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq25) (regionProof := pf25)
    (termX := (.var 0)) (simplex := sx2) (S := ex2)
    (degree := 5) (polynomial := tm11) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex2) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf27 : ProofObject Hnet sq20 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq21 pf22 sq24 pf26
    1 tm0 (.const 1) f63
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf28 : ProofObject Hnet sq26 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm13
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf29 : ProofObject Hnet sq19 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f60
    sq20 pf27 sq26 pf28
    rfl rfl rfl rfl))

def pf30 : ProofObject Hnet sq32 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf31 : ProofObject Hnet sq31 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq32 pf30 .tt rfl rfl))

def pf32 : ProofObject Hnet sq30 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq31 pf31 f4 rfl rfl))

def pf33 : ProofObject Hnet sq32 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf34 : ProofObject Hnet sq31 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq32 pf33 .tt rfl rfl))

def pf35 : ProofObject Hnet sq34 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq31 pf34 f0 rfl rfl))

def pf36 : ProofObject Hnet sq33 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq34) (regionProof := pf35)
    (termX := (.var 0)) (simplex := sx3) (S := ex3)
    (degree := 5) (polynomial := tm15) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex3) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf37 : ProofObject Hnet sq29 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq30 pf32 sq33 pf36
    1 tm0 (.const 1) f72
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf38 : ProofObject Hnet sq35 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm17
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf39 : ProofObject Hnet sq28 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f69
    sq29 pf37 sq35 pf38
    rfl rfl rfl rfl))

def pf40 : ProofObject Hnet sq41 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf41 : ProofObject Hnet sq40 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq41 pf40 .tt rfl rfl))

def pf42 : ProofObject Hnet sq39 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq40 pf41 f5 rfl rfl))

def pf43 : ProofObject Hnet sq41 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf44 : ProofObject Hnet sq40 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq41 pf43 .tt rfl rfl))

def pf45 : ProofObject Hnet sq43 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq40 pf44 f0 rfl rfl))

def pf46 : ProofObject Hnet sq42 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq43) (regionProof := pf45)
    (termX := (.var 0)) (simplex := sx4) (S := ex4)
    (degree := 5) (polynomial := tm19) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex4) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf47 : ProofObject Hnet sq38 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq39 pf42 sq42 pf46
    1 tm0 (.const 1) f81
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf48 : ProofObject Hnet sq44 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm21
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf49 : ProofObject Hnet sq37 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f78
    sq38 pf47 sq44 pf48
    rfl rfl rfl rfl))

def pf50 : ProofObject Hnet sq50 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf51 : ProofObject Hnet sq49 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq50 pf50 .tt rfl rfl))

def pf52 : ProofObject Hnet sq48 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq49 pf51 f6 rfl rfl))

def pf53 : ProofObject Hnet sq50 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf54 : ProofObject Hnet sq49 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq50 pf53 .tt rfl rfl))

def pf55 : ProofObject Hnet sq52 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq49 pf54 f0 rfl rfl))

def pf56 : ProofObject Hnet sq51 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq52) (regionProof := pf55)
    (termX := (.var 0)) (simplex := sx5) (S := ex5)
    (degree := 5) (polynomial := tm23) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex5) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf57 : ProofObject Hnet sq47 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq48 pf52 sq51 pf56
    1 tm0 (.const 1) f90
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf58 : ProofObject Hnet sq53 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm25
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf59 : ProofObject Hnet sq46 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f87
    sq47 pf57 sq53 pf58
    rfl rfl rfl rfl))

def pf60 : ProofObject Hnet sq59 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf61 : ProofObject Hnet sq58 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq59 pf60 .tt rfl rfl))

def pf62 : ProofObject Hnet sq57 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq58 pf61 f7 rfl rfl))

def pf63 : ProofObject Hnet sq59 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf64 : ProofObject Hnet sq58 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq59 pf63 .tt rfl rfl))

def pf65 : ProofObject Hnet sq61 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq58 pf64 f0 rfl rfl))

def pf66 : ProofObject Hnet sq60 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq61) (regionProof := pf65)
    (termX := (.var 0)) (simplex := sx6) (S := ex6)
    (degree := 5) (polynomial := tm27) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex6) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf67 : ProofObject Hnet sq56 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq57 pf62 sq60 pf66
    1 tm0 (.const 1) f99
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf68 : ProofObject Hnet sq62 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm29
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf69 : ProofObject Hnet sq55 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f96
    sq56 pf67 sq62 pf68
    rfl rfl rfl rfl))

def pf70 : ProofObject Hnet sq68 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf71 : ProofObject Hnet sq67 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq68 pf70 .tt rfl rfl))

def pf72 : ProofObject Hnet sq66 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq67 pf71 f8 rfl rfl))

def pf73 : ProofObject Hnet sq68 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf74 : ProofObject Hnet sq67 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq68 pf73 .tt rfl rfl))

def pf75 : ProofObject Hnet sq70 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq67 pf74 f0 rfl rfl))

def pf76 : ProofObject Hnet sq69 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq70) (regionProof := pf75)
    (termX := (.var 0)) (simplex := sx7) (S := ex7)
    (degree := 5) (polynomial := tm31) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex7) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf77 : ProofObject Hnet sq65 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq66 pf72 sq69 pf76
    1 tm0 (.const 1) f108
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf78 : ProofObject Hnet sq71 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm33
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf79 : ProofObject Hnet sq64 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f105
    sq65 pf77 sq71 pf78
    rfl rfl rfl rfl))

def pf80 : ProofObject Hnet sq77 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf81 : ProofObject Hnet sq76 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq77 pf80 .tt rfl rfl))

def pf82 : ProofObject Hnet sq75 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq76 pf81 f9 rfl rfl))

def pf83 : ProofObject Hnet sq77 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf84 : ProofObject Hnet sq76 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq77 pf83 .tt rfl rfl))

def pf85 : ProofObject Hnet sq79 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq76 pf84 f0 rfl rfl))

def pf86 : ProofObject Hnet sq78 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq79) (regionProof := pf85)
    (termX := (.var 0)) (simplex := sx8) (S := ex8)
    (degree := 5) (polynomial := tm35) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex8) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf87 : ProofObject Hnet sq74 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq75 pf82 sq78 pf86
    1 tm0 (.const 1) f117
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf88 : ProofObject Hnet sq80 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm37
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf89 : ProofObject Hnet sq73 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f114
    sq74 pf87 sq80 pf88
    rfl rfl rfl rfl))

def pf90 : ProofObject Hnet sq86 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf91 : ProofObject Hnet sq85 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq86 pf90 .tt rfl rfl))

def pf92 : ProofObject Hnet sq84 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq85 pf91 f10 rfl rfl))

def pf93 : ProofObject Hnet sq86 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf94 : ProofObject Hnet sq85 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq86 pf93 .tt rfl rfl))

def pf95 : ProofObject Hnet sq88 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq85 pf94 f0 rfl rfl))

def pf96 : ProofObject Hnet sq87 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq88) (regionProof := pf95)
    (termX := (.var 0)) (simplex := sx9) (S := ex9)
    (degree := 5) (polynomial := tm39) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex9) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf97 : ProofObject Hnet sq83 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq84 pf92 sq87 pf96
    1 tm0 (.const 1) f126
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf98 : ProofObject Hnet sq89 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm41
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf99 : ProofObject Hnet sq82 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f123
    sq83 pf97 sq89 pf98
    rfl rfl rfl rfl))

def pf100 : ProofObject Hnet sq95 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf101 : ProofObject Hnet sq94 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq95 pf100 .tt rfl rfl))

def pf102 : ProofObject Hnet sq93 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq94 pf101 f11 rfl rfl))

def pf103 : ProofObject Hnet sq95 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf104 : ProofObject Hnet sq94 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq95 pf103 .tt rfl rfl))

def pf105 : ProofObject Hnet sq97 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq94 pf104 f0 rfl rfl))

def pf106 : ProofObject Hnet sq96 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq97) (regionProof := pf105)
    (termX := (.var 0)) (simplex := sx10) (S := ex10)
    (degree := 5) (polynomial := tm43) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex10) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf107 : ProofObject Hnet sq92 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq93 pf102 sq96 pf106
    1 tm0 (.const 1) f135
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf108 : ProofObject Hnet sq98 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm45
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf109 : ProofObject Hnet sq91 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f132
    sq92 pf107 sq98 pf108
    rfl rfl rfl rfl))

def pf110 : ProofObject Hnet sq104 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf111 : ProofObject Hnet sq103 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq104 pf110 .tt rfl rfl))

def pf112 : ProofObject Hnet sq102 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq103 pf111 f12 rfl rfl))

def pf113 : ProofObject Hnet sq104 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf114 : ProofObject Hnet sq103 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq104 pf113 .tt rfl rfl))

def pf115 : ProofObject Hnet sq106 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq103 pf114 f0 rfl rfl))

def pf116 : ProofObject Hnet sq105 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq106) (regionProof := pf115)
    (termX := (.var 0)) (simplex := sx11) (S := ex11)
    (degree := 5) (polynomial := tm47) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex11) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf117 : ProofObject Hnet sq101 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq102 pf112 sq105 pf116
    1 tm0 (.const 1) f144
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf118 : ProofObject Hnet sq107 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm49
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf119 : ProofObject Hnet sq100 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f141
    sq101 pf117 sq107 pf118
    rfl rfl rfl rfl))

def pf120 : ProofObject Hnet sq113 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf121 : ProofObject Hnet sq112 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq113 pf120 .tt rfl rfl))

def pf122 : ProofObject Hnet sq111 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq112 pf121 f13 rfl rfl))

def pf123 : ProofObject Hnet sq113 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf124 : ProofObject Hnet sq112 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq113 pf123 .tt rfl rfl))

def pf125 : ProofObject Hnet sq115 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq112 pf124 f0 rfl rfl))

def pf126 : ProofObject Hnet sq114 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq115) (regionProof := pf125)
    (termX := (.var 0)) (simplex := sx12) (S := ex12)
    (degree := 5) (polynomial := tm51) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex12) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf127 : ProofObject Hnet sq110 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq111 pf122 sq114 pf126
    1 tm0 (.const 1) f153
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf128 : ProofObject Hnet sq116 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm53
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf129 : ProofObject Hnet sq109 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f150
    sq110 pf127 sq116 pf128
    rfl rfl rfl rfl))

def pf130 : ProofObject Hnet sq122 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf131 : ProofObject Hnet sq121 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq122 pf130 .tt rfl rfl))

def pf132 : ProofObject Hnet sq120 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq121 pf131 f14 rfl rfl))

def pf133 : ProofObject Hnet sq122 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf134 : ProofObject Hnet sq121 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq122 pf133 .tt rfl rfl))

def pf135 : ProofObject Hnet sq124 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq121 pf134 f0 rfl rfl))

def pf136 : ProofObject Hnet sq123 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq124) (regionProof := pf135)
    (termX := (.var 0)) (simplex := sx13) (S := ex13)
    (degree := 5) (polynomial := tm55) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex13) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf137 : ProofObject Hnet sq119 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq120 pf132 sq123 pf136
    1 tm0 (.const 1) f162
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf138 : ProofObject Hnet sq125 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm57
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf139 : ProofObject Hnet sq118 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f159
    sq119 pf137 sq125 pf138
    rfl rfl rfl rfl))

def pf140 : ProofObject Hnet sq131 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf141 : ProofObject Hnet sq130 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq131 pf140 .tt rfl rfl))

def pf142 : ProofObject Hnet sq129 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq130 pf141 f15 rfl rfl))

def pf143 : ProofObject Hnet sq131 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf144 : ProofObject Hnet sq130 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq131 pf143 .tt rfl rfl))

def pf145 : ProofObject Hnet sq133 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq130 pf144 f0 rfl rfl))

def pf146 : ProofObject Hnet sq132 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq133) (regionProof := pf145)
    (termX := (.var 0)) (simplex := sx14) (S := ex14)
    (degree := 5) (polynomial := tm59) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex14) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf147 : ProofObject Hnet sq128 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq129 pf142 sq132 pf146
    1 tm0 (.const 1) f171
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf148 : ProofObject Hnet sq134 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm61
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf149 : ProofObject Hnet sq127 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f168
    sq128 pf147 sq134 pf148
    rfl rfl rfl rfl))

def pf150 : ProofObject Hnet sq140 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf151 : ProofObject Hnet sq139 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq140 pf150 .tt rfl rfl))

def pf152 : ProofObject Hnet sq138 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq139 pf151 f16 rfl rfl))

def pf153 : ProofObject Hnet sq140 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf154 : ProofObject Hnet sq139 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq140 pf153 .tt rfl rfl))

def pf155 : ProofObject Hnet sq142 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq139 pf154 f0 rfl rfl))

def pf156 : ProofObject Hnet sq141 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq142) (regionProof := pf155)
    (termX := (.var 0)) (simplex := sx15) (S := ex15)
    (degree := 5) (polynomial := tm63) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex15) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf157 : ProofObject Hnet sq137 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq138 pf152 sq141 pf156
    1 tm0 (.const 1) f180
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf158 : ProofObject Hnet sq143 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm65
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf159 : ProofObject Hnet sq136 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f177
    sq137 pf157 sq143 pf158
    rfl rfl rfl rfl))

def pf160 : ProofObject Hnet sq149 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf161 : ProofObject Hnet sq148 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq149 pf160 .tt rfl rfl))

def pf162 : ProofObject Hnet sq147 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq148 pf161 f17 rfl rfl))

def pf163 : ProofObject Hnet sq149 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf164 : ProofObject Hnet sq148 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq149 pf163 .tt rfl rfl))

def pf165 : ProofObject Hnet sq151 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq148 pf164 f0 rfl rfl))

def pf166 : ProofObject Hnet sq150 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq151) (regionProof := pf165)
    (termX := (.var 0)) (simplex := sx16) (S := ex16)
    (degree := 5) (polynomial := tm67) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex16) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf167 : ProofObject Hnet sq146 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq147 pf162 sq150 pf166
    1 tm0 (.const 1) f189
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf168 : ProofObject Hnet sq152 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm69
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf169 : ProofObject Hnet sq145 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f186
    sq146 pf167 sq152 pf168
    rfl rfl rfl rfl))

def pf170 : ProofObject Hnet sq157 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf171 : ProofObject Hnet sq156 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq157 pf170 .tt rfl rfl))

def pf172 : ProofObject Hnet sq155 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq156 pf171 f18 rfl rfl))

def pf173 : ProofObject Hnet sq157 :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pf174 : ProofObject Hnet sq156 :=
  .mk _ _ .andE (.andE _ _ (.left _ _ sq157 pf173 .tt rfl rfl))

def pf175 : ProofObject Hnet sq159 :=
  .mk _ _ .andE (.andE _ _ (.right _ _ sq156 pf174 f0 rfl rfl))

def pf176 : ProofObject Hnet sq158 :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := sq159) (regionProof := pf175)
    (termX := (.var 0)) (simplex := sx17) (S := ex17)
    (degree := 5) (polynomial := tm71) (predicate := f44)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide +kernel⟩)
    (predShape := ⟨fun hne => absurd (by decide +kernel : isExtensionSetEmpty ex17) hne,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def pf177 : ProofObject Hnet sq154 :=
  .mk _ _ .eqElim (.eqElim _ _ (.mk _ _
    sq155 pf172 sq158 pf176
    1 tm0 (.const 1) f196
    rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)))

def pf178 : ProofObject Hnet sq160 :=
  .mk _ _ .farkas (.farkas _ _ (.mk _ _
    tm73
    tm1
    263
    ⟨[], by decide +kernel⟩
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

def pf179 : ProofObject Hnet sq153 :=
  .mk _ _ .cut (.cut _ _ (.mk _ _ f193
    sq154 pf177 sq160 pf178
    rfl rfl rfl rfl))

theorem v0 : (sq145).semanticallyValid Hnet := (pf169).sound

theorem v1 : (sq153).semanticallyValid Hnet := (pf179).sound

def st0 : OrECtxStep where
  seq := sq144
  leftPremise := sq145
  rightPremise := sq153
  path := .left (.right (.here))
  d₁ := f17
  d₂ := f18
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v2 : (sq144).semanticallyValid Hnet :=
  sound_orECtx st0 v0 v1

theorem v3 : (sq136).semanticallyValid Hnet := (pf159).sound

def st1 : OrECtxStep where
  seq := sq135
  leftPremise := sq136
  rightPremise := sq144
  path := .left (.right (.here))
  d₁ := f16
  d₂ := f19
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v4 : (sq135).semanticallyValid Hnet :=
  sound_orECtx st1 v3 v2

theorem v5 : (sq127).semanticallyValid Hnet := (pf149).sound

def st2 : OrECtxStep where
  seq := sq126
  leftPremise := sq127
  rightPremise := sq135
  path := .left (.right (.here))
  d₁ := f15
  d₂ := f20
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v6 : (sq126).semanticallyValid Hnet :=
  sound_orECtx st2 v5 v4

theorem v7 : (sq118).semanticallyValid Hnet := (pf139).sound

def st3 : OrECtxStep where
  seq := sq117
  leftPremise := sq118
  rightPremise := sq126
  path := .left (.right (.here))
  d₁ := f14
  d₂ := f21
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v8 : (sq117).semanticallyValid Hnet :=
  sound_orECtx st3 v7 v6

theorem v9 : (sq109).semanticallyValid Hnet := (pf129).sound

def st4 : OrECtxStep where
  seq := sq108
  leftPremise := sq109
  rightPremise := sq117
  path := .left (.right (.here))
  d₁ := f13
  d₂ := f22
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v10 : (sq108).semanticallyValid Hnet :=
  sound_orECtx st4 v9 v8

theorem v11 : (sq100).semanticallyValid Hnet := (pf119).sound

def st5 : OrECtxStep where
  seq := sq99
  leftPremise := sq100
  rightPremise := sq108
  path := .left (.right (.here))
  d₁ := f12
  d₂ := f23
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v12 : (sq99).semanticallyValid Hnet :=
  sound_orECtx st5 v11 v10

theorem v13 : (sq91).semanticallyValid Hnet := (pf109).sound

def st6 : OrECtxStep where
  seq := sq90
  leftPremise := sq91
  rightPremise := sq99
  path := .left (.right (.here))
  d₁ := f11
  d₂ := f24
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v14 : (sq90).semanticallyValid Hnet :=
  sound_orECtx st6 v13 v12

theorem v15 : (sq82).semanticallyValid Hnet := (pf99).sound

def st7 : OrECtxStep where
  seq := sq81
  leftPremise := sq82
  rightPremise := sq90
  path := .left (.right (.here))
  d₁ := f10
  d₂ := f25
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v16 : (sq81).semanticallyValid Hnet :=
  sound_orECtx st7 v15 v14

theorem v17 : (sq73).semanticallyValid Hnet := (pf89).sound

def st8 : OrECtxStep where
  seq := sq72
  leftPremise := sq73
  rightPremise := sq81
  path := .left (.right (.here))
  d₁ := f9
  d₂ := f26
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v18 : (sq72).semanticallyValid Hnet :=
  sound_orECtx st8 v17 v16

theorem v19 : (sq64).semanticallyValid Hnet := (pf79).sound

def st9 : OrECtxStep where
  seq := sq63
  leftPremise := sq64
  rightPremise := sq72
  path := .left (.right (.here))
  d₁ := f8
  d₂ := f27
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v20 : (sq63).semanticallyValid Hnet :=
  sound_orECtx st9 v19 v18

theorem v21 : (sq55).semanticallyValid Hnet := (pf69).sound

def st10 : OrECtxStep where
  seq := sq54
  leftPremise := sq55
  rightPremise := sq63
  path := .left (.right (.here))
  d₁ := f7
  d₂ := f28
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v22 : (sq54).semanticallyValid Hnet :=
  sound_orECtx st10 v21 v20

theorem v23 : (sq46).semanticallyValid Hnet := (pf59).sound

def st11 : OrECtxStep where
  seq := sq45
  leftPremise := sq46
  rightPremise := sq54
  path := .left (.right (.here))
  d₁ := f6
  d₂ := f29
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v24 : (sq45).semanticallyValid Hnet :=
  sound_orECtx st11 v23 v22

theorem v25 : (sq37).semanticallyValid Hnet := (pf49).sound

def st12 : OrECtxStep where
  seq := sq36
  leftPremise := sq37
  rightPremise := sq45
  path := .left (.right (.here))
  d₁ := f5
  d₂ := f30
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v26 : (sq36).semanticallyValid Hnet :=
  sound_orECtx st12 v25 v24

theorem v27 : (sq28).semanticallyValid Hnet := (pf39).sound

def st13 : OrECtxStep where
  seq := sq27
  leftPremise := sq28
  rightPremise := sq36
  path := .left (.right (.here))
  d₁ := f4
  d₂ := f31
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v28 : (sq27).semanticallyValid Hnet :=
  sound_orECtx st13 v27 v26

theorem v29 : (sq19).semanticallyValid Hnet := (pf29).sound

def st14 : OrECtxStep where
  seq := sq18
  leftPremise := sq19
  rightPremise := sq27
  path := .left (.right (.here))
  d₁ := f3
  d₂ := f32
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v30 : (sq18).semanticallyValid Hnet :=
  sound_orECtx st14 v29 v28

theorem v31 : (sq10).semanticallyValid Hnet := (pf19).sound

def st15 : OrECtxStep where
  seq := sq9
  leftPremise := sq10
  rightPremise := sq18
  path := .left (.right (.here))
  d₁ := f2
  d₂ := f33
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v32 : (sq9).semanticallyValid Hnet :=
  sound_orECtx st15 v31 v30

theorem v33 : (sq1).semanticallyValid Hnet := (pf9).sound

def st16 : OrECtxStep where
  seq := sq0
  leftPremise := sq1
  rightPremise := sq9
  path := .left (.right (.here))
  d₁ := f1
  d₂ := f34
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

theorem v34 : (sq0).semanticallyValid Hnet :=
  sound_orECtx st16 v33 v32

theorem CartpoleCoreDecrease_valid : (sq0).semanticallyValid Hnet := v34

#print axioms CartpoleCoreDecrease_valid

end PPLC.Handshake.CartpoleCoreDecrease
