import Qtsl.QArith

/-!
# Adversarial probes for the star identity

Each probe evaluates `starIdentityCheck` on a valid instance
(hypotheses of the statement satisfied); the identity as stated
predicts `some true` on all of them. Falsification probes violate one
hypothesis each, confirming every hypothesis is load-bearing.
-/

open PPLC.QArith

def mkP (ts : List (Mono × Rat)) : Poly := Poly.canon ts

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(0,1),(1,1)],1), ([(1,1)],-2), ([],3)])
  [1/2] [1/3, 2/3]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(0,1),(1,1)],1), ([(1,1)],-2), ([],3)])
  [-2/3] [1/3, 2/3]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(0,1),(1,1)],1), ([(1,1)],-2), ([],3)])
  [1/2] [3/2, -1/2]

#eval starIdentityCheck [[0,0],[1,0],[0,1],[1,1]] [true,true,false,false] 2
  (mkP [([(0,2)],1), ([(0,1),(1,1)],-3), ([(1,2)],2), ([(0,1)],1), ([],-1)])
  [1/2, -1/3] [1/4, 3/4]

#eval starIdentityCheck [[0],[2],[5]] [true,true,false] 3
  (mkP [([(0,3)],1), ([(0,1)],-2), ([],1)])
  [1/2, 1/3] [1]

#eval starIdentityCheck [[1,1],[0,0],[2,-1],[0,1]] [false,true,true,false] 2
  (mkP [([(0,1),(1,1)],1), ([(1,2)],1), ([(0,1)],-1)])
  [1/3, 1/5] [7/2, -5/2]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 0
  (mkP [([],7)]) [4/7] [1/3, 2/3]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,true,false] 2
  ([] : Poly) [1/2, 1/3] [1]

#eval starIdentityCheck [[0,0],[1],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(1,1)],-2)]) [1/2] [1/3, 2/3]

#eval starIdentityCheck [[0],[2],[5]] [true,true,false] 4
  (mkP [([(0,1)],1), ([],1)]) [-1/2, 1/3] [1]

#eval starIdentityCheck [[0,0],[1,0],[0,1],[1,1]] [true,true,false,false] 2
  (mkP [([(0,2)],1), ([(1,1)],1)]) [0, 0] [2/5, 3/5]

#eval starIdentityCheck [[0,0],[1,0],[0,1],[1,1]] [false,true,false,true] 4
  (mkP [([(0,2),(1,2)],1), ([(0,3)],-1), ([(1,1)],1), ([],2)])
  [-1/2, 1/7] [5/3, -2/3]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(1,1)],-2)]) [1/2] [2/3, 4/3]

#eval starIdentityCheck [[0,0],[1,0],[0,1]] [true,false,false] 2
  (mkP [([(0,2)],1), ([(1,1)],-2)]) [1/2] [1/2, -1/2]

#eval starIdentityCheck [[0],[2],[5]] [true,true,false] 2
  (mkP [([(0,3)],1)]) [1/2, 1/3] [1]
