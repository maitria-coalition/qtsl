import Qtsl.Core.DemoData

/-!
# Executable checker entry point

Entry point of the `checker_core` executable, which links only the
mathlib-free core closure. At runtime it re-executes the worked-example
receipt suite through the compiled code path and prints a verdict
table; the same checks run at elaboration time on the kernel path, so
any divergence between the two is a comparator finding.
-/

open PPLC PPLC.EvalDemo

def checkLine (name : String) (got expected : Bool) : IO Bool := do
  let ok := got == expected
  IO.println s!"{if ok then "PASS" else "FAIL"}  {name}: got {got}, expected {expected}"
  pure ok

def main : IO UInt32 := do
  IO.println "== Qtsl checker core (P1 compiled path) =="
  let mut allOk := true

  allOk := (← checkLine "check demoCert.proof" (check demoCert.proof) true) && allOk

  match QArith.fdBernstein [[1], [2]] [false, false] 1
      ((Term.asCoordPoly? polyB).getD []) with
  | some t =>
      IO.println s!"fdBernstein table: {reprStr t}"
  | none =>
      allOk := false
      IO.println "FAIL  fdBernstein: none (expected a table)"

  allOk := (← checkLine "bernConeCoeffCheck (branch B)"
    (bernConeCoeffCheck simplexB Sempty 1 polyB predP1) true) && allOk

  allOk := (← checkLine "mutant goal_tightened_minus5"
    (bernConeCoeffCheck simplexB Sempty 1
      (.add (.const (-5)) (.mul (.const 2) w0)) predP1) false) && allOk
  allOk := (← checkLine "mutant wrong_dynamics_sign"
    (bernConeCoeffCheck simplexB Sempty 1
      (.add (.const (1/2)) (.mul (.const (-2)) w0)) predP1) false) && allOk
  allOk := (← checkLine "mutant degree_lie_off_by_one"
    (bernConeCoeffCheck simplexB Sempty 1 (.mul w0 w0) predP1) false) && allOk
  allOk := (← checkLine "mutant nonconvex_predicate"
    (decide (isConvexPredicate
      (.or (.atom .ge (.var predicateHole) (.const 1))
           (.atom .le (.var predicateHole) (.const 0))))) false) && allOk
  allOk := (← checkLine "mutant corrupted-simplex (sub-dimensional)"
    (bernConeCoeffCheck simplexPt SemptyPt 1 polyB predP1) false) && allOk

  match QArith.fdBernstein [[1], [2]] [true, false] 1 (QArith.Poly.var 0) with
  | some t => IO.println s!"fdBernstein |S|=1 table: {reprStr t}"
  | none =>
      allOk := false
      IO.println "FAIL  fdBernstein |S|=1: none (expected a table)"
  allOk := (← checkLine "starIdentityCheck (facet-extended, exact)"
    ((QArith.starIdentityCheck [[1], [2]] [true, false] 2
      (QArith.Poly.add
        (QArith.Poly.scale 3 (QArith.Poly.mul (QArith.Poly.var 0) (QArith.Poly.var 0)))
        (QArith.Poly.add (QArith.Poly.scale (-1) (QArith.Poly.var 0))
          (QArith.Poly.const (1/7)))) [3] [1]).getD false) true) && allOk

  allOk := (← checkLine "barycentricHalfspaceForm (canonical conjunction)"
    (decide (barycentricHalfspaceForm w0 simplexB Sempty
      (.and (.atom .le (.add (.mul (.const 1) w0) (.const (-2))) (.const 0))
            (.atom .le (.add (.mul (.const (-1)) w0) (.const 1)) (.const 0)))))
    true) && allOk
  allOk := (← checkLine "farkasCheck (λ = 1 re-canonicalization)"
    (farkasCheck
      (.add (.mul (.const 1) (.sub w0 (.const 2))) (.const 0))
      (.atom .le w0 (.const 2))
      (.sub w0 (.const 2))) true) && allOk

  allOk := (← checkLine "farkasCheck mixed (TIdx + bare wire, λ = 1)"
    (farkasCheck
      (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
      (.atom .le (.idx (.var 3) 0) (.var 4))
      (.sub (.idx (.var 3) 0) (.var 4))) true) && allOk
  allOk := (← checkLine "farkasCheckCore rejects mixed (differential)"
    (farkasCheckCore
      (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
      (.atom .le (.idx (.var 3) 0) (.var 4))
      (.sub (.idx (.var 3) 0) (.var 4))) false) && allOk
  allOk := (← checkLine "farkasCheckW rejects mixed (differential)"
    (farkasCheckW
      (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
      (.atom .le (.idx (.var 3) 0) (.var 4))
      (.sub (.idx (.var 3) 0) (.var 4))) false) && allOk
  allOk := (← checkLine "farkasCheck refuses bare-w ≡ w[0] aliasing"
    (farkasCheck
      (.add (.mul (.const 1) (.idx (.var 3) 0)) (.const 0))
      (.atom .le (.idx (.var 3) 0) (.const 0))
      (.var 3)) false) && allOk
  allOk := (← checkLine "syzygyCheck mixed component entry"
    (syzygyCheck
      (.add (.mul (.const 1) (.sub (.idx (.var 3) 1) (.var 4))) (.const 0))
      [⟨.tt, .atom .le (.sub (.idx (.var 3) 1) (.var 4)) (.const 0)⟩]
      .tt
      (.sub (.idx (.var 3) 1) (.var 4))) true) && allOk
  allOk := (← checkLine "polynomialCanonicalEq (w₀+w₀ ≡ 2·w₀)"
    (decide (polynomialCanonicalEq (.add w0 w0) (.mul (.const 2) w0))) true) && allOk
  allOk := (← checkLine "polynomialCanonicalEq scale-preserving (F7)"
    (decide (polynomialCanonicalEq (.mul (.const 2) w0) w0)) false) && allOk

  allOk := (← checkLine "coverCheck [1,3/2]∪[3/2,2] over [1,2]"
    (coverCheck simplexB Sempty 2 subBranchSimplex subBranchS) true) && allOk
  allOk := (← checkLine "coverCheck mutant gap (4/3, 3/2)"
    (coverCheck simplexB Sempty 2
      (fun k => if k.val = 0 then simplexG else simplexR)
      (fun k => if k.val = 0 then SemptyG else SemptyR)) false) && allOk
  allOk := (← checkLine "coverCheck mutant point-supported branch"
    (coverCheck simplexB Sempty 1
      (fun _ => simplexPt) (fun _ => SemptyPt)) false) && allOk
  allOk := (← checkLine "coverCheck mutant ray parent (S ≠ ∅)"
    (coverCheck simplexB SextB 2 subBranchSimplex subBranchS) false) && allOk
  allOk := (← checkLine "coverCheck mutant untied branch simplices"
    (coverCheck simplexB Sempty 2
      (fun k => if k.val = 0 then simplexR else simplexL)
      subBranchS) false) && allOk
  allOk := (← checkLine "check pfSubdivide"
    (check pfSubdivide) true) && allOk

  allOk := (← checkLine "reluLinked HR (0,1)"
    (decide (reluLinked HR 0 1)) true) && allOk
  allOk := (← checkLine "reluLinked mutant reversed ports (1,0)"
    (decide (reluLinked HR 1 0)) false) && allOk
  allOk := (← checkLine "reluLinked mutant shape-[0] node"
    (decide (reluLinked HR0 0 1)) false) && allOk
  allOk := (← checkLine "relu spFact emitted at [1]"
    (decide ((PrimApp.relu [1] 0 1).spFact ≠ .tt)) true) && allOk
  allOk := (← checkLine "relu spFact withheld at [0]"
    (decide ((PrimApp.relu [0] 0 1).spFact = .tt)) true) && allOk
  allOk := (← checkLine "relu spFact withheld at [2]"
    (decide ((PrimApp.relu [2] 0 1).spFact = .tt)) true) && allOk
  allOk := (← checkLine "LiRPA mutant envelope (γ,δ)=(1/2,-1/2) fails hUpper1"
    (decide ((0 : Rat) ≤ (1/2) * (-1) + (-1/2))) false) && allOk
  allOk := (← checkLine "check pfLirpa"
    (check pfLirpa) true) && allOk
  allOk := (← checkLine "check pfReluPos"
    (check pfReluPos) true) && allOk

  allOk := (← checkLine "stack spFact emitted at scalar inputs"
    (decide ((PrimApp.stack 2 [] [2, 3] 4).spFact ≠ .tt)) true) && allOk
  allOk := (← checkLine "stack spFact withheld at rank-1 inputs"
    (decide ((PrimApp.stack 2 [1] [2, 3] 4).spFact = .tt)) true) && allOk
  allOk := (← checkLine "check pfLayer (2-neuron fragment)"
    (check pfLayer) true) && allOk

  allOk := (← checkLine "f64.rdn(1/3) = 6004799503160661/2^54"
    (decide (FloatFmt.f64.rdn (1/3) = 6004799503160661 / 2 ^ 54)) true) && allOk
  allOk := (← checkLine "f64.rne(1/10) rounds up"
    (decide (FloatFmt.f64.rne (1/10) = 7205759403792794 / 2 ^ 56)) true) && allOk
  allOk := (← checkLine "roundE ext saturation (+∞ at 2^2000, rup)"
    (decide (Dtype.F64.roundE .rup (2 ^ 2000) = ERat.posInf)) true) && allOk
  IO.println (if allOk then "== ALL CHECKS PASS ==" else "== FAILURES PRESENT ==")
  pure (if allOk then 0 else 1)
