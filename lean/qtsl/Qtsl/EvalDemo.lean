import Qtsl.Core.DemoData
import Qtsl.Catalogue
import Qtsl.Decide

/-!
# Worked-example receipts

Elaboration-time receipts for the worked-example certificate whose
value-level data lives in `Qtsl.Core.DemoData`: the `#eval`
mutant battery, the sign-direction witness, `#print axioms` gates, and
the well-typedness example. The `checker_core` executable re-runs the
same battery through the compiled code path at runtime — one battery,
several execution paths.
-/

namespace PPLC
namespace EvalDemo

example : check demoCert.proof = true := rfl

#eval QArith.fdBernstein [[1], [2]] [false, false] 1
  ((Term.asCoordPoly? polyB).getD [])

#eval bernConeCoeffCheck simplexB Sempty 1 polyB predP1

#eval bernConeCoeffCheck simplexB Sempty 1
  (.add (.const (-5)) (.mul (.const 2) w0)) predP1

#eval bernConeCoeffCheck simplexB Sempty 1
  (.add (.const (1/2)) (.mul (.const (-2)) w0)) predP1

#eval bernConeCoeffCheck simplexB Sempty 1 (.mul w0 w0) predP1

#eval decide (isConvexPredicate
  (.or (.atom .ge (.var predicateHole) (.const 1))
       (.atom .le (.var predicateHole) (.const 0))))

#eval bernConeCoeffCheck simplexPt SemptyPt 1 polyB predP1

#eval QArith.fdBernstein [[1], [2]] [true, false] 1 (QArith.Poly.var 0)

#eval QArith.starIdentityCheck [[1], [2]] [true, false] 2
  (QArith.Poly.add
    (QArith.Poly.scale 3 (QArith.Poly.mul (QArith.Poly.var 0) (QArith.Poly.var 0)))
    (QArith.Poly.add (QArith.Poly.scale (-1) (QArith.Poly.var 0))
      (QArith.Poly.const (1/7)))) [3] [1]

#eval decide (barycentricHalfspaceForm w0 simplexB Sempty
  (.and (.atom .le (.add (.mul (.const 1) w0) (.const (-2))) (.const 0))
        (.atom .le (.add (.mul (.const (-1)) w0) (.const 1)) (.const 0))))

#eval farkasCheck
  (.add (.mul (.const 1) (.sub w0 (.const 2))) (.const 0))
  (.atom .le w0 (.const 2))
  (.sub w0 (.const 2))

#eval decide (polynomialCanonicalEq (.add w0 w0) (.mul (.const 2) w0))

#eval decide (polynomialCanonicalEq (.mul (.const 2) w0) w0)

#eval farkasCheck
  (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
  (.atom .le (.idx (.var 3) 0) (.var 4))
  (.sub (.idx (.var 3) 0) (.var 4))
#eval farkasCheckCore
  (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
  (.atom .le (.idx (.var 3) 0) (.var 4))
  (.sub (.idx (.var 3) 0) (.var 4))
#eval farkasCheckW
  (.add (.mul (.const 1) (.sub (.idx (.var 3) 0) (.var 4))) (.const 0))
  (.atom .le (.idx (.var 3) 0) (.var 4))
  (.sub (.idx (.var 3) 0) (.var 4))

#eval farkasCheck
  (.add (.mul (.const 1) (.idx (.var 3) 0)) (.const 0))
  (.atom .le (.idx (.var 3) 0) (.const 0))
  (.var 3)

#eval syzygyCheck
  (.add (.mul (.const 1) (.sub (.idx (.var 3) 1) (.var 4))) (.const 0))
  [⟨.tt, .atom .le (.sub (.idx (.var 3) 1) (.var 4)) (.const 0)⟩]
  .tt
  (.sub (.idx (.var 3) 1) (.var 4))

#print axioms Term.asCoordPolyMixed?
#print axioms farkasCheckM
#print axioms syzygyCheckM

#print axioms bernConeCoeffCheck
#print axioms QArith.fdBernstein
#print axioms farkasCheck
#print axioms barycentricHalfspaceBuild
#print axioms Hypernet.spConjunction

#print axioms demoCert

example : regionB.WellTyped H0 := by decide +kernel

/-! ### Cell-schema conclusion-form receipts

Elaboration-time witnesses for the four cell-schema forms over a
cell-bearing variant of the worked geometry (vertices at 1 and 2, one
cell over the full simplex, empty extension) — the strict-interior
conjunction carries the RAW `baryLambdas1D` terms (constant on the
left of the sum, no rescale, no zero-offset special case), the
indicator forms chain by `Formula.chainAnd`, and the out-witness atom
reverses the strict-interior signs. Each negative example pins a
rendering the forms must reject — including the positive
primitive-integer rescale that `barycentricHalfspaceForm` would
require, which these forms must NOT accept where it differs from the
raw coefficients. -/

def cxCell : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 1 else 2
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := [(fun _ => true, fun _ => false)]
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide
  cellsWF := by decide

def kCell : Fin cxCell.cells.length := ⟨0, by decide⟩

-- Strict interior: λ₀ = 2 + (−1)·x > 0 AND λ₁ = −1 + 1·x > 0.
example : cellStrictInteriorForm cxCell w0 kCell
    (.and (.atom .gt (.add (.const 2) (.mul (.const (-1)) w0)) (.const 0))
          (.atom .gt (.add (.const (-1)) (.mul (.const 1) w0)) (.const 0))) := by
  decide +kernel

-- One-hot on the single-cell schema: (b₀ = 1) AND FTrue…
example : cellOneHotForm cxCell [5] kCell
    (.and (.atom .eq (.var 5) (.const 1)) .tt) := by decide +kernel

-- …and the bare atom (no FTrue arm) is NOT the form.
example : ¬ cellOneHotForm cxCell [5] kCell
    (.atom .eq (.var 5) (.const 1)) := by decide +kernel

-- Out-witness at core vertex 0: the single REVERSED atom λ₀ < 0.
example : cellOutWitnessForm cxCell w0 kCell ⟨0, by decide⟩
    (.atom .lt (.add (.const 2) (.mul (.const (-1)) w0)) (.const 0)) := by
  decide +kernel

-- Out-zero: the single atom (b₀ = 0).
example : cellOutZeroForm cxCell [5] kCell
    (.atom .eq (.var 5) (.const 0)) := by decide +kernel

/-- The left-half geometry (vertices at 1 and 3/2) with one cell:
λ₁ = −2 + 2·x, whose coefficients are NOT coprime — the receipt pair
below separates the raw rendering (accepted) from the positive
primitive-integer rescale −1 + 1·x (rejected). -/
def cxLCell : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 1 else 3/2
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := [(fun _ => true, fun _ => false)]
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

def kLCell : Fin cxLCell.cells.length := ⟨0, by decide⟩

example : cellStrictInteriorForm cxLCell w0 kLCell
    (.and (.atom .gt (.add (.const 3) (.mul (.const (-2)) w0)) (.const 0))
          (.atom .gt (.add (.const (-2)) (.mul (.const 2) w0)) (.const 0))) := by
  decide +kernel

example : ¬ cellStrictInteriorForm cxLCell w0 kLCell
    (.and (.atom .gt (.add (.const 3) (.mul (.const (-2)) w0)) (.const 0))
          (.atom .gt (.add (.const (-1)) (.mul (.const 1) w0)) (.const 0))) := by
  decide +kernel

#print axioms cellStrictInteriorBuild
#print axioms cellOneHotBuild
#print axioms cellOutWitnessBuild
#print axioms cellOutZeroBuild

#eval coverCheck simplexB Sempty 2 subBranchSimplex subBranchS
example : coverCheck simplexB Sempty 2 subBranchSimplex subBranchS
    = true := by decide +kernel

#eval coverCheck simplexB Sempty 2
  (fun k => if k.val = 0 then simplexG else simplexR)
  (fun k => if k.val = 0 then SemptyG else SemptyR)
example : coverCheck simplexB Sempty 2
    (fun k => if k.val = 0 then simplexG else simplexR)
    (fun k => if k.val = 0 then SemptyG else SemptyR)
    = false := by decide +kernel

#eval coverCheck simplexB Sempty 1
  (fun _ => simplexPt) (fun _ => SemptyPt)
example : coverCheck simplexB Sempty 1
    (fun _ => simplexPt) (fun _ => SemptyPt)
    = false := by decide +kernel

#eval coverCheck simplexB SextB 2 subBranchSimplex subBranchS
example : coverCheck simplexB SextB 2 subBranchSimplex subBranchS
    = false := by decide +kernel

#eval coverCheck simplexB Sempty 2
  (fun k => if k.val = 0 then simplexR else simplexL) subBranchS
example : coverCheck simplexB Sempty 2
    (fun k => if k.val = 0 then simplexR else simplexL) subBranchS
    = false := by decide +kernel

example : check pfSubdivide = true := rfl

#print axioms pfSubdivide

#eval decide (reluLinked HR 0 1)
example : reluLinked HR 0 1 := by decide +kernel

#eval decide (reluLinked HR 1 0)
example : ¬ reluLinked HR 1 0 := by decide +kernel

#eval decide (reluLinked HR0 0 1)
example : ¬ reluLinked HR0 0 1 := by decide +kernel

#eval decide ((0 : ℚ) ≤ (1/2) * (-1) + (-1/2))
example : ¬ ((0 : ℚ) ≤ (1/2) * (-1) + (-1/2)) := by decide +kernel

example : (PrimApp.relu [1] 0 1).spFact ≠ .tt := by decide
example : (PrimApp.relu [0] 0 1).spFact = .tt := rfl
example : (PrimApp.relu [2] 0 1).spFact = .tt := rfl

example : check pfReluNN = true := rfl
example : check pfReluAbove = true := rfl
example : check pfReluPos = true := rfl
example : check pfReluNeg = true := rfl
example : check pfLirpa = true := rfl
example : check pfLayer = true := rfl

example : (PrimApp.stack 2 [] [2, 3] 4).spFact ≠ .tt := by decide
example : (PrimApp.stack 2 [1] [2, 3] 4).spFact = .tt := rfl

#print axioms pfLirpa
#print axioms pfLayer

/-!
## Predicate-class receipts

The three semantic-class side conditions (`isConicPredicate`,
`isConvexPredicate`, `isUpwardClosedConicPredicate`) read off the total
`classifyPred` recognizer. These receipts pin the fragment-boundary
rows the ground evaluators transcribe: literal-only coefficients,
structural `evalQ?` folding (`0 * w` does not fold), re-oriented
constant-left atoms, the convex/conic split, and the closed-world
non-atoms (`.tt` is not a convex predicate).
-/

example : isConicPredicate (.atom .ge (.var predicateHole) (.const 0)) := by decide
example : isUpwardClosedConicPredicate (.atom .ge (.var predicateHole) (.const 0)) := by
  decide

example : isConicPredicate
    (.atom .le (.mul (.const 3) (.var predicateHole)) (.const 0)) := by decide
example : ¬ isUpwardClosedConicPredicate
    (.atom .le (.var predicateHole) (.const 0)) := by decide

-- Re-orientation: a constant-left atom flips the bowtie.
example : isUpwardClosedConicPredicate
    (.atom .le (.const 0) (.var predicateHole)) := by decide

-- The convex/conic split: a shifted halfline is convex, not conic.
example : isConvexPredicate (.atom .ge (.var predicateHole) (.const 1)) := by decide
example : ¬ isConicPredicate (.atom .ge (.var predicateHole) (.const 1)) := by decide

-- `evalQ?` folds the comparison side structurally… (`.neg (.const 0)`
-- rather than `.sub (.const 1) (.const 1)`: `Rat.sub`'s normalization
-- does not kernel-reduce under `decide`; the subtraction row lives in
-- the ground evaluator's battery and corpus instead.)
example : isConicPredicate
    (.atom .ge (.var predicateHole) (.neg (.const 0))) := by decide
-- …but never through a wire: `0 * w` is not a constant to `evalQ?`.
example : ¬ isConvexPredicate
    (.atom .ge (.var predicateHole) (.mul (.const 0) (.var 7))) := by decide

-- The scaling coefficient is an immediate literal, strictly positive.
example : ¬ isConvexPredicate
    (.atom .ge (.mul (.add (.const 1) (.const 1)) (.var predicateHole))
      (.const 0)) := by decide
example : ¬ isConvexPredicate
    (.atom .ge (.mul (.const 0) (.var predicateHole)) (.const 0)) := by decide

-- Conjunctions combine both class bits.
example : isConicPredicate
    (.and (.atom .ge (.var predicateHole) (.const 0))
      (.atom .le (.var predicateHole) (.const 0))) := by decide
example : ¬ isUpwardClosedConicPredicate
    (.and (.atom .ge (.var predicateHole) (.const 0))
      (.atom .le (.var predicateHole) (.const 0))) := by decide

-- The closed world: `.tt` and off-origin equalities classify as
-- nothing.
example : ¬ isConvexPredicate .tt := by decide
example : ¬ isConvexPredicate (.atom .eq (.var predicateHole) (.const 5)) := by
  decide

end EvalDemo
end PPLC
