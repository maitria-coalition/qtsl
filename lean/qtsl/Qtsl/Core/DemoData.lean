import Qtsl.Core.Catalogue
import Qtsl.Core.Decide

/-!
# Worked-example certificate data (computational core)

The value-level constructions of the worked example — the certificate
for `w₀ ∈ [1,2] ⊢ 1/2 + 2·w₀ ≥ 0` by Ax → ∧E → BernCone at `S = ∅` —
in the mathlib-free core so the executable checker can link them.
Side conditions are established by `decide +kernel`, which needs no
mathlib. The elaboration-time receipts live in
`Qtsl.EvalDemo`, which imports this module.
-/

namespace PPLC
namespace EvalDemo

def cxB : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 1 else 2
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := []
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide
  cellsWF := by decide

def simplexB : Simplex := ⟨cxB, fun _ => true, by decide⟩

def Sempty : ExtensionSet := ⟨simplexB, fun _ => false, by decide, by decide⟩

def H0 : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

def w0 : Term := .var 0

def polyB : Term := .add (.const (1/2)) (.mul (.const 2) w0)

def predP1 : Formula := .atom .ge (.var predicateHole) (.const 0)

def regionB : Formula := .inRegion w0 simplexB Sempty

def goalB : Formula := .atom .ge polyB (.const 0)

def seqAx : Sequent := ⟨.and regionB .tt, .and regionB .tt⟩
def seqRegion : Sequent := ⟨.and regionB .tt, regionB⟩
def seqGoal : Sequent := ⟨.and regionB .tt, goalB⟩

def pfAx : ProofObject H0 seqAx :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pfRegion : ProofObject H0 seqRegion :=
  .mk _ _ .andE (.andE _ _ (.left _ _ seqAx pfAx .tt rfl rfl))

def pfGoal : ProofObject H0 seqGoal :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := seqRegion) (regionProof := pfRegion)
    (termX := w0) (simplex := simplexB) (S := Sempty)
    (degree := 1) (polynomial := polyB) (predicate := predP1)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide⟩)
    (predShape := ⟨fun h => absurd (fun _ => rfl) h, fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

def demoCert : Certificate where
  hypernet := H0
  goalPre := regionB
  goalPost := goalB
  holeFresh := rfl
  proof := pfGoal

def simplexPt : Simplex := ⟨cxB, fun (v : Fin 2) => v == 0, by decide +kernel⟩
def SemptyPt : ExtensionSet :=
  ⟨simplexPt, fun _ => false, by decide +kernel, by decide +kernel⟩

def cxL : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 1 else 3/2
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := []
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

def simplexL : Simplex := ⟨cxL, fun _ => true, by decide⟩
def SemptyL : ExtensionSet := ⟨simplexL, fun _ => false, by decide, by decide⟩

def cxR : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 3/2 else 2
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := []
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

def simplexR : Simplex := ⟨cxR, fun _ => true, by decide⟩
def SemptyR : ExtensionSet := ⟨simplexR, fun _ => false, by decide, by decide⟩

def subBranchSimplex : Fin 2 → Simplex := fun k =>
  if k.val = 0 then simplexL else simplexR
def subBranchS : Fin 2 → ExtensionSet := fun k =>
  if k.val = 0 then SemptyL else SemptyR

def subBranchSeq : Fin 2 → Sequent := fun k =>
  ⟨.and seqRegion.pre (.inRegion w0 (subBranchSimplex k) (subBranchS k)),
   goalB⟩

def pfSubBranch : (k : Fin 2) → ProofObject H0 (subBranchSeq k) := fun k =>
  .mk _ _ .weaken (.weaken _ _ (.mk _ _ seqGoal pfGoal
    (.inRegion w0 (subBranchSimplex k) (subBranchS k)) rfl rfl))

def pfSubdivide : ProofObject H0 seqGoal :=
  .mk _ _ .subdivide (.subdivide _ _ (.mk _ _
    (regionPremise := seqRegion) (regionProof := pfRegion)
    (termX := w0) (simplex := simplexB) (S := Sempty)
    (nBranches := 2)
    (branchSimplex := subBranchSimplex)
    (branchS := subBranchS)
    (branchPremise := subBranchSeq)
    (branchProof := pfSubBranch)
    (coverCertificate := .const 0)
    (denBoundLog2 := 1)
    (preEq := rfl) (regionPost := rfl)
    (branchPre := fun _ => rfl) (branchPost := fun _ => rfl)
    (coverValid := by decide +kernel)))

def cxG : SimpC where
  nVertices := 2
  ambDim := 1
  coord := fun v _ => if v = 0 then 1 else 4/3
  simplices := [fun _ => true, fun v => v == 0, fun v => v == 1]
  cells := []
  nonempty := by decide
  closure := by decide
  conformity := by decide
  distinctVerts := by decide +kernel
  cellsWF := by decide

def simplexG : Simplex := ⟨cxG, fun _ => true, by decide⟩
def SemptyG : ExtensionSet := ⟨simplexG, fun _ => false, by decide, by decide⟩

def SextB : ExtensionSet :=
  ⟨simplexB, fun (v : Fin 2) => v == 0, by decide, by decide⟩

def HR : Hypernet where
  wireType := fun w =>
    if w = 0 then some ⟨[1], Dtype.Q⟩
    else if w = 1 then some ⟨[1], Dtype.Q⟩ else none
  applications := [.relu [1] 0 1]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide

def seqReluNN : Sequent := ⟨.tt, .atom .ge (.var 1) (.const 0)⟩
def pfReluNN : ProofObject HR seqReluNN :=
  .mk _ _ .reluNN (.reluNN _ _ (.mk _ _ 0 1 (by decide +kernel) rfl))

def seqReluAbove : Sequent := ⟨.tt, .atom .ge (.var 1) (.var 0)⟩
def pfReluAbove : ProofObject HR seqReluAbove :=
  .mk _ _ .reluAbove (.reluAbove _ _ (.mk _ _ 0 1 (by decide +kernel) rfl))

def preGe : Formula := .atom .ge (.var 0) (.const 0)
def seqReluPosPrem : Sequent := ⟨preGe, preGe⟩
def pfReluPosPrem : ProofObject HR seqReluPosPrem :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))
def seqReluPos : Sequent := ⟨preGe, .atom .eq (.var 1) (.var 0)⟩
def pfReluPos : ProofObject HR seqReluPos :=
  .mk _ _ .reluPos (.reluPos _ _ (.mk _ _ seqReluPosPrem pfReluPosPrem
    0 1 (by decide +kernel) rfl rfl rfl))

def preLe : Formula := .atom .le (.var 0) (.const 0)
def seqReluNegPrem : Sequent := ⟨preLe, preLe⟩
def pfReluNegPrem : ProofObject HR seqReluNegPrem :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))
def seqReluNeg : Sequent := ⟨preLe, .atom .eq (.var 1) (.const 0)⟩
def pfReluNeg : ProofObject HR seqReluNeg :=
  .mk _ _ .reluNeg (.reluNeg _ _ (.mk _ _ seqReluNegPrem pfReluNegPrem
    0 1 (by decide +kernel) rfl rfl rfl))

def preBox : Formula := .and (.atom .le (.const (-1)) (.var 0))
                             (.atom .le (.var 0) (.const 1))
def seqBoxAx : Sequent := ⟨preBox, preBox⟩
def pfBoxAx : ProofObject HR seqBoxAx := .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))
def seqBoxLo : Sequent := ⟨preBox, .atom .le (.const (-1)) (.var 0)⟩
def pfBoxLo : ProofObject HR seqBoxLo :=
  .mk _ _ .andE (.andE _ _ (.left _ _ seqBoxAx pfBoxAx _ rfl rfl))
def seqBoxHi : Sequent := ⟨preBox, .atom .le (.var 0) (.const 1)⟩
def pfBoxHi : ProofObject HR seqBoxHi :=
  .mk _ _ .andE (.andE _ _ (.right _ _ seqBoxAx pfBoxAx _ rfl rfl))
def seqLirpa : Sequent :=
  ⟨preBox, .and (.atom .le (affineWireTerm (-1/4) (1/2) 0) (.var 1))
                (.atom .le (.var 1) (affineWireTerm (1/2) (1/2) 0))⟩
def pfLirpa : ProofObject HR seqLirpa :=
  .mk _ _ .lirpa (.lirpa _ _ (.mk _ _ seqBoxLo pfBoxLo seqBoxHi pfBoxHi
    0 1 (-1) 1 (1/2) (-1/4) (1/2) (1/2) 2
    (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl rfl rfl rfl rfl))

def HR0 : Hypernet where
  wireType := fun w =>
    if w = 0 then some ⟨[0], Dtype.Q⟩
    else if w = 1 then some ⟨[0], Dtype.Q⟩ else none
  applications := [.relu [0] 0 1]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide

def HL : Hypernet where
  wireType := fun w =>
    if w = 0 then some ⟨[], Dtype.Q⟩
    else if w = 1 then some ⟨[], Dtype.Q⟩
    else if w = 2 then some ⟨[], Dtype.Q⟩
    else if w = 3 then some ⟨[], Dtype.Q⟩
    else if w = 4 then some ⟨[2], Dtype.Q⟩ else none
  applications := [.relu [] 0 2, .relu [] 1 3, .stack 2 [] [2, 3] 4]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide

def seqLayer : Sequent :=
  ⟨.tt, .and (.atom .ge (.var 2) (.const 0))
             (.atom .ge (.var 3) (.const 0))⟩
def pfLayer : ProofObject HL seqLayer :=
  .mk _ _ .andI (.andI _ _ (.mk _ _
    ⟨.tt, .atom .ge (.var 2) (.const 0)⟩
    (.mk _ _ .reluNN (.reluNN _ _ (.mk _ _ 0 2 (by decide +kernel) rfl)))
    ⟨.tt, .atom .ge (.var 3) (.const 0)⟩
    (.mk _ _ .reluNN (.reluNN _ _ (.mk _ _ 1 3 (by decide +kernel) rfl)))
    rfl rfl rfl))

end EvalDemo
end PPLC
