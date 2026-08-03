import Qtsl.Soundness
import Qtsl.Decide

/-!
# Comparator fixture: a multivariate Bernstein-cone certificate

A genuinely multivariate BernCone certificate: Ax → ∧E → BernCone at
`S = ∅` over the standard 3-simplex `conv(0, e₁, e₂, e₃) ⊆ ℚ³`, for the
degree-2 polynomial `p(x) = 1 + x₀·x₁ + x₂²` under the predicate
`□ ≥ 0`. In barycentric coordinates the normalized Bernstein
coefficients are all nonnegative, so the sweep passes; the tightened
control `□ ≥ 3/2` must fail (the pure-λ₀ coefficient is 1).
-/

namespace PPLC.Comparator.Fixtures.MultivarBernCone

open PPLC

def cxM : SimpC where
  nVertices := 4
  ambDim := 3
  coord := fun v j => if v.val = j.val + 1 then 1 else 0
  simplices :=
    [ fun v => v.val == 0 || v.val == 1 || v.val == 2 || v.val == 3,
      fun v => v.val == 1 || v.val == 2 || v.val == 3,
      fun v => v.val == 0 || v.val == 2 || v.val == 3,
      fun v => v.val == 0 || v.val == 1 || v.val == 3,
      fun v => v.val == 0 || v.val == 1 || v.val == 2,
      fun v => v.val == 2 || v.val == 3,
      fun v => v.val == 1 || v.val == 3,
      fun v => v.val == 1 || v.val == 2,
      fun v => v.val == 0 || v.val == 3,
      fun v => v.val == 0 || v.val == 2,
      fun v => v.val == 0 || v.val == 1,
      fun v => v.val == 0,
      fun v => v.val == 1,
      fun v => v.val == 2,
      fun v => v.val == 3 ]
  cells := []
  nonempty := by decide +kernel
  closure := by decide +kernel
  conformity := by decide +kernel
  distinctVerts := by decide +kernel
  cellsWF := by decide +kernel

def simplexM : Simplex :=
  ⟨cxM, fun v => v.val == 0 || v.val == 1 || v.val == 2 || v.val == 3, by decide +kernel⟩

def SemptyM : ExtensionSet :=
  ⟨simplexM, fun _ => false, by decide +kernel, by decide +kernel⟩

def SoneM : ExtensionSet :=
  ⟨simplexM, fun v => v.val == 0, by decide +kernel, by decide +kernel⟩

def H0M : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[3], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

def w0 : Term := .var 0

def polyM : Term :=
  .add (.add (.const 1) (.mul (.idx w0 0) (.idx w0 1)))
       (.mul (.idx w0 2) (.idx w0 2))

def predP1 : Formula := .atom .ge (.var predicateHole) (.const 0)

def regionM : Formula := .inRegion w0 simplexM SemptyM

def goalM : Formula :=
  .atom .ge (.add (.add (.const 1) (.mul (.idx w0 0) (.idx w0 1)))
                  (.mul (.idx w0 2) (.idx w0 2))) (.const 0)

def seqAx : Sequent := ⟨.and regionM .tt, .and regionM .tt⟩
def seqRegion : Sequent := ⟨.and regionM .tt, regionM⟩
def seqGoal : Sequent := ⟨.and regionM .tt, goalM⟩

def pfAx : ProofObject H0M seqAx :=
  .mk _ _ .ax (.ax _ _ (.mk _ _ rfl))

def pfRegion : ProofObject H0M seqRegion :=
  .mk _ _ .andE (.andE _ _ (.left _ _ seqAx pfAx .tt rfl rfl))

def pf : ProofObject H0M seqGoal :=
  .mk _ _ .bernCone (.bernCone _ _ (.mk _ _
    (regionPremise := seqRegion) (regionProof := pfRegion)
    (termX := w0) (simplex := simplexM) (S := SemptyM)
    (degree := 2) (polynomial := polyM) (predicate := predP1)
    (preEq := rfl) (regionPost := rfl)
    (polyTie := Or.inr ⟨0, rfl, by decide⟩)
    (predShape := ⟨fun h => absurd (fun _ => rfl) h,
                   fun _ => by decide +kernel⟩)
    (coefficients := by decide +kernel)
    (postApply := rfl)))

theorem pfFrag : pf.v0frag = true := by decide +kernel

theorem multivarValid : seqGoal.semanticallyValid H0M :=
  check_sound_v0 pf pfFrag

#print axioms multivarValid

#eval bernConeCoeffCheck simplexM SemptyM 2 polyM predP1

#eval QArith.fdBernstein
  (((List.finRange cxM.nVertices).filter (fun v => simplexM.contains v)).map
    fun v => (List.finRange cxM.ambDim).map fun j => cxM.coord v j)
  [false, false, false, false] 2 ((Term.asCoordPoly? polyM).getD [])

#eval bernConeCoeffCheck simplexM SemptyM 2 polyM
  (.atom .ge (.var predicateHole) (.const (3/2)))

#eval bernConeCoeffCheck simplexM SemptyM 2
  (.add (.const 1) (.idx w0 3)) predP1

#eval bernConeCoeffCheck simplexM SoneM 2 polyM predP1

#eval bernConeCoeffCheck simplexM SemptyM 2
  (.add w0 (.idx w0 0)) predP1

#eval bernConeCoeffCheck simplexM SemptyM 1 polyM predP1

end PPLC.Comparator.Fixtures.MultivarBernCone
