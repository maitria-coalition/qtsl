import Qtsl.Soundness
import Qtsl.Comparator.Fixtures.DemoBernCone
import Qtsl.Comparator.Fixtures.MultivarBernCone
import Qtsl.Comparator.Fixtures.NormOutsideFragment

/-!
# Comparator fixture registry

Registry for the checker comparator harness, which runs the same
certificate values through independent execution paths of the same
Lean functions (`check` and `ProofObject.v0frag`) and compares
verdicts: the compiled path (this registry built as an executable),
the kernel path (per-fixture `decide +kernel` probes), and the
interpreted path (this registry under `lean --run`). Any disagreement
between paths is a finding.
-/

namespace PPLC.Comparator

structure Entry where
  name : String
  checkVerdict : Bool
  fragVerdict : Bool

def entries : List Entry :=
  [ ⟨"DemoBernCone",
      check Fixtures.DemoBernCone.pf,
      Fixtures.DemoBernCone.pf.v0frag⟩,
    ⟨"MultivarBernCone",
      check Fixtures.MultivarBernCone.pf,
      Fixtures.MultivarBernCone.pf.v0frag⟩,
    ⟨"NormOutsideFragment",
      check Fixtures.NormOutsideFragment.pf,
      Fixtures.NormOutsideFragment.pf.v0frag⟩ ]

def printVerdicts : IO Unit := do
  for e in entries do
    IO.println s!"{e.name} check={e.checkVerdict} v0frag={e.fragVerdict}"

end PPLC.Comparator
