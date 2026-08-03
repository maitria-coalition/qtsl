import Qtsl.EvalDemo

/-!
# Comparator fixture: the worked-example certificate

The one-dimensional worked example (Ax → ∧E → BernCone at `S = ∅` over
`conv(1, 2)`), as constructed in `Qtsl.EvalDemo`. Expected
verdicts: `check = true`, `v0frag = true` — the positive-lane fixture on
which all execution paths must agree.
-/

namespace PPLC.Comparator.Fixtures.DemoBernCone

def pf : ProofObject EvalDemo.H0 EvalDemo.seqGoal := EvalDemo.pfGoal

end PPLC.Comparator.Fixtures.DemoBernCone
