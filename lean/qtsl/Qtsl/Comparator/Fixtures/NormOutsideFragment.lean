import Qtsl.EvalDemo

/-!
# Comparator fixture: a single `Norm` node

A certificate consisting of one `Norm` node (canonical-form equality of
`w₀ + w₀` and `2·w₀`), side conditions kernel-checked at elaboration.
Expected verdicts: `check = true`, `v0frag = true` — since `v0frag` is
defined by proof availability and the `Norm` soundness lemma covers
every `.norm` node, this fixture sits inside the v0 fragment; all
execution paths must agree on acceptance.
-/

namespace PPLC.Comparator.Fixtures.NormOutsideFragment

open EvalDemo

def seqNorm : Sequent :=
  ⟨.tt, .atom .eq (.add w0 w0) (.mul (.const 2) w0)⟩

def pf : ProofObject H0 seqNorm :=
  .mk _ _ .norm (.norm _ _ (.mk _ _
    (.add w0 w0) (.mul (.const 2) w0)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    rfl))

end PPLC.Comparator.Fixtures.NormOutsideFragment
