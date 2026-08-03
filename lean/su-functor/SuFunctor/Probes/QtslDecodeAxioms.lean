import SuFunctor.QtslSem.Decode.Fixture
import SuFunctor.QtslSem.Decode.Binding

/-! # Axiom audit for the theory-Qtsl row decoder

Prints the axiom footprint of the S1 decoder's pin table
well-formedness, the decode/seam/kit-walk fixture theorems, the
refusal fixtures, the binding table's well-formedness, and the two
carrier face theorems on the decoded row.  Expected: at most
`propext`, `Classical.choice`, `Quot.sound` — the standard three
(`Classical.choice` enters by design where the free-promotion
transpose is consumed; the pure decide-checked decode equalities are
expected below that envelope), no `sorryAx`, nothing else.  The
interpretation reading (`interpDeriv`/`interpDerivSeq`) is untouched
by this leg and must remain axiom-free — reprobed here. -/

#print axioms SuFunctor.QtslSem.Decode.qtslPins_wf
#print axioms SuFunctor.QtslSem.Decode.qtslBindingTable_wf
#print axioms SuFunctor.QtslSem.Decode.decode_fixture_ok
#print axioms SuFunctor.QtslSem.Decode.fixture_leaf_seq
#print axioms SuFunctor.QtslSem.Decode.walk_fixture
#print axioms SuFunctor.QtslSem.Decode.refuse_missing_sys
#print axioms SuFunctor.QtslSem.Decode.refuse_orphan_proof
#print axioms SuFunctor.QtslSem.Decode.refuse_unpinned
#print axioms SuFunctor.QtslSem.Decode.refuse_sys_wrong_sort
#print axioms SuFunctor.QtslSem.Decode.refuse_qpl_cycle
#print axioms SuFunctor.QtslSem.Decode.decodedLeafRule_gate
#print axioms SuFunctor.QtslSem.Decode.decodedLeaf_face_through_promotion
#print axioms SuFunctor.QtslSem.Decode.decodedLeaf_face_through_promotionJ
#print axioms CategoryTheory.VdcInterpretation.interpDeriv
#print axioms CategoryTheory.VdcInterpretation.interpDerivSeq
