import SuFunctor.QtslSem.Decode.Warrant
import SuFunctor.QtslSem.Decode.ReceiptWarrantUnit

/-! # Axiom audit for the warrant route

Prints the axiom footprint of the widened acceptance route: the
warrant acceptance functions, the soundness theorems, the
`SpecJudgLayer` resolution (cells, the resolved inclusion, the
pointwise face and the restated stock lemma), the correspondence
lemmas, and the fixture/refusal battery.  Everything whose statement
mentions the decoder or the carriers is expected at the standard three
(`propext`, `Classical.choice`, `Quot.sound`); `sound_QSatFromRegion`
and `AcceptedWarrant.resolve`/`resolve_pointwise`/
`formula_class_agrees` are expected **axiom-free** (set algebra and
one rewrite).  No `sorryAx` anywhere.  This module's package touches
no existing module. -/

#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat
#print axioms SuFunctor.QtslSem.Decode.acceptClaimsW
#print axioms SuFunctor.QtslSem.Decode.acceptFragmentGateW
#print axioms SuFunctor.QtslSem.Decode.acceptQtslOpsW
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealedW
#print axioms SuFunctor.QtslSem.Decode.QtslAcceptedW.leaves
#print axioms SuFunctor.QtslSem.Decode.QtslAcceptedW.warrants
#print axioms SuFunctor.QtslSem.Decode.acceptQtslOpsW_sound_leaf
#print axioms SuFunctor.QtslSem.Decode.acceptQtslOpsW_sound_membership
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealedW_sound_leaf
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealedW_sound_membership
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealedW_su_sound
#print axioms SuFunctor.QtslSem.Decode.ClassAssignment
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.membershipCell
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.warrantCell
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.resolvedCell
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.resolve
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.resolveCell
#print axioms Qtsl.Aliases.sound_QSatFromRegion
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.resolve_pointwise
#print axioms SuFunctor.QtslSem.Decode.AcceptedWarrant.formula_class_agrees
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_elem
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_sys
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_f
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_region
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_leaf
#print axioms SuFunctor.QtslSem.Decode.acceptClaimsW_spec
#print axioms SuFunctor.QtslSem.Decode.decode_fixtureWarrant_ok
#print axioms SuFunctor.QtslSem.Decode.fixtureWarrant
#print axioms SuFunctor.QtslSem.Decode.fixtureWarrant_leaf_seq
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_fixture
#print axioms SuFunctor.QtslSem.Decode.acceptClaimsW_fixture
#print axioms SuFunctor.QtslSem.Decode.acceptW_fixture_warrant
#print axioms SuFunctor.QtslSem.Decode.acceptW_fixture_evalOnly
#print axioms SuFunctor.QtslSem.Decode.acceptedW_fixture_membership_face
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_no_eval
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_wrong_tie
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_face_not_sinit
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_foreign_face
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_init_member_order
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_no_initmember
#print axioms SuFunctor.QtslSem.Decode.refuse_uncited_region_W
#print axioms SuFunctor.QtslSem.Decode.refuse_statistical_W

/-! ## Real-byte round-trip: the receipt module's key
theorems.  `qtslPins_wf` stays axiom-FREE at the 182-row width; the
decide-carried parse/scan/assembly ties and the refusal tooth are
expected at the standard three or below; the sealed acceptance and the
checker-face corollary ride the carried validity (standard three). -/

#print axioms SuFunctor.QtslSem.Decode.qtslPins_wf
#print axioms SuFunctor.QtslSem.Decode.commitShape
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealedW_eq_of_commitShape
#print axioms SuFunctor.QtslSem.Decode.realUnit_commit_shape
#print axioms SuFunctor.QtslSem.Decode.realUnit_scan
#print axioms SuFunctor.QtslSem.Decode.realUnit_assemble
#print axioms SuFunctor.QtslSem.Decode.realUnit_leaf_seq
#print axioms SuFunctor.QtslSem.Decode.acceptGroundLeaf_realUnit
#print axioms SuFunctor.QtslSem.Decode.acceptWarrantSat_realUnit
#print axioms SuFunctor.QtslSem.Decode.accept_realUnit_ops
#print axioms SuFunctor.QtslSem.Decode.accept_realUnit_sealed
#print axioms SuFunctor.QtslSem.Decode.realUnit_membership_face
#print axioms SuFunctor.QtslSem.Decode.decode_realUnit_init_member_order
#print axioms SuFunctor.QtslSem.Decode.refuse_realUnit_init_member_order
