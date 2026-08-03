import SuFunctor.QtslSem.Decode.Acceptance
import SuFunctor.QtslSem.Decode.AliasAcceptance

/-! # Axiom audit for the QtslSem acceptance theorem

Prints the axiom footprint of the acceptance route: the generic
assembly lemmas (the checked ground leaf through the promoted functor,
both carriers), the acceptance soundness theorems and the four E4
altitudes, the transport corollaries, the correspondence theorems, and
the fixture/refusal battery.  Per the preregistered expectation for
this seam,
everything whose statement mentions the decoder is expected at the
standard three (`propext`, `Classical.choice`, `Quot.sound`) — nothing
below is claimed.  No `sorryAx` anywhere.  `interpDeriv` /
`interpDerivSeq` are re-audited and stay axiom-free: this module's
package touches no existing module. -/

#print axioms SuFunctor.QtslSem.Decode.groundLeafCellM
#print axioms SuFunctor.QtslSem.Decode.groundLeafCoveringM
#print axioms SuFunctor.QtslSem.Decode.groundLeaf_valid_through_M
#print axioms SuFunctor.QtslSem.Decode.groundLeaf_valid_through_MJ
#print axioms SuFunctor.QtslSem.Decode.AcceptedLeaf.scopedAll
#print axioms SuFunctor.QtslSem.Decode.acceptedLeafRule_gate
#print axioms SuFunctor.QtslSem.Decode.acceptGroundLeaf
#print axioms SuFunctor.QtslSem.Decode.acceptQtslOps
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed
#print axioms SuFunctor.QtslSem.Decode.acceptQtslOps_sound
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed_sound
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed_face_sound
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed_modelClass_sound
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed_face_valWire_sound
#print axioms SuFunctor.QtslSem.Decode.acceptQtslSealed_su_sound
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteDeriv
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteCell
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteCovering
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteFacet_valid_through_M
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteFacet_valid_through_MJ
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteLeft_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteRight_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.acceptedCiteLeft_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.Decode.acceptGroundLeaf_elem
#print axioms SuFunctor.QtslSem.Decode.acceptGroundLeaf_seq
#print axioms SuFunctor.QtslSem.Decode.acceptLeaf_seq
#print axioms SuFunctor.QtslSem.Decode.acceptLeaf_elem
#print axioms SuFunctor.QtslSem.Decode.acceptLeaves_spec
#print axioms SuFunctor.QtslSem.Decode.accept_spec
#print axioms SuFunctor.QtslSem.Decode.fixtureEval
#print axioms SuFunctor.QtslSem.Decode.fixtureLeaf
#print axioms SuFunctor.QtslSem.Decode.acceptGroundLeaf_fixture
#print axioms SuFunctor.QtslSem.Decode.acceptLeaf_fixture
#print axioms SuFunctor.QtslSem.Decode.acceptLeaves_fixture
#print axioms SuFunctor.QtslSem.Decode.accept_fixture
#print axioms SuFunctor.QtslSem.Decode.accept_fixture_pres
#print axioms SuFunctor.QtslSem.Decode.accept_fixture_leaves
#print axioms SuFunctor.QtslSem.Decode.accept_fixture_matches_enumerator
#print axioms SuFunctor.QtslSem.Decode.accepted_fixture_face_through_M
#print axioms SuFunctor.QtslSem.Decode.accepted_fixture_su_sound
#print axioms SuFunctor.QtslSem.Decode.refuse_routeless
#print axioms SuFunctor.QtslSem.Decode.refuse_region_tier
#print axioms SuFunctor.QtslSem.Decode.refuse_warrant_routed
#print axioms SuFunctor.QtslSem.Decode.refuse_statistical_tier
#print axioms SuFunctor.QtslSem.Decode.refuse_nonatom_concl
#print axioms SuFunctor.QtslSem.Decode.fixtureEvalFalse
#print axioms SuFunctor.QtslSem.Decode.refuse_eval_false

/-! The v1.1 alias-citation walk (`Decode.AliasAcceptance` + the
route extensions in `Decode.Acceptance`): same expectation — the
standard three, `sorryAx` 0.  (`accepted_taylor_le_exp` reaches
`Real.exp` through mathlib; still the standard three.) -/

#print axioms SuFunctor.QtslSem.Decode.resolveCitation
#print axioms SuFunctor.QtslSem.Decode.sequentMatchesSublevel
#print axioms SuFunctor.QtslSem.Decode.acceptLeaves_spec
#print axioms SuFunctor.QtslSem.Decode.accept_taylor
#print axioms SuFunctor.QtslSem.Decode.accepted_taylor_su_sound
#print axioms SuFunctor.QtslSem.Decode.taylorPartialSum_demo
#print axioms SuFunctor.QtslSem.Decode.accepted_taylor_le_exp
#print axioms SuFunctor.QtslSem.Decode.accept_citation
#print axioms SuFunctor.QtslSem.Decode.accepted_citation_su_sound
#print axioms SuFunctor.QtslSem.Decode.accepted_rootEval_member
#print axioms SuFunctor.QtslSem.Decode.refuse_misrooted_citation
#print axioms SuFunctor.QtslSem.Decode.refuse_box_region_citation
#print axioms SuFunctor.QtslSem.Decode.refuse_affine_region_citation
#print axioms SuFunctor.QtslSem.Decode.refuse_threshold_mismatch
#print axioms SuFunctor.QtslSem.Decode.refuse_eq_comparator_citation

#print axioms CategoryTheory.VdcInterpretation.interpDeriv
#print axioms CategoryTheory.VdcInterpretation.interpDerivSeq
