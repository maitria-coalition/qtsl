import SuFunctor.QtslSem.Decode.BLMultiSeam

/-! # Axiom audit for the decoder→BLMulti seam

Prints the axiom footprint of the seam enumerator's fixture theorem
(expected axiom-free — kernel reduction), the wire-free scoping lemma
(at most `propext`), and the emb/extend routes through the many-object
carriers (the standard three — the free-promotion transpose's
footprint, as measured on the many-object presentation's own battery).
No `sorryAx`, nothing else.  `interpDeriv`/`interpDerivSeq` are
re-audited and stay axiom-free: this module's package touches no
existing module. -/

#print axioms SuFunctor.QtslSem.Decode.satLeafSequents_fixture
#print axioms SuFunctor.QtslSem.Decode.leafSeqDemo_wellScoped
#print axioms SuFunctor.QtslSem.Decode.embDecodedCell
#print axioms SuFunctor.QtslSem.Decode.embDecodedCovering
#print axioms SuFunctor.QtslSem.Decode.decodedLeaf_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.decodedLeaf_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.Decode.decodedCiteDeriv
#print axioms SuFunctor.QtslSem.Decode.decodedCiteCell
#print axioms SuFunctor.QtslSem.Decode.decodedCiteCovering
#print axioms SuFunctor.QtslSem.Decode.decodedCiteFacet_valid_through_M
#print axioms SuFunctor.QtslSem.Decode.decodedCiteFacet_valid_through_MJ
#print axioms SuFunctor.QtslSem.Decode.decodedCiteLeft_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.decodedCiteRight_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.decodedCiteLeft_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.Decode.decodedCiteRight_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.Decode.decodedLeafCiteX_face_through_promotionM
#print axioms SuFunctor.QtslSem.Decode.decodedLeafCiteY_face_through_promotionMJ
#print axioms CategoryTheory.VdcInterpretation.interpDeriv
#print axioms CategoryTheory.VdcInterpretation.interpDerivSeq
