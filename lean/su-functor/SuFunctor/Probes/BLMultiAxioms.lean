import SuFunctor.QtslSem.BLMulti

/-! # Axiom audit for the many-object presentation

Prints the axiom footprint of the hypernet-context presentation, its
two carrier interpretations and promoted semantics, the derived cite
family of the product-lattice rule, the batch lemma, and the two-factor
fixture corollaries.  Expected footprint: the fold-transport lemmas and
the derivation-level data at most `propext`; everything consuming the
free-promotion transpose the standard three (`propext`,
`Classical.choice`, `Quot.sound`); no `sorryAx`, nothing else.  The
presentation machinery itself is untouched by this module —
`interpDeriv`/`interpDerivSeq` are re-audited here and stay
axiom-free. -/

#print axioms SuFunctor.QtslSem.fold_emb_valid
#print axioms SuFunctor.QtslSem.foldJ_emb_valid
#print axioms SuFunctor.QtslSem.blPresentationM
#print axioms SuFunctor.QtslSem.blMInterpretation
#print axioms SuFunctor.QtslSem.blMInterpretationJ
#print axioms SuFunctor.QtslSem.qtslSemBLM
#print axioms SuFunctor.QtslSem.qtslSemBLMJ
#print axioms SuFunctor.QtslSem.extendDeriv
#print axioms SuFunctor.QtslSem.citeDeriv
#print axioms SuFunctor.QtslSem.citeCell
#print axioms SuFunctor.QtslSem.citeCovering
#print axioms SuFunctor.QtslSem.cite_valid_through_M
#print axioms SuFunctor.QtslSem.cite_valid_through_MJ
#print axioms SuFunctor.QtslSem.cite_face_through_promotionM
#print axioms SuFunctor.QtslSem.cite_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.citeLeft_face_through_promotionM
#print axioms SuFunctor.QtslSem.citeRight_face_through_promotionM
#print axioms SuFunctor.QtslSem.citeLeft_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.citeRight_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.sound_productLattice_through_M
#print axioms SuFunctor.QtslSem.sound_productLattice_through_MJ
#print axioms SuFunctor.QtslSem.demoJoinFacetX_face_through_promotionM
#print axioms SuFunctor.QtslSem.demoJoinFacetY_face_through_promotionM
#print axioms SuFunctor.QtslSem.demoJoinFacetX_face_through_promotionMJ
#print axioms SuFunctor.QtslSem.demoJoinFacetY_face_through_promotionMJ
#print axioms CategoryTheory.VdcInterpretation.interpDeriv
#print axioms CategoryTheory.VdcInterpretation.interpDerivSeq
