import SuFunctor.QtslSem.Fixture

/-! # Axiom audit for the presented-semantics scaffold

Prints the axiom footprint of the presentation machinery (the derivation
reading, the induced virtual double functor, the free-promotion
transpose), the structural fragment's interpretation, and the fixture's
composed statement.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three (`Classical.choice`
enters by design: the transpose is noncomputable), no `sorryAx`, nothing
else. -/

#print axioms CategoryTheory.Presented.cellSeq_derivSeq
#print axioms CategoryTheory.VdcInterpretation.interpDeriv
#print axioms CategoryTheory.VdcInterpretation.interpDerivSeq
#print axioms CategoryTheory.VdcInterpretation.functor
#print axioms CategoryTheory.VdcInterpretation.sem
#print axioms CategoryTheory.VdcInterpretation.sem_isPseudo
#print axioms SuFunctor.QtslSem.blInterpretation
#print axioms SuFunctor.QtslSem.qtslSemBL
#print axioms SuFunctor.QtslSem.cutCell
#print axioms SuFunctor.QtslSem.cut_face_through_promotion
#print axioms SuFunctor.QtslSem.eqElimConstDeriv
#print axioms SuFunctor.QtslSem.eqElimConstCell
#print axioms SuFunctor.QtslSem.eqElim_const_face_through_promotion
#print axioms SuFunctor.QtslSem.reluChainDeriv
#print axioms SuFunctor.QtslSem.reluChainCell
#print axioms SuFunctor.QtslSem.reluChain_face_through_promotion
#print axioms CategoryTheory.LoosePath.ofList
#print axioms CategoryTheory.LoosePath.ofFin
#print axioms CategoryTheory.LoosePath.map_ofList
#print axioms CategoryTheory.LoosePath.map_ofFin
#print axioms SuFunctor.QtslSem.fold_ofList_valid
#print axioms SuFunctor.QtslSem.fold_ofFin_valid
#print axioms SuFunctor.QtslSem.subdivideFanDeriv
#print axioms SuFunctor.QtslSem.subdivideFanCell
#print axioms SuFunctor.QtslSem.subdivideFan_face_through_promotion
#print axioms SuFunctor.QtslSem.syzygyPairCell
#print axioms SuFunctor.QtslSem.syzygyPair_face_through_promotion
#print axioms SuFunctor.QtslSem.antisymConstDeriv
#print axioms SuFunctor.QtslSem.antisymConstCell
#print axioms SuFunctor.QtslSem.antisymConst_face_through_promotion
