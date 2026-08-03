import SuFunctor.QtslSem.BLFactoring

/-! # Axiom audit for the judgment layer

Prints the axiom footprint of the judgment-layer carrier (the ordered
decoration datum's derived inverse transport, the fibre-order cell
constructor), the semantic universe's inclusion-ordered instance, and
the re-targeted structural fragment with its fixture twin.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three (`Classical.choice` enters by design
where the free-promotion transpose is consumed), no `sorryAx`, nothing
else. -/

#print axioms CategoryTheory.JudgmentOrder.pull_inv
#print axioms CategoryTheory.JudgmentOrder.propDatum
#print axioms CategoryTheory.JudgLayer.cell_subsingleton
#print axioms CategoryTheory.JudgLayer.cellOfLe
#print axioms SuFunctor.QtslSem.specJudgOrder
#print axioms SuFunctor.QtslSem.specJudgLayer_pseudoDoubleCategory
#print axioms SuFunctor.QtslSem.specJudgLayer_cell_subsingleton
#print axioms SuFunctor.QtslSem.cellOfSubset
#print axioms SuFunctor.QtslSem.blInterpretationJ
#print axioms SuFunctor.QtslSem.qtslSemBLJ
#print axioms SuFunctor.QtslSem.cut_face_through_promotionJ
#print axioms SuFunctor.QtslSem.eqElim_const_face_through_promotionJ
#print axioms SuFunctor.QtslSem.reluChain_face_through_promotionJ
#print axioms SuFunctor.QtslSem.foldJ_ofList_valid
#print axioms SuFunctor.QtslSem.foldJ_ofFin_valid
#print axioms SuFunctor.QtslSem.subdivideFan_face_through_promotionJ
#print axioms SuFunctor.QtslSem.syzygyPair_face_through_promotionJ
#print axioms SuFunctor.QtslSem.antisymConst_face_through_promotionJ
