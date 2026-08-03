import SuFunctor.TokenArcs

/-! # Axiom audit for the bag former and the token-arc compiles

Prints the axiom footprint of the bag former's denotational layer: the
switch subsumption, the functoriality and naturality of the statics,
the exchange action and its invariance classes, the multiset
denotation with its quotient identification (invariance +
completeness), the monad structure's static shadows, and the arc-level
compile statements (ordinary-arc cons identity and its
well-definedness on the quotient, the enabling readout's
parameter-identification denotation, the exchange-covariance family).
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.BagFormer SuFunctor.TokenArcs

#print axioms SuFunctor.BagFormer.bagObj_eq_switchObj
#print axioms SuFunctor.BagFormer.modeIncl_eq_switchIncl
#print axioms SuFunctor.BagFormer.bagMap_id
#print axioms SuFunctor.BagFormer.bagMap_comp
#print axioms SuFunctor.BagFormer.tokenIncl_natural
#print axioms SuFunctor.BagFormer.countIncl_natural
#print axioms SuFunctor.BagFormer.modeIncl_natural
#print axioms SuFunctor.BagFormer.dnfPull_token_natural
#print axioms SuFunctor.BagFormer.bagPerm_one
#print axioms SuFunctor.BagFormer.bagPerm_comp
#print axioms SuFunctor.BagFormer.bagPerm_countIncl
#print axioms SuFunctor.BagFormer.bagPerm_tokenIncl
#print axioms SuFunctor.BagFormer.modeIncl_bagPerm
#print axioms SuFunctor.BagFormer.bagPerm_bagMap
#print axioms SuFunctor.BagFormer.exchangeInvariant_count
#print axioms SuFunctor.BagFormer.exchangeInvariant_map
#print axioms SuFunctor.BagFormer.powBag_card
#print axioms SuFunctor.BagFormer.map_univ_val_eq_iff
#print axioms SuFunctor.BagFormer.powBag_perm
#print axioms SuFunctor.BagFormer.powBag_eq_iff
#print axioms SuFunctor.BagFormer.toBag_card
#print axioms SuFunctor.BagFormer.toBag_bagPerm
#print axioms SuFunctor.BagFormer.tokenIncl_mem_toBag
#print axioms SuFunctor.BagFormer.toBag_one
#print axioms SuFunctor.BagFormer.powBag_flatten
#print axioms SuFunctor.TokenArcs.powBag_drop
#print axioms SuFunctor.TokenArcs.drop_wellDefined
#print axioms SuFunctor.TokenArcs.readRows_pat_iff
#print axioms SuFunctor.TokenArcs.readSetRows
#print axioms SuFunctor.TokenArcs.readRows_perm
#print axioms SuFunctor.TokenArcs.readCell
