import SuFunctor.Adequacy.StochasticPetriDemonic

/-! # Axiom audit for the demonic (scheduler-quantified) net square

Prints the axiom footprint of the headline statements: the machine-
checked obstruction (the donor's hypothesis refutable at nets, and at
the shipped control net), the enabling-respecting arena and its Zeno
certificate, the rank-irrelevance package, the feeding lemma and the
invertible cell, the credal-slice reconciliation, the uniform-member
verdicts, the semantic-universe wiring quartet, and the concrete
controls (arena plurality, the discard member).  Expected footprint
for every entry: within `propext`, `Classical.choice`, `Quot.sound` —
the standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Adequacy.FinISPN.not_branchZenoFree_of_disabled
#print axioms SuFunctor.Adequacy.FinISPN.respZenoFree
#print axioms SuFunctor.Adequacy.FinISPN.uniformResp
#print axioms SuFunctor.Adequacy.FinISPN.demonicTangibleLaws_rank_irrel
#print axioms SuFunctor.Adequacy.FinISPN.demonicTangibleCredal_rank_irrel
#print axioms SuFunctor.Adequacy.FinISPN.ispnDemonicC_iff
#print axioms SuFunctor.Adequacy.FinISPN.ispn_demonic_adequacy
#print axioms SuFunctor.Adequacy.FinISPN.ispnDemonicCredalC_iff
#print axioms SuFunctor.Adequacy.FinISPN.ispn_demonic_maxSlice
#print axioms SuFunctor.Adequacy.FinISPN.ispn_demonic_ray_singleton_reconciliation
#print axioms SuFunctor.Adequacy.FinISPN.satCredal_lower_ispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinISPN.satCredal_upper_ispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinISPN.ispnDemonicC_uniform
#print axioms SuFunctor.Adequacy.FinISPN.demonicTangibleLaws_iff
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_demonic_adequacy
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_demonic_mem
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_demonic_bottom
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_demonic_slice
#print axioms SuFunctor.Adequacy.SpnDemonicControls.net₁_not_branchZenoFree
#print axioms SuFunctor.Adequacy.SpnDemonicControls.net₁_uniform_mem
#print axioms SuFunctor.Adequacy.SpnDemonicControls.net₁_demonicC_uniform
#print axioms SuFunctor.Adequacy.SpnDemonicControls.discardPolicy_respects
#print axioms SuFunctor.Adequacy.SpnDemonicControls.arena_plural
#print axioms SuFunctor.Adequacy.SpnDemonicControls.net₁_discard_mem
