import SuFunctor.Adequacy.StochasticPetriColouredDemonic

/-! # Axiom audit for the coloured demonic and angelic net faces

Prints the axiom footprint of the headline statements: the
machine-checked obstruction at colour (disabled pairs by supply and
by guard, each refuting the donor's branch-level hypothesis), the
enabling-respecting arena over pairs and its Zeno certificate, the
rank-irrelevance package, the feeding lemma and the invertible cell,
the credal-slice reconciliation, the verdicts at both polarities, the
membership lemma, the angelic feeding equivalence and both directed
transfers, the semantic-universe wiring quartet, and the concrete
controls (the double refutation, the rank-free recolouring cycle, the
colour-conflict arena plurality).  Expected footprint for every
entry: within `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Adequacy.FinCISPN.not_branchZenoFree_of_disabled
#print axioms SuFunctor.Adequacy.FinCISPN.respZenoFree
#print axioms SuFunctor.Adequacy.FinCISPN.uniformResp
#print axioms SuFunctor.Adequacy.FinCISPN.demonicTangibleLaws_rank_irrel
#print axioms SuFunctor.Adequacy.FinCISPN.demonicTangibleCredal_rank_irrel
#print axioms SuFunctor.Adequacy.FinCISPN.cispnDemonicC_iff
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_demonic_adequacy
#print axioms SuFunctor.Adequacy.FinCISPN.cispnDemonicCredalC_iff
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_demonic_maxSlice
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_demonic_ray_singleton_reconciliation
#print axioms SuFunctor.Adequacy.FinCISPN.satCredal_lower_cispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinCISPN.satCredal_upper_cispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinCISPN.cispnDemonicC_uniform
#print axioms SuFunctor.Adequacy.FinCISPN.demonicTangibleLaws_iff
#print axioms SuFunctor.Adequacy.FinCISPN.satAngelic_cispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_angelic_of_member
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_demonic_verdict_to_member
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_demonic_upper_to_member
#print axioms SuFunctor.Adequacy.FinCISPN.satAngelic_unsliced_degenerate
#print axioms SuFunctor.Adequacy.FinCISPN.satAngelic_unsliced_leC_degenerate
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_demonic_adequacy
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_demonic_mem
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_demonic_bottom
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_demonic_slice
#print axioms SuFunctor.Adequacy.CspnDemonicControls.cnet₁_not_branchZenoFree
#print axioms SuFunctor.Adequacy.CspnDemonicControls.cnet₁_not_branchZenoFree_guard
#print axioms SuFunctor.Adequacy.CspnDemonicControls.cnet₁_uniform_mem
#print axioms SuFunctor.Adequacy.CspnDemonicControls.cnet₁_demonicC_uniform
#print axioms SuFunctor.Adequacy.CspnDemonicControls.cnet₂_no_cascadeRank
#print axioms SuFunctor.Adequacy.CspnDemonicControls.preferRed_respects
#print axioms SuFunctor.Adequacy.CspnDemonicControls.arena_plural_by_colour
