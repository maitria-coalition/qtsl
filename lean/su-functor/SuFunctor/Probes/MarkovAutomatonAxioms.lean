import SuFunctor.Adequacy.MarkovAutomaton
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Axiom audit for the Markov-automaton square

Prints the axiom footprint of the Markov-automaton adequacy square at
its fixed-scheduler face: the mixed immediate kernel and its derived
stochasticity, the acyclic-absorption package (stabilization, mass,
uniqueness), the fixed-scheduler closure with its rate-factorization
and thinning receipts, the rate-closure triangle, the square, the
blindness receipt, the transported connector, and the
semantic-universe wiring.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinMA.offRate_nonneg
#print axioms SuFunctor.Adequacy.FinMA.offRate_diag
#print axioms SuFunctor.Adequacy.FinMA.offRate_of_ne
#print axioms SuFunctor.Adequacy.FinMA.exitRate_nonneg
#print axioms SuFunctor.Adequacy.mix_row_sum
#print axioms SuFunctor.Adequacy.FinMA.imStep_nonneg
#print axioms SuFunctor.Adequacy.FinMA.imStep_row_sum
#print axioms SuFunctor.Adequacy.zenoFree_of_branch
#print axioms SuFunctor.Adequacy.hitMass_nonneg
#print axioms SuFunctor.Adequacy.absorbIter_inl
#print axioms SuFunctor.Adequacy.absorbIter_nonneg
#print axioms SuFunctor.Adequacy.absorbIter_succ_stab
#print axioms SuFunctor.Adequacy.absorbIter_stab
#print axioms SuFunctor.Adequacy.absorbIter_inl_mass
#print axioms SuFunctor.Adequacy.absorbIter_mass
#print axioms SuFunctor.Adequacy.absorbIter_unique
#print axioms SuFunctor.Adequacy.lt_absFuel
#print axioms SuFunctor.Adequacy.FinMA.absorb_nonneg
#print axioms SuFunctor.Adequacy.FinMA.absorb_mass
#print axioms SuFunctor.Adequacy.FinMA.absorb_step
#print axioms SuFunctor.Adequacy.FinMA.close_rate
#print axioms SuFunctor.Adequacy.FinMA.close_init
#print axioms SuFunctor.Adequacy.FinMA.preChain_offRate
#print axioms SuFunctor.Adequacy.FinMA.preChain_offRate_inr
#print axioms SuFunctor.Adequacy.FinMA.preChain_exitRate
#print axioms SuFunctor.Adequacy.FinMA.close_offRate_factor
#print axioms SuFunctor.Adequacy.FinMA.close_exitRate_thinning
#print axioms SuFunctor.Adequacy.FinMA.close_exitRate_le
#print axioms SuFunctor.Adequacy.FinMA.pathLaw_mass
#print axioms SuFunctor.Adequacy.MaRows.rateAt_nonneg
#print axioms SuFunctor.Adequacy.compileMa_rateRow
#print axioms SuFunctor.Adequacy.compileMa_branchRow
#print axioms SuFunctor.Adequacy.compileMa_initRow
#print axioms SuFunctor.Adequacy.compileMa_wf
#print axioms SuFunctor.Adequacy.compileMa_rateAt
#print axioms SuFunctor.Adequacy.compileMa_branchAt
#print axioms SuFunctor.Adequacy.compileMa_diag_blind
#print axioms SuFunctor.Adequacy.imStepRows_nonneg
#print axioms SuFunctor.Adequacy.imStepRows_row_sum
#print axioms SuFunctor.Adequacy.closeMaRows_rateRow
#print axioms SuFunctor.Adequacy.closeMaRows_initRow
#print axioms SuFunctor.Adequacy.closeMaRows_wf
#print axioms SuFunctor.Adequacy.compile_closeMa_comm
#print axioms SuFunctor.Adequacy.ma_adequacy
#print axioms SuFunctor.Adequacy.FinMA.trajPMF_eq
#print axioms SuFunctor.Adequacy.su_ma_adequacy
#print axioms SuFunctor.Adequacy.su_ma_pathLaw_mem
#print axioms SuFunctor.Adequacy.su_ma_bottom
#print axioms SuFunctor.Adequacy.FinMA.pathLaw_ne_zero
#print axioms SuFunctor.Adequacy.su_ma_slice
