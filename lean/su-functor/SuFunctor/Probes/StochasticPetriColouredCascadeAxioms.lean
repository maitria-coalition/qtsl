import SuFunctor.Adequacy.StochasticPetriColouredCascade

/-! # Axiom audit for the coloured stochastic-Petri cascade face

Prints the axiom footprint of the coloured immediate/cascade face:
the coloured vanishing/tangible classification and its equivalence,
the automaton reading with (transition, colour-vector) actions, the
uniform pair scheduler and the enabling-respect discipline, the
coloured cascade-rank certificate and its Zeno-freedom transfer, the
tangible chain with the initial-tangibility receipt, the compile
triangle, the square, the semantic-universe wiring, and the
controls.  Expected footprint for every entry: at most `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinCISPN.ofSum_toSum
#print axioms SuFunctor.Adequacy.FinCISPN.toSum_ofSum
#print axioms SuFunctor.Adequacy.FinCISPN.toSum_inr_val
#print axioms SuFunctor.Adequacy.FinCISPN.markingEquiv
#print axioms SuFunctor.Adequacy.FinCISPN.toFinMA_rate
#print axioms SuFunctor.Adequacy.FinCISPN.toFinMA_branch
#print axioms SuFunctor.Adequacy.FinCISPN.toFinMA_init
#print axioms SuFunctor.Adequacy.FinCISPN.enabledCount_pos
#print axioms SuFunctor.Adequacy.FinCISPN.uniformPolicy_respects
#print axioms SuFunctor.Adequacy.FinCISPN.zenoFree_of_cascadeRank
#print axioms SuFunctor.Adequacy.FinCISPN.zenoFree_uniform
#print axioms SuFunctor.Adequacy.FinCISPN.tangibleChain_eq
#print axioms SuFunctor.Adequacy.FinCISPN.tangiblePathLaw_eq
#print axioms SuFunctor.Adequacy.FinCISPN.tangibleChain_init_of_tangible
#print axioms SuFunctor.Adequacy.FinCISPN.compile_cispn_comm
#print axioms SuFunctor.Adequacy.FinCISPN.compileCispn_wf
#print axioms SuFunctor.Adequacy.FinCISPN.cispn_cascade_adequacy
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_cascade_adequacy
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_pathLaw_mem
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_bottom
#print axioms SuFunctor.Adequacy.FinCISPN.tangiblePathLaw_ne_zero
#print axioms SuFunctor.Adequacy.FinCISPN.su_cispn_slice
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_red_vanishing
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_mixed_vanishing
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_blue_tangible
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_cap_tangible
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_fire_20
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_fire_11
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_stay
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_rank
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_zenoFree
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_choice_20
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_choice_11
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_imStep_20
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_imStep_11
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_absorb_mid
#print axioms SuFunctor.Adequacy.CispnControls.cnet₁_cascade_absorb
#print axioms SuFunctor.Adequacy.CispnControls.cnet₂_count
#print axioms SuFunctor.Adequacy.CispnControls.cnet₂_pair_split
