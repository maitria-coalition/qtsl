import SuFunctor.Adequacy.StochasticPetriCascade

/-! # Axiom audit for the immediate/cascade stochastic-Petri face

Prints the axiom footprint of the immediate-transition/cascade face of
the stochastic-Petri adequacy story: the vanishing/tangible
classification and its equivalence, the automaton reading of the net,
the uniform scheduler and the enabling-respect discipline, the
cascade-rank certificate and its Zeno-freedom transfer, the tangible
chain with the initial-tangibility receipt, the compile triangle, the
square, the semantic-universe wiring, and the controls.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinISPN.ofSum_toSum
#print axioms SuFunctor.Adequacy.FinISPN.toSum_ofSum
#print axioms SuFunctor.Adequacy.FinISPN.toFinMA_rate
#print axioms SuFunctor.Adequacy.FinISPN.toFinMA_branch
#print axioms SuFunctor.Adequacy.FinISPN.toFinMA_init
#print axioms SuFunctor.Adequacy.FinISPN.enabledCount_pos
#print axioms SuFunctor.Adequacy.FinISPN.uniformPolicy_respects
#print axioms SuFunctor.Adequacy.FinISPN.zenoFree_of_cascadeRank
#print axioms SuFunctor.Adequacy.FinISPN.zenoFree_uniform
#print axioms SuFunctor.Adequacy.FinISPN.tangibleChain_eq
#print axioms SuFunctor.Adequacy.FinISPN.tangiblePathLaw_eq
#print axioms SuFunctor.Adequacy.FinISPN.tangibleChain_init_of_tangible
#print axioms SuFunctor.Adequacy.FinISPN.compile_ispn_comm
#print axioms SuFunctor.Adequacy.FinISPN.compileIspn_wf
#print axioms SuFunctor.Adequacy.FinISPN.ispn_cascade_adequacy
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_cascade_adequacy
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_pathLaw_mem
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_bottom
#print axioms SuFunctor.Adequacy.FinISPN.tangiblePathLaw_ne_zero
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_slice
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_vanishing
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_tangible
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_rank
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_zenoFree
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_uniform_choice
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_singleton_renorm
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_enabling_filter
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_race_to_vanishing
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_absorb_i10
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_uniform_split
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_thinning
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₁_stay_branch
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_rank
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_zenoFree
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_imStep_move
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_imStep_consume
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_absorb_mid
#print axioms SuFunctor.Adequacy.SpnCascadeControls.net₂_cascade_absorb
