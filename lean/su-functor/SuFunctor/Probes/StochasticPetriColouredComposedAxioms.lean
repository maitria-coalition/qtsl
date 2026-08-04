import SuFunctor.Adequacy.StochasticPetriColouredComposed

/-! # Axiom audit for the coloured composed corollary

Prints the axiom footprint of the coloured premise rows (initial
tangibility, the colour-indexed token bound, the reachability bound),
the interface tier (triangle, skeleton agreement, composed corollary,
connector, semantic-universe, exit-rate faces, from agreement), the
flattening construction and its derived agreement, the discharged
tier, the premise-bundle entry points, and the witness tier (the
coloured classification, the rank certificate, the flattened-side
certificate, and the composed corollary consumed as token-game
verdicts).  Expected footprint for every entry: within `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

#print axioms SuFunctor.Adequacy.Coloured.consCount_le_vecDemand
#print axioms SuFunctor.Adequacy.FinCISPN.tangibleChain_init_eq_of_tangibleInit
#print axioms SuFunctor.Adequacy.FinCISPN.fire_val_of_enabled
#print axioms SuFunctor.Adequacy.FinCISPN.ifire_val_of_enabled
#print axioms SuFunctor.Adequacy.FinCISPN.cwsum_fire_le
#print axioms SuFunctor.Adequacy.FinCISPN.cwsum_ifire_le
#print axioms SuFunctor.Adequacy.FinCISPN.cwsum_le_of_reach
#print axioms SuFunctor.Adequacy.FinCISPN.count_le_of_reach
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_triangle_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_skeleton_agreement_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_triangle_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_connector_agreement_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.su_flatten_composed_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_exitRate_agree_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flattenChain
#print axioms SuFunctor.Adequacy.FinCISPN.flattenChain_agree_off
#print axioms SuFunctor.Adequacy.FinCISPN.flattenChain_agree_init
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_triangle
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_skeleton_agreement
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_triangle
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_connector_agreement
#print axioms SuFunctor.Adequacy.FinCISPN.su_flatten_composed
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_exitRate_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_skeleton_agreement_of_premises
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_triangle_of_premises
#print axioms SuFunctor.Adequacy.CspnComposedWitness.cwnet_t11
#print axioms SuFunctor.Adequacy.CspnComposedWitness.cwnet_t22
#print axioms SuFunctor.Adequacy.CspnComposedWitness.cwnet_rank
#print axioms SuFunctor.Adequacy.CspnComposedWitness.cwnet_zenoFree
#print axioms SuFunctor.Adequacy.CspnComposedWitness.cwnet_bound
#print axioms SuFunctor.Adequacy.CspnComposedWitness.fexit_11
#print axioms SuFunctor.Adequacy.CspnComposedWitness.fstep_11_10
#print axioms SuFunctor.Adequacy.CspnComposedWitness.fstep_11_20
#print axioms SuFunctor.Adequacy.CspnComposedWitness.fdrain_weight
#print axioms SuFunctor.Adequacy.CspnComposedWitness.witness_token_game_drain
#print axioms SuFunctor.Adequacy.CspnComposedWitness.witness_token_game_flip
#print axioms SuFunctor.Adequacy.CspnComposedWitness.witness_composed_triangle
#print axioms SuFunctor.Adequacy.CspnComposedWitness.witness_composed_of_premises
