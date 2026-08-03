import SuFunctor.TokenGame
import SuFunctor.Adequacy.StochasticPetri

/-! # Axiom audit for the stochastic-Petri adequacy square

Prints the axiom footprint of the statics square (the tuple-bag
combinatorics, the vertical identification, the split denotation, the
firing correspondence, the monotonicity warrant, the init and
race-aggregation faces) and of the delay-race face at the finite
time-abstract stratum (the census ties, the dictionary triangle, the
square, the thinning receipt, and the semantic-universe wiring).
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.TokenGame SuFunctor.Adequacy

#print axioms SuFunctor.TokenGame.tupleBag_card
#print axioms SuFunctor.TokenGame.tupleBag_eq_ofFn
#print axioms SuFunctor.TokenGame.univ_val_sum_type
#print axioms SuFunctor.TokenGame.tupleBag_elim_equiv
#print axioms SuFunctor.TokenGame.tupleBag_comp_le
#print axioms SuFunctor.TokenGame.netBag_card
#print axioms SuFunctor.TokenGame.powBag_surjective
#print axioms SuFunctor.TokenGame.exists_state_of_placeTuples
#print axioms SuFunctor.TokenGame.netBag_surjective
#print axioms SuFunctor.TokenGame.netBag_eq_iff
#print axioms SuFunctor.TokenGame.initMarking_realized
#print axioms SuFunctor.TokenGame.powBag_split
#print axioms SuFunctor.TokenGame.res_tokenIncl_placeIncl
#print axioms SuFunctor.TokenGame.step_iff_fireWitness
#print axioms SuFunctor.TokenGame.enabled_mono
#print axioms SuFunctor.TokenGame.sum_tokens_eq_bag_sum
#print axioms SuFunctor.TokenGame.sum_tokens_exchange
#print axioms SuFunctor.Adequacy.FinSPN.raceCount_eq_card_embeddings
#print axioms SuFunctor.Adequacy.FinSPN.raceCount_eq_dict
#print axioms SuFunctor.Adequacy.FinSPN.raceRate_nonneg
#print axioms SuFunctor.Adequacy.FinSPN.compile_race_comm
#print axioms SuFunctor.Adequacy.FinSPN.spn_delay_adequacy
#print axioms SuFunctor.Adequacy.FinSPN.spn_jumpLaw_thinning
#print axioms SuFunctor.Adequacy.FinSPN.su_spn_delay_adequacy
#print axioms SuFunctor.Adequacy.FinSPN.su_spn_jumpLaw_mem
#print axioms SuFunctor.Adequacy.FinSPN.su_spn_bottom
#print axioms SuFunctor.Adequacy.FinSPN.su_spn_slice
