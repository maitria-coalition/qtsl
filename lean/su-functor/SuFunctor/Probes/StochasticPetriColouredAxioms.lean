import SuFunctor.Adequacy.StochasticPetriColoured

/-! # Axiom audit for the coloured stochastic-Petri delay face

Prints the axiom footprint of the coloured formation and its
delay-race face: the coloured census layer and its dictionary, the
race chain, the compile triangle, the square, the semantic-universe
wiring, the unit-colour degeneracy suite, and the controls.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.Coloured.census_eq_dict
#print axioms SuFunctor.Adequacy.Coloured.census_eq_card_embeddings
#print axioms SuFunctor.Adequacy.FinCSPN.raceCount_eq_dict
#print axioms SuFunctor.Adequacy.FinCSPN.raceCount_eq_card_embeddings
#print axioms SuFunctor.Adequacy.FinCSPN.raceRate_nonneg
#print axioms SuFunctor.Adequacy.FinCSPN.raceRate_eq_zero_of_not_enabled
#print axioms SuFunctor.Adequacy.FinCSPN.raceCtmc
#print axioms SuFunctor.Adequacy.FinCSPN.compileCspn
#print axioms SuFunctor.Adequacy.FinCSPN.compile_race_comm
#print axioms SuFunctor.Adequacy.FinCSPN.cspn_delay_adequacy
#print axioms SuFunctor.Adequacy.FinCSPN.cspn_jumpLaw_thinning
#print axioms SuFunctor.Adequacy.FinCSPN.cspnDnf
#print axioms SuFunctor.Adequacy.FinCSPN.su_cspn_delay_adequacy
#print axioms SuFunctor.Adequacy.FinCSPN.su_cspn_jumpLaw_mem
#print axioms SuFunctor.Adequacy.FinCSPN.su_cspn_bottom
#print axioms SuFunctor.Adequacy.FinCSPN.su_cspn_slice
#print axioms SuFunctor.Adequacy.unitMarkingEquiv
#print axioms SuFunctor.Adequacy.FinSPN.toColoured
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_vecDemand
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_consCount
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_prodCount
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_outAt
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_raceCount
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_dict
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_enabled_iff
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_fire
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_init
#print axioms SuFunctor.Adequacy.FinSPN.toColoured_raceRate
#print axioms SuFunctor.Adequacy.CspnControls.cnetR_fire_flip
#print axioms SuFunctor.Adequacy.CspnControls.cnetR_full_blocked
#print axioms SuFunctor.Adequacy.CspnControls.cnetR_capacity
#print axioms SuFunctor.Adequacy.CspnControls.cnetR_rate_red
#print axioms SuFunctor.Adequacy.CspnControls.cnetR_rate_blue
#print axioms SuFunctor.Adequacy.CspnControls.cnetG_blue_blocked
#print axioms SuFunctor.Adequacy.CspnControls.cnetG_gate
