import SuFunctor.Adequacy.StochasticPetriSetFiring

/-! # Axiom audit for the set-firing stochastic-Petri face

Prints the axiom footprint of the simultaneous-composite-firing face:
the chain value identity, order-invariance and the pairwise diamond,
the composite firing and its chain equality, the reservation
precondition with the headroom discharge of the scope condition, the
packaged face, the automaton connective, and the controls.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`; the `decide`-grade
controls are expected axiom-free or `propext`-only. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinISPN.ifire_val
#print axioms SuFunctor.Adequacy.FinISPN.chainFire_val
#print axioms SuFunctor.Adequacy.FinISPN.chainFire_eq_of_enabled
#print axioms SuFunctor.Adequacy.FinISPN.ifire_comm
#print axioms SuFunctor.Adequacy.FinISPN.compositeOut_add_first
#print axioms SuFunctor.Adequacy.FinISPN.chainFire_eq_compositeFire
#print axioms SuFunctor.Adequacy.FinISPN.replicate_composite
#print axioms SuFunctor.Adequacy.FinISPN.iEnabled_of_reservation
#print axioms SuFunctor.Adequacy.FinISPN.chainEnabled_of_headroom
#print axioms SuFunctor.Adequacy.FinISPN.setNonConflicting_of_headroom
#print axioms SuFunctor.Adequacy.FinISPN.r1r3_composite_adequacy
#print axioms SuFunctor.Adequacy.FinISPN.toFinMA_branch_ifire
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c1_both_orders
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c1_composite
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c2_not_setNonConflicting
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c3_chain_enabled
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c3_composite_diverges
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c4_reservation_holds
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c4_not_setNonConflicting
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c5_value_identity_fails
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c6_reads_clause_fails
#print axioms SuFunctor.Adequacy.SpnSetFiringControls.c7_values_diverge
