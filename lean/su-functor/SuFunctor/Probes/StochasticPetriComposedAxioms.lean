import SuFunctor.Adequacy.StochasticPetriComposed

/-! # Axiom audit for the composed corollary of the commuting triangle

Prints the axiom footprint of the composed-corollary statements: the
law-level skeleton agreement, the pasted precise face, the two
composed directed faces, the connector and semantic-universe faces,
the exit-rate data agreement — and the witness tier: the composed
faces at the drain net, the flattened-side certificate computations,
and the consumption theorems in both verdict senses.  Expected
footprint for every entry: within `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Crd.entailsOfCell
#print axioms SuFunctor.Adequacy.FinISPN.flatten_skeleton_agreement_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_triangle_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_demonic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_angelic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_connector_agreement_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.su_flatten_composed_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_exitRate_agree_of_agree
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_skeleton_agreement
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_composed_triangle
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_composed_demonic
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_composed_angelic
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_su_composed
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_exitRate_agree
#print axioms SuFunctor.Adequacy.SpnComposedWitness.ωd_zero
#print axioms SuFunctor.Adequacy.SpnComposedWitness.ωd_one
#print axioms SuFunctor.Adequacy.SpnComposedWitness.ωe_zero
#print axioms SuFunctor.Adequacy.SpnComposedWitness.ωe_one
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_relabel_init_T20
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_relabel_rate_T20_T00
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_relabel_rate_T20_T10
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_exit_T20
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_step_T20_T00
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_step_T20_T10
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_drain_weight
#print axioms SuFunctor.Adequacy.SpnComposedWitness.flat_evap_weight
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_token_game_drain
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_angelic_drain
#print axioms SuFunctor.Adequacy.SpnComposedWitness.wnet_demonic_mass
#print axioms SuFunctor.Adequacy.SpnComposedWitness.witness_flat_mass_via_demonic
