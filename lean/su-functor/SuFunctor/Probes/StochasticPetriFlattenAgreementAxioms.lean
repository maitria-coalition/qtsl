import SuFunctor.Adequacy.StochasticPetriFlattenAgreement

/-! # Axiom audit for the former-level flattening-agreement cell

Prints the axiom footprint of the flattening construction, the derived
atom-transport agreement (rate rows and initial rows), the discharged
precise-face tier (triangle, skeleton agreement, composed corollary,
connector, semantic-universe, exit-rate faces), the discharged directed
tier (both directed cells, both verdict transfers, both composed
directed faces), the premise-bundle entry points, and the witness tier
(the construction reproducing the hand-written flattening; the
composed corollary and the flattened-side certificate at zero
hypotheses).  Expected footprint for every entry: within `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

#print axioms SuFunctor.Adequacy.FinCTMC.relabel_refl
#print axioms SuFunctor.Adequacy.FinISPN.flattenChain
#print axioms SuFunctor.Adequacy.FinISPN.flattenChain_rate
#print axioms SuFunctor.Adequacy.FinISPN.flattenChain_init
#print axioms SuFunctor.Adequacy.FinISPN.flattenChain_agree_off
#print axioms SuFunctor.Adequacy.FinISPN.flattenChain_agree_init
#print axioms SuFunctor.Adequacy.FinISPN.flatten_triangle
#print axioms SuFunctor.Adequacy.FinISPN.flatten_skeleton_agreement
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_triangle
#print axioms SuFunctor.Adequacy.FinISPN.flatten_connector_agreement
#print axioms SuFunctor.Adequacy.FinISPN.su_flatten_composed
#print axioms SuFunctor.Adequacy.FinISPN.flatten_exitRate_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_demonic_directed
#print axioms SuFunctor.Adequacy.FinISPN.flatten_angelic_directed
#print axioms SuFunctor.Adequacy.FinISPN.flatten_demonic_verdict
#print axioms SuFunctor.Adequacy.FinISPN.flatten_angelic_witness
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_demonic_directed
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_angelic_directed
#print axioms SuFunctor.Adequacy.FinISPN.flatten_skeleton_agreement_of_premises
#print axioms SuFunctor.Adequacy.FinISPN.flatten_composed_triangle_of_premises
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_flattenChain_drain
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_flattenChain_evap
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_flattenChain_agree_hand_off
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_flattenChain_agree_hand_init
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_composed_triangle_constructed
#print axioms SuFunctor.Adequacy.SpnFlattenAgreeWitness.wnet_drain_weight_constructed
