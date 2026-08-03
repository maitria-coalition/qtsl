import SuFunctor.Adequacy.HeatTorusInit

/-! # Axiom audit for the initial-face port on the heat torus

Prints the axiom footprint of the headline declarations of the ported
square: the trace row's transport, the concrete face's filter fee, the
bundling lemma, the corner-condition analogue at both tiers, the
ported wiring theorem and square, the conditional con discharge, the
constructive feeds (equilibria and the single Fourier mode, with the
mode's non-equilibrium witness), and the load-bearing-port pair.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.InitTraceOn.congr
#print axioms SuFunctor.Adequacy.initFace_neBot
#print axioms SuFunctor.Adequacy.heatInitAtoms_iff
#print axioms SuFunctor.Adequacy.initFace_wrap_compat
#print axioms SuFunctor.Adequacy.IsHeatTorusSolInit.trace_wrap_compat
#print axioms SuFunctor.Adequacy.RingMesh.mem_arc_of_mem_chart
#print axioms SuFunctor.Adequacy.meshInitSols_eq_classical
#print axioms SuFunctor.Adequacy.heat_init_adequacy
#print axioms SuFunctor.Adequacy.heatInitAtoms_consistent_of_feed
#print axioms SuFunctor.Adequacy.portFeed_const
#print axioms SuFunctor.Adequacy.modeField_hasDerivAt_x
#print axioms SuFunctor.Adequacy.modeField_hasDerivAt_x2
#print axioms SuFunctor.Adequacy.modeField_hasDerivAt_t
#print axioms SuFunctor.Adequacy.heatAt_mode
#print axioms SuFunctor.Adequacy.modeField_periodic
#print axioms SuFunctor.Adequacy.modeField_trace
#print axioms SuFunctor.Adequacy.portFeed_mode
#print axioms SuFunctor.Adequacy.modeDatum_ne_const
#print axioms SuFunctor.Adequacy.not_init1_const
#print axioms SuFunctor.Adequacy.heatAtoms_not_pin_port
