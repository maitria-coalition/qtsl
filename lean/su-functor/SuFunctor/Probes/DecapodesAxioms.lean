import SuFunctor.Decapodes.HeatCycle

/-! # Axiom audit for the Decapodes discrete tier

Prints the axiom footprint of the headline theorems of the schema +
lowering development and its heat-on-the-torus receipt: the lowering
soundness/completeness pair, the solution-set characterization and
its bijection form, the tangent/drift bridge, the
schedule-independence pair, and the receipt theorems (verbatim
stencil rows, the dissipation syzygy with its cone corollary,
constants-as-equilibria, and fused-presentation invariance).
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Decapodes

#print axioms SuFunctor.Decapodes.sat_generatedFrom
#print axioms SuFunctor.Decapodes.generated_of_sat
#print axioms SuFunctor.Decapodes.solSet_eq_range
#print axioms SuFunctor.Decapodes.solEquivState
#print axioms SuFunctor.Decapodes.tangent_eq_drift
#print axioms SuFunctor.Decapodes.driftRows_eval_unique
#print axioms SuFunctor.Decapodes.driftRows_unique
#print axioms SuFunctor.Decapodes.heatSchedule
#print axioms SuFunctor.Decapodes.heat_driftRows
#print axioms SuFunctor.Decapodes.heatDrift_eq
#print axioms SuFunctor.Decapodes.heat_dissipation
#print axioms SuFunctor.Decapodes.heat_dissipation_nonpos
#print axioms SuFunctor.Decapodes.heat_equilibrium
#print axioms SuFunctor.Decapodes.fusedSchedule
#print axioms SuFunctor.Decapodes.fused_driftRows_eq
