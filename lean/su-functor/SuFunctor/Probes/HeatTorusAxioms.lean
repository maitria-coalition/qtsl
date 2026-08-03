import SuFunctor.Adequacy.HeatTorus

/-! # Axiom audit for the heat-on-torus mesh square

Prints the axiom footprint of the headline theorems of the cyclic-mesh
instance: the locality engine, the chain paste (m2's positive
control), the ring glue (the con-obligation discharge), the bundling
lemma, the wiring theorem, the square, the consistency and holonomy
witnesses with their no-repair partners, the two-ring contrast, the
credal contrast, and the compositor's order-independence.  Expected
footprint for every entry: `propext`, `Classical.choice`, `Quot.sound`
— the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Universe.CylPt.mk_lt_mk_of_time_lt
#print axioms SuFunctor.Universe.CylPt.isAntichain_timeSlice
#print axioms SuFunctor.Universe.CylPt.punitOrderIso
#print axioms SuFunctor.Adequacy.HeatAt.congr
#print axioms SuFunctor.Adequacy.HeatAt.comp_sub_const
#print axioms SuFunctor.Adequacy.paste_isHeatSol
#print axioms SuFunctor.Adequacy.heat_chain_glues
#print axioms SuFunctor.Adequacy.periodize_germ
#print axioms SuFunctor.Adequacy.periodize_isHeatSol
#print axioms SuFunctor.Adequacy.heat_mesh_glues
#print axioms SuFunctor.Adequacy.heatAtoms_iff
#print axioms SuFunctor.Adequacy.meshSols_eq_classical
#print axioms SuFunctor.Adequacy.heat_adequacy
#print axioms SuFunctor.Adequacy.heatAtoms_consistent
#print axioms SuFunctor.Adequacy.chainAtoms_dirac_lin
#print axioms SuFunctor.Adequacy.not_wrap_lin
#print axioms SuFunctor.Adequacy.no_periodic_glue_lin
#print axioms SuFunctor.Adequacy.not_seam12_mismatch
#print axioms SuFunctor.Adequacy.no_glue_mismatch
#print axioms SuFunctor.Adequacy.heat_ring_glues_vorobev_ring_not
#print axioms SuFunctor.Adequacy.credalCompile_heatAtoms_ne_bot
#print axioms SuFunctor.looseConj_perm
#print axioms SuFunctor.Adequacy.heatAtoms_order_independent
#print axioms SuFunctor.Adequacy.heatAtoms_dirac_of_torusSol
#print axioms SuFunctor.Adequacy.diracC_heatRecOf_entails_heat
#print axioms SuFunctor.Adequacy.isHeatTorusSol_const
