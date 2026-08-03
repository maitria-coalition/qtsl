import SuFunctor.Adequacy.Envelope

/-! # Axiom audit for the envelope stratum

Prints the axiom footprint of the headline theorems of the
ray-vs-singleton reconciliation and the kind-selected credal
satisfaction.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

open SuFunctor

#print axioms SuFunctor.SubPMF.prob_of_wt_smul
#print axioms SuFunctor.SubPMF.mass_scale
#print axioms SuFunctor.SubPMF.dirac_ne_zero
#print axioms SuFunctor.smul_wt_cancel
#print axioms SuFunctor.singletonC_le_rayC
#print axioms SuFunctor.maxSlice_rayC
#print axioms SuFunctor.maxSlice_rayC_zero
#print axioms SuFunctor.maxSlice_rayC_empty_iff
#print axioms SuFunctor.maxSlice_singletonC
#print axioms SuFunctor.rayC_eq_singletonC_iff
#print axioms SuFunctor.downClosed_leC
#print axioms SuFunctor.satCredal_lower_rayC
#print axioms SuFunctor.satCredal_lower_singletonC
#print axioms SuFunctor.satCredal_upper_singletonC
#print axioms SuFunctor.satCredal_upper_rayC
#print axioms SuFunctor.satCredal_lower_ray_singleton
#print axioms SuFunctor.satCredal_upper_ray_singleton
#print axioms SuFunctor.not_satCredal_upper_rayC_geC
#print axioms SuFunctor.satCredal_lower_rayC_geC
#print axioms SuFunctor.ray_singleton_reconciliation
