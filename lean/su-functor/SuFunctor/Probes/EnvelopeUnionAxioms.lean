import SuFunctor.Adequacy.EnvelopeUnion

/-! # Axiom audit for the set-valued envelope stratum

Prints the axiom footprint of the headline theorems of the
union-of-rays slice reconciliation and its verdict transfer.  Expected
footprint for every entry: `propext`, `Classical.choice`, `Quot.sound`
— the standard three, no `sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.SubPMF.eq_zero_of_mass_eq_zero
#print axioms SuFunctor.unionRays_self
#print axioms SuFunctor.unionSingletons_self
#print axioms SuFunctor.unionSingletons_le_unionRays
#print axioms SuFunctor.unionRays_zero_iff
#print axioms SuFunctor.maxSlice_unionRays_subset
#print axioms SuFunctor.mem_maxSlice_unionRays
#print axioms SuFunctor.maxSlice_unionRays
#print axioms SuFunctor.maxSlice_unionSingletons
#print axioms SuFunctor.maxSlice_unionRays_mass_zero
#print axioms SuFunctor.satCredal_lower_unionRays
#print axioms SuFunctor.satCredal_lower_unionSingletons
#print axioms SuFunctor.satCredal_upper_unionRays
#print axioms SuFunctor.satCredal_upper_unionSingletons
#print axioms SuFunctor.satCredal_lower_union_ray_singleton
#print axioms SuFunctor.satCredal_upper_union_ray_singleton
#print axioms SuFunctor.unionSingletons_halfPair
#print axioms SuFunctor.not_maxSlice_unionRays_halfPair
#print axioms SuFunctor.union_ray_singleton_reconciliation
