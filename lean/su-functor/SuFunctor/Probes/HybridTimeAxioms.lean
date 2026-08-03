import SuFunctor.Adequacy.HybridTime

/-! # Axiom audit for the hybrid-time pattern (assumption-slot semantics)

Prints the axiom footprint of the headline statements: the shared-site
finding, the schedule-genericity package, wall relaxation along the
assumption slot, properness under either slot, the semantic bite of
the duplicate-declaration refusal, and the hybrid-time square (lax
face, function-graph equality face with its tick-seam instance, and
the demonic separation with its wall-tier, model-class-tier, and
unwalled-incomparability witnesses).  Expected footprint for every
entry: within `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Spacetime.tickSite_pinned_eq_jittered
#print axioms SuFunctor.Spacetime.pinnedTickClock_real
#print axioms SuFunctor.Spacetime.jitteredTickClock_real_nontrivial
#print axioms SuFunctor.Spacetime.scheduleGeneric_iff
#print axioms SuFunctor.Spacetime.scheduleGeneric_transport
#print axioms SuFunctor.Spacetime.sampleWireWall_antitone
#print axioms SuFunctor.Spacetime.pinnedSeamSet_subset_tickSeamSet
#print axioms SuFunctor.Spacetime.pinnedWall_le_jitteredWall
#print axioms SuFunctor.Spacetime.pinnedWalled_modelClass_subset
#print axioms SuFunctor.Spacetime.tickSeamState_mem_pinned
#print axioms SuFunctor.Spacetime.exists_pinnedSeam_wall_eq_zero
#print axioms SuFunctor.Spacetime.tickJitteredState_mem_relaxed
#print axioms SuFunctor.Spacetime.tickJitteredState_notMem_pinned
#print axioms SuFunctor.Spacetime.exists_double_schedule_strictly_stronger
#print axioms SuFunctor.Spacetime.pinnedWall_strictly_above
#print axioms SuFunctor.Plain.suppIn_inter
#print axioms SuFunctor.Plain.possWall_sup
#print axioms SuFunctor.Spacetime.seam_perTickRows_subset_coarseRows
#print axioms SuFunctor.Spacetime.seam_coarseRows_subset_perTickRows_of_graph
#print axioms SuFunctor.Spacetime.seamWalled_modelClass_mono
#print axioms SuFunctor.Spacetime.hybridTime_square_subset
#print axioms SuFunctor.Spacetime.hybridTime_square_eq_of_graph
#print axioms SuFunctor.Spacetime.tickSeam_transport_eq
#print axioms SuFunctor.Spacetime.tickSeam_hybridTime_square_eq
#print axioms SuFunctor.Spacetime.demonicRows_scheduleGeneric
#print axioms SuFunctor.Spacetime.demonicState_mem
#print axioms SuFunctor.Spacetime.exists_demonic_gap
#print axioms SuFunctor.Spacetime.demonicWall_strictly_above
#print axioms SuFunctor.Spacetime.exists_hybridTime_square_strict
#print axioms SuFunctor.Spacetime.exists_unwalled_square_fails
