import SuFunctor.Adequacy.SolutionSetMesh

/-! # Axiom audit for the solution-set mesh

Prints the axiom footprint of the headline theorems of the first
`FellDescentEqualizer` consumer: the descent instantiation at the ring
cover, the tube-citizenship transport, the ℤ-orbit holonomy witness
with its wall-satisfaction and control partners, the local-character
refutation, the one-sided compiled square with its free-con witness,
the labelled positive face, and the record-tier ⊥-forcing shadow.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Universe.FellCloseds.IsLocalLocusEq.glue_mem
#print axioms SuFunctor.Adequacy.RingMesh.iUnion_arc
#print axioms SuFunctor.Adequacy.iUnion_arcRegion
#print axioms SuFunctor.Adequacy.meshDescent
#print axioms SuFunctor.Adequacy.meshGlue_toEqualizer
#print axioms SuFunctor.Adequacy.toEqualizer_meshGlue
#print axioms SuFunctor.Adequacy.isCellTube_clip
#print axioms SuFunctor.Adequacy.tubeWrapWall_of_torusTube
#print axioms SuFunctor.Adequacy.isTorusTube_univ
#print axioms SuFunctor.Adequacy.labelled_ensembles_glue
#print axioms SuFunctor.Adequacy.heatAt_linZ
#print axioms SuFunctor.Adequacy.isClosed_orbitTube
#print axioms SuFunctor.Adequacy.isCellTube_orbit
#print axioms SuFunctor.Adequacy.orbitEq_wrapWall
#print axioms SuFunctor.Adequacy.not_tubeWrap_singleLin
#print axioms SuFunctor.Adequacy.orbitTube_is_chartTube
#print axioms SuFunctor.Adequacy.thread_const
#print axioms SuFunctor.Adequacy.contOn_slice
#print axioms SuFunctor.Adequacy.orbitTube_not_torusTube
#print axioms SuFunctor.Adequacy.setStratum_holonomy
#print axioms SuFunctor.Adequacy.not_isLocalLocusEq_torusTube
#print axioms SuFunctor.Adequacy.tubeAtoms_of_classical
#print axioms SuFunctor.Adequacy.solset_forward_cell
#print axioms SuFunctor.Adequacy.tubeAtoms_consistent
#print axioms SuFunctor.Adequacy.topTube_classical
#print axioms SuFunctor.Adequacy.tubeAtoms_not_classical
#print axioms SuFunctor.Adequacy.meshSols_inter_orbitEnclosure
#print axioms SuFunctor.Adequacy.orbit_enclosure_forces_zero
