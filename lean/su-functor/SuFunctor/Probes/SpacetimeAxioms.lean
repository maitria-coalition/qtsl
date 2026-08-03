import SuFunctor.Spacetime.Base
import SuFunctor.Spacetime.Universe
import SuFunctor.Spacetime.Walls

/-! # Axiom audit for the spacetime tier

Prints the axiom footprint of the headline declarations of the
spacetime-site dimension: the profiled base and its double-category
structure, the site-fibration facts, the profile-forgetting embedding,
the iterated total with its opfibration projection, the per-site
conservativity equivalences, and the generic wall conjuncts.  Expected
footprint for every entry: at most `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Spacetime SuFunctor.Universe

-- the profiled base
#print axioms SuFunctor.Spacetime.instPseudoDoubleCategory
#print axioms SuFunctor.Spacetime.compFst_tot_hComp
#print axioms SuFunctor.Spacetime.compSnd_tot_lAssoc

-- the site-fibration facts (interfaces over site-profiles)
#print axioms SuFunctor.Spacetime.profile_eq_of_identified
#print axioms SuFunctor.Spacetime.profileLiftHom
#print axioms SuFunctor.Spacetime.profile_unique_of_hom

-- the profile-forgetting embedding
#print axioms SuFunctor.Spacetime.profiledEmbed
#print axioms SuFunctor.Spacetime.profiledEmbed_faithful_tight

-- the iterated total
#print axioms SuFunctor.Spacetime.spacetimeSpecFunctor
#print axioms SuFunctor.Spacetime.spacetimeSpecFunctor_fibre_eq
#print axioms SuFunctor.Spacetime.spacetimeSpecFunctor_map_eq
#print axioms SuFunctor.Spacetime.semanticUniverse_pseudoDoubleCategory
#print axioms SuFunctor.Spacetime.universeProj_isPseudo
#print axioms SuFunctor.Spacetime.universeProj_discreteOpfibration

-- per-site conservativity
#print axioms SuFunctor.Spacetime.constStates
#print axioms SuFunctor.Spacetime.constHomEquiv
#print axioms SuFunctor.Spacetime.constPatEquiv
#print axioms SuFunctor.Spacetime.constPatEquiv_id_pointwise
#print axioms SuFunctor.Spacetime.constPatEquiv_comp_pointwise
#print axioms SuFunctor.Spacetime.siteRead

-- walls: seams as conjuncts in the fibres
#print axioms SuFunctor.Universe.SpecAtom.mem_modelClass_withWall
#print axioms SuFunctor.Universe.SpecDnf.mem_modelClass_withWall

-- per-site conservativity, packaged (successor S2)
#print axioms SuFunctor.Spacetime.constProfile
#print axioms SuFunctor.Spacetime.constProfile_map_eq
#print axioms SuFunctor.Spacetime.constProfile_mapLoose_eq
#print axioms SuFunctor.Spacetime.constProfile_isPseudo

-- wall instances (successor S1): the indicator wall's order lemmas
#print axioms SuFunctor.Plain.possWall_le_iff
#print axioms SuFunctor.Plain.possWall_antitone
#print axioms SuFunctor.Universe.SpecDnf.withWall_modelClass_antitone

-- the profile pin
#print axioms SuFunctor.Spacetime.profilePinSet_eq_range
#print axioms SuFunctor.Spacetime.mem_modelClass_withWall_profilePin

-- the bundled SampleWire wall
#print axioms SuFunctor.Spacetime.sampleWireSet_ports_transport
#print axioms SuFunctor.Spacetime.sampleWireSet_subset_perPortSampleSet
#print axioms SuFunctor.Spacetime.sampleWireSet_subset_coarseClockPin
#print axioms SuFunctor.Spacetime.sampleWire_entails_coarseClockPin
#print axioms SuFunctor.Spacetime.sampleWire_union_refinement_iff

-- the tick seam (the premium's clocks, inside the fibres)
#print axioms SuFunctor.Spacetime.tickSeamState_mem
#print axioms SuFunctor.Spacetime.exists_tickSeam_wall_eq_zero
#print axioms SuFunctor.Spacetime.tickTwoPortState_mem_perPort
#print axioms SuFunctor.Spacetime.tickTwoPortState_notMem_bundled
#print axioms SuFunctor.Spacetime.exists_unwalled_leak
