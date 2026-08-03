import SuFunctor.Adequacy.PetriVanilla

/-! # Axiom audit for the vanilla-Petri adequacy square

Prints the axiom footprint of the headline theorems of the vanilla
place/transition species: the run model's derived enabledness, both
legs of the interleaving square, the dwell-uniformity corollary, the
stabilization glue, the record-space layer (trajectory laws, the
definitional feeding lemma, the slice reconciliation, the verdict
transfers), the semantic-universe wiring, the possibilistic retract
identification, and the two control nets.  Expected footprint for every
entry: within `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.PetriVanilla.DemonicRun.enabled_at
#print axioms SuFunctor.Adequacy.PetriVanilla.marks_reach
#print axioms SuFunctor.Adequacy.PetriVanilla.face_sound
#print axioms SuFunctor.Adequacy.PetriVanilla.DemonicRun.extend
#print axioms SuFunctor.Adequacy.PetriVanilla.reach_endrun
#print axioms SuFunctor.Adequacy.PetriVanilla.face_complete
#print axioms SuFunctor.Adequacy.PetriVanilla.face_eq_reach
#print axioms SuFunctor.Adequacy.PetriVanilla.face_dwell_uniform
#print axioms SuFunctor.Adequacy.PetriVanilla.marks_stab
#print axioms SuFunctor.Adequacy.PetriVanilla.dirac_wt_ne_zero_iff
#print axioms SuFunctor.Adequacy.PetriVanilla.DemonicRun.law_mass
#print axioms SuFunctor.Adequacy.PetriVanilla.vanillaDemonicLaws_iff
#print axioms SuFunctor.Adequacy.PetriVanilla.vanillaDemonicC_iff
#print axioms SuFunctor.Adequacy.PetriVanilla.vanilla_demonic_adequacy
#print axioms SuFunctor.Adequacy.PetriVanilla.vanilla_demonic_maxSlice
#print axioms SuFunctor.Adequacy.PetriVanilla.satCredal_lower_vanillaDemonicCredal
#print axioms SuFunctor.Adequacy.PetriVanilla.satCredal_upper_vanillaDemonicCredal
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_demonic_adequacy
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_demonic_mem
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_demonic_bottom
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_demonic_slice
#print axioms SuFunctor.Adequacy.PetriVanilla.recordVisited_eq_face
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_face_eq_reach
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_reach_iff
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_dwell_uniform
#print axioms SuFunctor.Adequacy.PetriVanilla.su_vanilla_safety
#print axioms SuFunctor.Adequacy.PetriVanillaControls.toggle_reach_iff
#print axioms SuFunctor.Adequacy.PetriVanillaControls.toggle_onesafe
#print axioms SuFunctor.Adequacy.PetriVanillaControls.su_toggle_visited
#print axioms SuFunctor.Adequacy.PetriVanillaControls.su_toggle_onesafe
#print axioms SuFunctor.Adequacy.PetriVanillaControls.source_reach
#print axioms SuFunctor.Adequacy.PetriVanillaControls.su_source_unbounded
