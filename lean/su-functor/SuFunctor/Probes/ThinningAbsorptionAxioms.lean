import SuFunctor.Universe.ThinningAbsorption

/-! # Axiom audit for thinning absorption

Prints the axiom footprint of the thinning-absorption module: the
mass-one chart facts, the generator recovery pair, the envelope
preservation pair, the credal landing chain (Cozman, Richardson,
convex credal body, credal body — probability face and rate face), the
slice recovery, the honest negatives (no full-mass family is radial;
the packaging is not pointwise-down closed), and the endpoint probe
with its coupling divergence witness.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe.Thinning

#print axioms SuFunctor.Universe.Thinning.mass_thin
#print axioms SuFunctor.Universe.Thinning.mass_eq_one_of_mem_thinFamily
#print axioms SuFunctor.Universe.Thinning.extGen_thin
#print axioms SuFunctor.Universe.Thinning.extGen_thinRate
#print axioms SuFunctor.Universe.Thinning.extGen_image_thinFamilyRate
#print axioms SuFunctor.Universe.Thinning.sSup_extGen_thinFamilyRate
#print axioms SuFunctor.Universe.Thinning.thinFamily_nonempty
#print axioms SuFunctor.Universe.Thinning.isCompact_thinFamily
#print axioms SuFunctor.Universe.Thinning.isClosed_thinFamily
#print axioms SuFunctor.Universe.Thinning.convexBody_thinFamily
#print axioms SuFunctor.Universe.Thinning.isCozman_scaleSegment_thinFamily
#print axioms SuFunctor.Universe.Thinning.isRichardsonBody_scaleSegment_thinFamily
#print axioms SuFunctor.Universe.Thinning.isConvexCredalBody_scaleSegment_thinFamily
#print axioms SuFunctor.Universe.Thinning.isCredalBody_scaleSegment_thinFamily
#print axioms SuFunctor.Universe.Thinning.isCozman_scaleSegment_thinFamilyRate
#print axioms SuFunctor.Universe.Thinning.isCredalBody_scaleSegment_thinFamilyRate
#print axioms SuFunctor.Universe.Thinning.sep_mass_one_scaleSegment
#print axioms SuFunctor.Universe.Thinning.sep_mass_one_scaleSegment_thinFamily
#print axioms SuFunctor.Universe.Thinning.not_isRadial_of_forall_mass_eq_one
#print axioms SuFunctor.Universe.Thinning.not_isRadial_thinFamily
#print axioms SuFunctor.Universe.Thinning.not_ptwiseDown_scaleSegment_thinFamily_pair
#print axioms SuFunctor.Universe.Thinning.not_isUltra_scaleSegment_thinFamily_pair
#print axioms SuFunctor.Universe.Thinning.jumpGen_le_max_endpoint
#print axioms SuFunctor.Universe.Thinning.min_endpoint_le_jumpGen
#print axioms SuFunctor.Universe.Thinning.probe_coupling_diverges
#print axioms SuFunctor.Universe.Thinning.probe_coupling_fst
#print axioms SuFunctor.Universe.Thinning.probe_coupling_snd
