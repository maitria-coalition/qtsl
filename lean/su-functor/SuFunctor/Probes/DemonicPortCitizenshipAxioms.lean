import SuFunctor.Universe.DemonicPortCitizenship

/-! # Axiom audit for demonic-port citizenship

Prints the axiom footprint of the demonic-port citizenship module: the
radial-embedding engine (radiality, compactness, the credal-body
landing), the citizenship lemma and its piecewise and polynomial faces,
the packaging honesty pair (exact slice recovery; the raw image is
never a credal body), the non-convex witness chain (the quadratic curve
is a citizen, is not a convex body, and refutes the convex
strengthening), and the convexity-free composite-shape landings for
absorbed families.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

open SuFunctor.Universe.DemonicPort

#print axioms SuFunctor.Universe.DemonicPort.isRadial_scaleSegment
#print axioms SuFunctor.Universe.DemonicPort.isCompact_scaleSegment
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_of_isCompact
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_image
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_iUnion
#print axioms SuFunctor.Universe.DemonicPort.scaleSegment_iUnion
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_iUnion_image
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_polyImage
#print axioms SuFunctor.Universe.DemonicPort.sep_mass_one_scaleSegment_image
#print axioms SuFunctor.Universe.DemonicPort.not_isCredalBody_image_of_fullMass
#print axioms SuFunctor.Universe.DemonicPort.continuous_parabMap
#print axioms SuFunctor.Universe.DemonicPort.mass_parabMap
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_parabImage
#print axioms SuFunctor.Universe.DemonicPort.not_convexBody_scaleSegment_parabImage
#print axioms SuFunctor.Universe.DemonicPort.not_isConvexCredalBody_scaleSegment_parabImage
#print axioms SuFunctor.Universe.DemonicPort.not_isCredalBody_parabImage_raw
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_thinFamily_of_isCompact
#print axioms SuFunctor.Universe.DemonicPort.isCredalBody_scaleSegment_thinFamilyRate_of_isCompact
