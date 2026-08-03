import SuFunctor.Site.WavyCoverage

/-! # Axiom audit for the wavy coverage

`#print axioms` receipts for the coverage stratum of the
temporal-type-theory site leg: the wavy ideal and halving lemmas, the
coverage and the closed form of its generated topology, the
zero-duration forcing theorem, the interior topology on windows, and
the morphism-of-sites package for the anchor quotient. -/

open SuFunctor.Site SuFunctor.Site.TTT

#print axioms SuFunctor.Site.TTT.wavy_map_iff
#print axioms SuFunctor.Site.TTT.Shave.Wavy.comp_left
#print axioms SuFunctor.Site.TTT.Shave.Wavy.comp_right
#print axioms SuFunctor.Site.TTT.Shave.Wavy.factor
#print axioms SuFunctor.Site.TTT.wavyCoverage
#print axioms SuFunctor.Site.TTT.wavyTopology
#print axioms SuFunctor.Site.TTT.wavyCoverage_toGrothendieck
#print axioms SuFunctor.Site.TTT.wavyTopology_zero
#print axioms SuFunctor.Site.TTT.flush_not_mem_generate_wavyFam
#print axioms SuFunctor.Site.TTT.bot_mem_of_le_wavy
#print axioms SuFunctor.Site.TTT.Window.StrictlyInterior.interpolate
#print axioms SuFunctor.Site.TTT.interiorTopology
#print axioms SuFunctor.Site.TTT.eq_of_le_of_gaps_eq
#print axioms SuFunctor.Site.TTT.coverPreserving_anchorQuot
#print axioms SuFunctor.Site.TTT.isCocontinuous_anchorQuot
#print axioms SuFunctor.Site.TTT.compatiblePreserving_anchorQuot
#print axioms SuFunctor.Site.TTT.isContinuous_anchorQuot
#print axioms SuFunctor.Site.TTT.mem_interiorTopology_iff
#print axioms SuFunctor.Site.TTT.isSheaf_zero_unique
