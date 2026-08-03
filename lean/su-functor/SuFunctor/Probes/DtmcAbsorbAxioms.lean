import SuFunctor.Adequacy.DtmcAbsorb

/-! # Axiom audit for the DTMC absorption brackets

Prints the axiom footprint of the absorption-bracket module: the
forward measure evolution and its conservation facts, the duality
bridge to the path law, monotone absorption, the conservation bracket,
the correlated-ratio (posterior) bracket, the composed claim shape,
and the transfer-contraction induction with its `c = 1` subsumption of
the supermartingale consumption.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.massAt_nonneg
#print axioms SuFunctor.Adequacy.massAt_sum
#print axioms SuFunctor.Adequacy.massAt_dual
#print axioms SuFunctor.Adequacy.massOn_dual
#print axioms SuFunctor.Adequacy.dtmcAbsorb_mass_mono_step
#print axioms SuFunctor.Adequacy.dtmcAbsorb_mass_mono
#print axioms SuFunctor.Adequacy.dtmcAbsorbBracket_sound
#print axioms SuFunctor.Adequacy.dtmcPosteriorBracket_sound
#print axioms SuFunctor.Adequacy.dtmcAbsorb_eventual_bracket
#print axioms SuFunctor.Adequacy.massAt_expect_le_of_contraction
#print axioms SuFunctor.Adequacy.pathLaw_expect_le_of_genRow_nonpos
