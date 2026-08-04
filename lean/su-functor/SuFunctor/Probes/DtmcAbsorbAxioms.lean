import SuFunctor.Adequacy.DtmcAbsorb

/-! # Axiom audit for the DTMC absorption brackets

Prints the axiom footprint of the absorption-bracket module: the
forward measure evolution and its conservation facts, the duality
bridge to the path law, monotone absorption (via monotone mass on
forward-closed sets), the conservation bracket, the
reachability-sharpened bracket with its subsumption lemma and
strict-improvement witness, the correlated-ratio (posterior) bracket,
the composed claim shapes, and the transfer-contraction induction
with its `c = 1` subsumption of the supermartingale consumption.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

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

/- The reachability sharpening (revision-event cargo on
`DtmcAbsorbBracket`): forward-closed monotonicity, the sharpened
bracket, subsumption against the incumbent residual, the sharpened
claim shape, and the strict-improvement witness. -/

#print axioms SuFunctor.Adequacy.dtmc_mass_mono_step_of_forwardClosed
#print axioms SuFunctor.Adequacy.dtmc_mass_mono_of_forwardClosed
#print axioms SuFunctor.Adequacy.FinDTMC.eq_of_absorbing_step
#print axioms SuFunctor.Adequacy.FinDTMC.forwardClosed_of_absorbing
#print axioms SuFunctor.Adequacy.FinDTMC.Reaches.mem_of_absorbing
#print axioms SuFunctor.Adequacy.FinDTMC.forwardClosed_compl_reachSet
#print axioms SuFunctor.Adequacy.dtmcAbsorb_mass_le_reach
#print axioms SuFunctor.Adequacy.dtmcAbsorbBracket_reach_sound
#print axioms SuFunctor.Adequacy.dtmcAbsorb_reach_residual_le
#print axioms SuFunctor.Adequacy.dtmcAbsorb_eventual_bracket_reach
#print axioms SuFunctor.Adequacy.idBool_massOn_true
#print axioms SuFunctor.Adequacy.idBool_incumbent_residual
#print axioms SuFunctor.Adequacy.idBool_sharp_residual
#print axioms SuFunctor.Adequacy.idBool_strict_improvement
