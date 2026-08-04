import SuFunctor.Adequacy.ProbProg

/-! # Axiom audit for the probabilistic-programs square

Prints the axiom footprint of the former-level square: the real face
of an exact-rational law with its injectivity, the unrolled text's
measurability, the text-equals-iterate law, the profile theorem, the
presentation transfer, and the wired square with its positive face,
ex-falso corner, and fair-coin specimen.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.SubPMF.probFun_injective
#print axioms SuFunctor.Adequacy.measurable_snoc
#print axioms SuFunctor.Adequacy.measurable_progTraj
#print axioms SuFunctor.Adequacy.noiseDenot_progTraj
#print axioms SuFunctor.Adequacy.pathDist_profile
#print axioms SuFunctor.Adequacy.pathDist_presents
#print axioms SuFunctor.Adequacy.pathLaw_probFun_eq
#print axioms SuFunctor.Adequacy.su_pprog_adequacy
#print axioms SuFunctor.Adequacy.su_pprog_pathLaw_mem
#print axioms SuFunctor.Adequacy.su_pprog_bottom
#print axioms SuFunctor.Adequacy.fairStep_presents
#print axioms SuFunctor.Adequacy.su_fairStep_adequacy
