import SuFunctor.Adequacy.MarginalGlue

/-! # Axiom audit for the marginal-glue obstruction

Prints the axiom footprint of the headline theorems of the Vorob'ev
non-gluability instance, its controls, and its credal absorption.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.SubPMF.push_wt_sum
#print axioms SuFunctor.SubPMF.ofFun_wt
#print axioms SuFunctor.pairCorr_fst
#print axioms SuFunctor.pairCorr_snd
#print axioms SuFunctor.pairIndep_fst
#print axioms SuFunctor.pairIndep_snd
#print axioms SuFunctor.vorobev_no_joint
#print axioms SuFunctor.vorobev_record_glue
#print axioms SuFunctor.chain_glues
#print axioms SuFunctor.corrRing_glues
#print axioms SuFunctor.rayC_trans
#print axioms SuFunctor.downClosed_credalCompile
#print axioms SuFunctor.credalCompile_least
#print axioms SuFunctor.vorobev_unsatisfiable
#print axioms SuFunctor.credalCompile_vorobevGlue
#print axioms SuFunctor.vorobev_absorption
#print axioms SuFunctor.satCredal_lower_vorobevGlue
#print axioms SuFunctor.satCredal_lower_vorobevGlue_false
#print axioms SuFunctor.satisfiable_not_local
