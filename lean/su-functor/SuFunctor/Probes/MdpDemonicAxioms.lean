import SuFunctor.Adequacy.MdpDemonic

/-! # Axiom audit for the demonic MDP adequacy square

Prints the axiom footprint of the headline theorems of the demonic
(open-policy) face: the feeding lemma, the set-valued square, the
credal-slice reconciliation, the uniform-over-policies verdict
theorems, and the mechanized degeneracies.  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.compilePolicy_toPolicy
#print axioms SuFunctor.Adequacy.demonicC_iff
#print axioms SuFunctor.Adequacy.mdp_demonic_adequacy
#print axioms SuFunctor.Adequacy.demonicCredalC_iff
#print axioms SuFunctor.Adequacy.demonic_maxSlice
#print axioms SuFunctor.Adequacy.demonic_ray_singleton_reconciliation
#print axioms SuFunctor.Adequacy.satCredal_lower_demonicCredal
#print axioms SuFunctor.Adequacy.satCredal_upper_demonicCredal
#print axioms SuFunctor.Adequacy.satCredal_lower_demonicLaws
#print axioms SuFunctor.Adequacy.satCredal_upper_demonicLaws
#print axioms SuFunctor.Adequacy.satCredal_lower_demonic_ray_singleton
#print axioms SuFunctor.Adequacy.satCredal_upper_demonic_ray_singleton
#print axioms SuFunctor.Adequacy.Policy.nonempty
#print axioms SuFunctor.Adequacy.not_satCredal_upper_demonicCredal_geC
#print axioms SuFunctor.Adequacy.FinMDP.nonempty_state
#print axioms SuFunctor.Adequacy.isEmpty_policy_iff
#print axioms SuFunctor.Adequacy.satCredal_demonic_of_isEmpty_policy
