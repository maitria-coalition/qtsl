import SuFunctor.Adequacy.MaDemonic
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Axiom audit for the demonic Markov-automaton adequacy square

Prints the axiom footprint of the headline theorems of the demonic
(scheduler-quantification) face: the rank-irrelevance package, the
feeding lemma, the set-valued square, the credal-slice reconciliation,
the uniform-over-schedulers verdict theorems, the mechanized
degeneracies, the certified-family stratum, and the semantic-universe
wiring.  Expected footprint for every entry: within `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinMA.BranchZenoFree.zenoFree
#print axioms SuFunctor.Adequacy.absorbIter_absFuel_rank_irrel
#print axioms SuFunctor.Adequacy.FinMA.absorb_rank_irrel
#print axioms SuFunctor.Adequacy.FinMA.pathLaw_rank_irrel
#print axioms SuFunctor.Adequacy.FinMA.demonicLaws_rank_irrel
#print axioms SuFunctor.Adequacy.FinMA.demonicCredal_rank_irrel
#print axioms SuFunctor.Adequacy.maDemonicC_iff
#print axioms SuFunctor.Adequacy.ma_demonic_adequacy
#print axioms SuFunctor.Adequacy.maDemonicCredalC_iff
#print axioms SuFunctor.Adequacy.ma_demonic_maxSlice
#print axioms SuFunctor.Adequacy.ma_demonic_ray_singleton_reconciliation
#print axioms SuFunctor.Adequacy.satCredal_lower_maDemonicCredal
#print axioms SuFunctor.Adequacy.satCredal_upper_maDemonicCredal
#print axioms SuFunctor.Adequacy.satCredal_lower_maDemonicLaws
#print axioms SuFunctor.Adequacy.satCredal_upper_maDemonicLaws
#print axioms SuFunctor.Adequacy.satCredal_lower_maDemonic_ray_singleton
#print axioms SuFunctor.Adequacy.satCredal_upper_maDemonic_ray_singleton
#print axioms SuFunctor.Adequacy.Policy.nonempty_of_isEmpty
#print axioms SuFunctor.Adequacy.Policy.isEmpty_iff
#print axioms SuFunctor.Adequacy.not_satCredal_upper_maDemonicCredal_geC
#print axioms SuFunctor.Adequacy.satCredal_maDemonic_of_isEmpty_policy
#print axioms SuFunctor.Adequacy.FinMA.nonempty_markovian
#print axioms SuFunctor.Adequacy.FinMA.demonicLawsCert_iff
#print axioms SuFunctor.Adequacy.FinMA.demonicCredalCert_iff
#print axioms SuFunctor.Adequacy.satCredal_lower_maDemonicCredalCert
#print axioms SuFunctor.Adequacy.satCredal_upper_maDemonicCredalCert
#print axioms SuFunctor.Adequacy.su_ma_demonic_wiring
#print axioms SuFunctor.Adequacy.su_ma_demonic_wiring'
#print axioms SuFunctor.Adequacy.su_ma_demonic_bottom
#print axioms SuFunctor.Adequacy.su_ma_demonic_slice
