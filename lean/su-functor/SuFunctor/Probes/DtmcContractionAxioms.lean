import SuFunctor.Adequacy.DtmcContraction

/-! # Axiom audit for the weighted transfer contraction

Prints the axiom footprint of the contraction-species module: the
weighted forward evolution and its stochastic instance tie, the
weighted contraction core with its score face and subsumption
instance, the regional packaging, exit domination, the series bounds,
and the two tail assemblies.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.wmassAt_nonneg
#print axioms SuFunctor.Adequacy.massAt_eq_wmassAt
#print axioms SuFunctor.Adequacy.wmassAt_expect_succ
#print axioms SuFunctor.Adequacy.wmassAt_expect_le_of_contraction
#print axioms SuFunctor.Adequacy.wmassAt_expect_le_of_contraction_scored
#print axioms SuFunctor.Adequacy.massAt_expect_le_of_contraction_of_weighted
#print axioms SuFunctor.Adequacy.qGenFormContraction_subsumes_genform
#print axioms SuFunctor.Adequacy.wmassAt_expect_on_le_of_contraction_on
#print axioms SuFunctor.Adequacy.wmassAt_exit_le_of_contraction
#print axioms SuFunctor.Adequacy.sum_range_mul_pow_mul_eq
#print axioms SuFunctor.Adequacy.sum_range_pow_le
#print axioms SuFunctor.Adequacy.sum_range_mul_pow_le
#print axioms SuFunctor.Adequacy.sum_Ico_pow_le
#print axioms SuFunctor.Adequacy.sum_Ico_mul_pow_le
#print axioms SuFunctor.Adequacy.wmassAt_exit_tail_le
#print axioms SuFunctor.Adequacy.wmassAt_exit_moment_tail_le
