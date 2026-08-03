import SuFunctor.Universe.SpecRewrite

/-! # Axiom audit for the rewrite layer as compiled-class equalities

Prints the axiom footprint of the headline statements: the two
warrants and the decided fork, the normal-form-agreement route, the
lattice-homomorphism family and its surface-formula corollaries, the
dualities, the disjunction-free coincidence, and the record-site layer
(the avoidance equality, the one-way alias with its reverse-failure
witness, the refusal receipts, the Streett degeneration).  Expected
footprint for every entry: within `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Universe.classEq_of_nnf_eq
#print axioms SuFunctor.Universe.classEquiv_of_nnf_eq
#print axioms SuFunctor.Universe.wallOn_mem_safeProper_iff
#print axioms SuFunctor.Universe.exists_denEq_not_classEq
#print axioms SuFunctor.Universe.not_denEq_imp_classEq
#print axioms SuFunctor.Universe.classEq_iff_classSem
#print axioms SuFunctor.Universe.classSem_conj_disj_left
#print axioms SuFunctor.Universe.classSem_absorb_conj
#print axioms SuFunctor.Universe.classSem_absorb_disj
#print axioms SuFunctor.Universe.classEquiv_conj_comm
#print axioms SuFunctor.Universe.classEquiv_distrib
#print axioms SuFunctor.Universe.classEquiv_absorb_conj
#print axioms SuFunctor.Universe.classEquiv_neg_neg
#print axioms SuFunctor.Universe.classEquiv_neg_conj
#print axioms SuFunctor.Universe.classEquiv_neg_disj
#print axioms SuFunctor.Universe.classSem_eq_iff_den_eq_disjFree
#print axioms SuFunctor.Universe.recordClass_avoid
#print axioms SuFunctor.Universe.recordClass_always_subset_alwaysT
#print axioms SuFunctor.Universe.exists_recordClass_alwaysT_not_always
#print axioms SuFunctor.Universe.pathNnf_notPath_always_refuses
#print axioms SuFunctor.Universe.pathNnf_notPath_untilF_refuses
#print axioms SuFunctor.Universe.pathNnf_notPath_streett_refuses
#print axioms SuFunctor.Universe.streettOn_singleton_univ_of_nonempty
#print axioms SuFunctor.Universe.streettOn_singleton_univ_empty
