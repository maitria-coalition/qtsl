import SuFunctor.Adequacy.Bag

/-! # Axiom audit for the bag former's exchange-quotient transport

Prints the axiom footprint of the E1 transport cell: the
order-statistic identity and sort measurability, the quotient/section
identities and fiber-orbit lemma, the generic quotient-kernel square
(one-step, section-independence, finite-horizon intertwining), the
shape-indexed assembly (`bag_transport`), and the order-graph
witnesses.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else. -/

open SuFunctor.Adequacy.Bag

#print axioms SuFunctor.Adequacy.Bag.sortTuple_comp_perm
#print axioms SuFunctor.Adequacy.Bag.sortTuple_apply_eq_inf_sup
#print axioms SuFunctor.Adequacy.Bag.measurable_max_of_le
#print axioms SuFunctor.Adequacy.Bag.measurable_min_of_le
#print axioms SuFunctor.Adequacy.Bag.measurable_sup'_of_le
#print axioms SuFunctor.Adequacy.Bag.measurable_inf'_of_le
#print axioms SuFunctor.Adequacy.Bag.measurable_sortTuple
#print axioms SuFunctor.Adequacy.Bag.toSym_comp_perm
#print axioms SuFunctor.Adequacy.Bag.toSym_val_eq_ofFn
#print axioms SuFunctor.Adequacy.Bag.measurable_toSym
#print axioms SuFunctor.Adequacy.Bag.toSym_sortTuple
#print axioms SuFunctor.Adequacy.Bag.monotone_symSec
#print axioms SuFunctor.Adequacy.Bag.symSec_eq_ofMultiset_get
#print axioms SuFunctor.Adequacy.Bag.toSym_symSec
#print axioms SuFunctor.Adequacy.Bag.monotone_eq_of_toSym_eq
#print axioms SuFunctor.Adequacy.Bag.symSec_toSym
#print axioms SuFunctor.Adequacy.Bag.symSec_comp_toSym
#print axioms SuFunctor.Adequacy.Bag.fiber_exists_perm
#print axioms SuFunctor.Adequacy.Bag.measurable_symSec
#print axioms SuFunctor.Adequacy.Bag.quotKernel_comp_eq
#print axioms SuFunctor.Adequacy.Bag.comap_section_congr
#print axioms SuFunctor.Adequacy.Bag.deterministic_comp_eq
#print axioms SuFunctor.Adequacy.Bag.iter_intertwine
#print axioms SuFunctor.Adequacy.Bag.iter_intertwine_apply
#print axioms SuFunctor.Adequacy.Bag.measurable_sigma_mk
#print axioms SuFunctor.Adequacy.Bag.measurable_sigma_iff
#print axioms SuFunctor.Adequacy.Bag.toSymSigma_symSecSigma
#print axioms SuFunctor.Adequacy.Bag.measurable_toSymSigma
#print axioms SuFunctor.Adequacy.Bag.measurable_symSecSigma
#print axioms SuFunctor.Adequacy.Bag.symSecSigma_toSymSigma
#print axioms SuFunctor.Adequacy.Bag.invariance_iff_perm
#print axioms SuFunctor.Adequacy.Bag.bag_transport
#print axioms SuFunctor.Adequacy.Bag.measurableSet_le_real
#print axioms SuFunctor.Adequacy.Bag.measurableSet_le_lex
#print axioms SuFunctor.Adequacy.Bag.measurableSet_le_lex'
