import SuFunctor.Universe.HausdorffKL

/-! # Axiom audit for the Hausdorff–KL embedding and its updating theory

Prints the axiom footprint of the credal-embedding development: the
strict Gibbs inequality, the chain-rule engine, the weighted square
(Halpern–Leung likelihood updating), the normalization identity, the
argmin face (Gilboa–Schmeidler maximum-likelihood updating), the
vacuous-conditioning collapse, the reversed-direction adjudication pair,
the wall contrast, and the refutation fixtures (unnormalized zero set,
fenceless argmin, argmax-vs-argmin, generalized-Bayes square failure).
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe.HausdorffKL

-- foundations: strict Gibbs, the point-mass evaluation, the zero set
#print axioms SuFunctor.Universe.HausdorffKL.klq_eq_zero_iff
#print axioms SuFunctor.Universe.HausdorffKL.klq_dirac
#print axioms SuFunctor.Universe.HausdorffKL.hkl_eq_zero_iff
#print axioms SuFunctor.Universe.HausdorffKL.hklSet_range

-- the chain-rule engine and the vacuous-conditioning fence
#print axioms SuFunctor.Universe.HausdorffKL.klq_add_surprisal
#print axioms SuFunctor.Universe.HausdorffKL.klq_add_surprisal_eq_top_of_evProb_eq_zero

-- the square (weighted, exact), its normalization, its argmin face
#print axioms SuFunctor.Universe.HausdorffKL.mwu_hklW_eq
#print axioms SuFunctor.Universe.HausdorffKL.iInf_mwu_hklW
#print axioms SuFunctor.Universe.HausdorffKL.argmin_mwu_hkl_eq_mluSet

-- the direction adjudication: the flip collapses, the forward stays proper
#print axioms SuFunctor.Universe.HausdorffKL.flip_add_surprisal_eq_top
#print axioms SuFunctor.Universe.HausdorffKL.mwu_hklFlip_eq_top
#print axioms SuFunctor.Universe.HausdorffKL.Witness.flip_collapses
#print axioms SuFunctor.Universe.HausdorffKL.Witness.forward_proper

-- the wall contrast: possibilistic updating only intersects
#print axioms SuFunctor.Universe.HausdorffKL.mwu_probWall_eq_zero_iff

-- refutation fixtures, exact rationals
#print axioms SuFunctor.Universe.HausdorffKL.Witness.unnormalized_zero_set_empty
#print axioms SuFunctor.Universe.HausdorffKL.Witness.fenceless_argmin_univ
#print axioms SuFunctor.Universe.HausdorffKL.Witness.mluSet_ne_mluSetMin
#print axioms SuFunctor.Universe.HausdorffKL.Witness.gbr_cross_sums_ne
#print axioms SuFunctor.Universe.HausdorffKL.Witness.argmin_I3
