import SuFunctor.Adequacy.StochasticPetriFlatten

/-! # Axiom audit for the flattening premises and the triangle instance

Prints the axiom footprint of the headline statements: the premise
rows (initial tangibility with its closed-init receipt; the
witness-vector token bound with its step soundness, reachability
closure, intrinsic per-place bound, and the token-creating refusal),
the dictionary controls past arity 2, the relabeling transport, the
triangle packaging pair (invertible from agreement; demonic directed
from membership), and the drain-net instance (premises discharged,
agreement both faces, the invertible cell, the directed cell, the
wired positive face).  Expected footprint for every entry: within
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

#print axioms SuFunctor.Adequacy.FinCTMC.relabel
#print axioms SuFunctor.Adequacy.FinISPN.tangibleChain_init_eq_of_tangibleInit
#print axioms SuFunctor.Adequacy.FinISPN.wsum_fire_le
#print axioms SuFunctor.Adequacy.FinISPN.wsum_ifire_le
#print axioms SuFunctor.Adequacy.FinISPN.wsum_le_of_reach
#print axioms SuFunctor.Adequacy.FinISPN.count_le_of_reach
#print axioms SuFunctor.Adequacy.FinISPN.flatten_triangle_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_demonic_directed_of_agree
#print axioms SuFunctor.Adequacy.SpnDictControls.race₃_census
#print axioms SuFunctor.Adequacy.SpnDictControls.race₃_factor
#print axioms SuFunctor.Adequacy.SpnDictControls.race₂₁_census
#print axioms SuFunctor.Adequacy.SpnDictControls.race₂₁_factor
#print axioms SuFunctor.Adequacy.SpnBoundControls.netC_tokenBound_isEmpty
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.wnet_rank
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.tbW
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.wnet_tangibleInit
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.premisesW
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.absorb_V02
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.close_T20_T00
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.close_T20_T10
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.close_T10_T00
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.flat_agree_off
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.flat_agree_init
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.witness_triangle
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.witness_demonic_directed
#print axioms SuFunctor.Adequacy.SpnFlattenWitness.su_witness_flat
