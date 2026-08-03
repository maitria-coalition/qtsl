import SuFunctor.Plain.SeamDensity

/-! # Axiom audit for the density-completion package

Prints the axiom footprint of the seam-density transport package: the
Lebesgue integral across the seam, the closed-comparison lemma, the
three transport theorems (upper bounds, equalities, suprema), the
rational sub-stratum (dyadic approximation and its density chain), the
finite-carrier surjectivity, the direct density instance over `ℕ`, and
the two refutation pins (lower bounds and infima do not transport).
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Plain

#print axioms SuFunctor.Plain.Joint.lintegral_toMeas
#print axioms SuFunctor.Plain.sum_measure_singleton
#print axioms SuFunctor.Plain.measure_eq_tsum_singleton
#print axioms SuFunctor.Plain.measure_ext_of_singleton
#print axioms SuFunctor.Plain.isClosed_le_of_lsc_usc
#print axioms SuFunctor.Plain.MeasPen.le_of_seam_le
#print axioms SuFunctor.Plain.MeasPen.eq_of_seam_eq
#print axioms SuFunctor.Plain.MeasPen.iSup_seam_eq
#print axioms SuFunctor.Plain.dyadicApprox_le
#print axioms SuFunctor.Plain.le_dyadicApprox_add
#print axioms SuFunctor.Plain.tendsto_dyadicApprox
#print axioms SuFunctor.Plain.Joint.isRatWeighted_ratApprox
#print axioms SuFunctor.Plain.Joint.tendsto_toMeas_ratApprox
#print axioms SuFunctor.Plain.Joint.toMeas_mem_closure_ratSeam
#print axioms SuFunctor.Plain.Joint.dense_ratSeam
#print axioms SuFunctor.Plain.Joint.toMeas_surjective
#print axioms SuFunctor.Plain.MeasJoint.tendsto_truncNat
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas_nat
#print axioms SuFunctor.Plain.geometricMeasJoint_singleton
#print axioms SuFunctor.Plain.Joint.toMeas_ne_geometric
#print axioms SuFunctor.Plain.isClosed_singleton_geometricMeasJoint
#print axioms SuFunctor.Plain.lowerSemicontinuous_dropWall
#print axioms SuFunctor.Plain.not_seam_ge_transport
#print axioms SuFunctor.Plain.iInf_seam_ne_iInf
#print axioms SuFunctor.Plain.dense_seam_inf_gap
