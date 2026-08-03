import SuFunctor.Universe.Marginalization
import SuFunctor.Universe.HullClosure

/-! # Axiom audit for the Polish-residue theorems

Prints the axiom footprint of the marginalization rider (the escaping-mass
witness, the lsc-envelope adjunction, exactness under the inf-compactness
certificate) and the binary-hull closure package (hull closedness,
levelwise exactness of the quasiconvex coproduct).  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe

-- marginalization: the witness
#print axioms SuFunctor.Universe.exists_lowerSemicontinuous_not_lowerSemicontinuous_infProj
#print axioms SuFunctor.Universe.isClosed_range_escapeMix
#print axioms SuFunctor.Universe.not_tendsto_escapeMix_atTop
#print axioms SuFunctor.Universe.not_isClosed_image_liveMass
-- marginalization: the reflector adjunction
#print axioms SuFunctor.Universe.le_lscEnv_iff
#print axioms SuFunctor.Universe.le_infProj_iff
#print axioms SuFunctor.Universe.le_hide_iff
#print axioms SuFunctor.Universe.lscEnv_add_lscEnv_le
-- marginalization: exactness under the certificate
#print axioms SuFunctor.Universe.sublevel_infProj_eq
#print axioms SuFunctor.Universe.exists_infProj_attained
#print axioms SuFunctor.Universe.isCompact_sublevel_infProj
#print axioms SuFunctor.Universe.lowerSemicontinuous_infProj
#print axioms SuFunctor.Universe.isCompact_sublevel_of_isTightMeasureSet
#print axioms SuFunctor.Universe.sublevel_infProj_margFst_eq
-- hull closure
#print axioms SuFunctor.Universe.isClosed_pairHull
#print axioms SuFunctor.Universe.isClosed_binaryHull
#print axioms SuFunctor.Universe.isTightMeasureSet_range_of_tendsto
-- levelwise exactness
#print axioms SuFunctor.Universe.iInter_binaryHull_sublevel
#print axioms SuFunctor.Universe.sublevel_qCoproduct_eq
#print axioms SuFunctor.Universe.qCoproduct_le_min
#print axioms SuFunctor.Universe.le_qCoproduct_of_forall_mixConvex
