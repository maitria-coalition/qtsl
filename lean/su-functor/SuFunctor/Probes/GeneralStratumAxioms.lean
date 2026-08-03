import SuFunctor.Plain.MeasJoint
import SuFunctor.Plain.GeneralFunctor
import SuFunctor.Plain.GeneralSeam

/-! # Axiom audit for the general stratum of the composition tier

Prints the axiom footprint of the headline theorems of the
subprobability-measure stratum: the joint calculus and its coherence
cores, the weak-topology and lower-semicontinuity stock, the tight-tier
decoration functor over measurable carriers, the transposed acceptance
battery, and the seam exhibiting the finite stratum as a sub-instance.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Plain

#print axioms SuFunctor.Plain.MeasJoint.push_id
#print axioms SuFunctor.Plain.MeasJoint.push_push
#print axioms SuFunctor.Plain.MeasJoint.mass_push
#print axioms SuFunctor.Plain.MeasPen.pull_pull
#print axioms SuFunctor.Plain.pull_mboxplus_of_comm
#print axioms SuFunctor.Plain.pull_mboxplus_assoc
#print axioms SuFunctor.Plain.pull_mboxplus_zero_left
#print axioms SuFunctor.Plain.pull_mboxplus_zero_right
#print axioms SuFunctor.Plain.continuous_push
#print axioms SuFunctor.Plain.lowerSemicontinuous_pull
#print axioms SuFunctor.Plain.lowerSemicontinuous_mboxplus
#print axioms SuFunctor.Plain.exists_isMinOn_of_lowerSemicontinuous
#print axioms SuFunctor.Plain.IsCompactlySupported.push
#print axioms SuFunctor.Plain.measSpecObj
#print axioms SuFunctor.Plain.mem_mboxplusClass_iff
#print axioms SuFunctor.Plain.mboxplusClass_nonempty
#print axioms SuFunctor.Plain.munitClass_transparent
#print axioms SuFunctor.Plain.msingleton_mboxplus
#print axioms SuFunctor.Plain.mtransport_singleton
#print axioms SuFunctor.Plain.midealPoint_le_iff
#print axioms SuFunctor.Plain.mboxplusClass_mono
#print axioms SuFunctor.Plain.measSpecMap_mono
#print axioms SuFunctor.Plain.taxedMboxplus_breaks_unit_transparency
#print axioms SuFunctor.Plain.funnelMComp_breaks_unit_coherence
#print axioms SuFunctor.Plain.Joint.toMeas
#print axioms SuFunctor.Plain.Joint.toMeas_mass
#print axioms SuFunctor.Plain.Joint.toMeas_zero
#print axioms SuFunctor.Plain.Joint.toMeas_singleton
#print axioms SuFunctor.Plain.Joint.toMeas_injective
#print axioms SuFunctor.Plain.Joint.toMeas_push
#print axioms SuFunctor.Plain.Joint.pull_toMeas
#print axioms SuFunctor.Plain.Joint.image_pull_toMeas
