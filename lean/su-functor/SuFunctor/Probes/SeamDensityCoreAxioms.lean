import SuFunctor.Plain.SeamDensityCore

/-! # Axiom audit for the density of finitely supported joints

Prints the axiom footprint of the density theorem — finitely supported joints
are narrowly dense among subprobability measures over a separable pseudometric
carrier — together with its pseudo-metrizable wrapper and the
weighted-point-mass constructions it rests on.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor.Plain

#print axioms SuFunctor.Plain.Joint.SeamDensityCore.ofFinset
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.measSum_ofFinset
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.lintegral_toMeas
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.lintegral_toMeas_ofFinset
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.quantize
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.lintegral_quantize
#print axioms SuFunctor.Plain.Joint.SeamDensityCore.tendsto_sum_quantization
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas_of_pseudoMetrizable
