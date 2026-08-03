import SuFunctor.Universe.General.EnvelopeIdentification
import SuFunctor.Universe.General.EnvelopeWitness

/-! # Axiom audit for the countably additive envelope theorem

Prints the axiom footprint of the envelope-identification package: the
coherence layer with Hahn–Banach attainment, the σ-smooth representation
engine, the identification/attainment/minimum-display theorems with their
compact-carrier unconditional form and tight-envelope converse, and the
witnesses on `ℕ` that the σ-smoothness hypothesis cannot be dropped.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe.General

-- the coherence layer
#print axioms SuFunctor.Universe.General.IsCoherentLP.const_eq
#print axioms SuFunctor.Universe.General.IsCoherentLP.mono
#print axioms SuFunctor.Universe.General.IsCoherentLP.le_conjUpper
#print axioms SuFunctor.Universe.General.IsCoherentLP.abs_conjUpper_le
#print axioms SuFunctor.Universe.General.DominatesLP.one_eq
#print axioms SuFunctor.Universe.General.DominatesLP.sigmaSmoothAtZero
-- Hahn–Banach attainment
#print axioms SuFunctor.Universe.General.IsCoherentLP.exists_dominatesLP_eq
-- Dini: σ-smoothness is free at compact carriers
#print axioms SuFunctor.Universe.General.IsCoherentLP.sigmaSmoothAtZero_conjUpper_of_compact
-- the σ-smooth representation engine
#print axioms SuFunctor.Universe.General.exists_probabilityMeasure_of_sigmaSmooth
-- the identification
#print axioms SuFunctor.Universe.General.DominatesLP.exists_probabilityMeasure
#print axioms SuFunctor.Universe.General.IsCoherentLP.caCredal_nonempty
#print axioms SuFunctor.Universe.General.IsCoherentLP.exists_mem_caCredal_integral_eq
#print axioms SuFunctor.Universe.General.IsCoherentLP.isLeast_caCredal_image
#print axioms SuFunctor.Universe.General.IsCoherentLP.isLeast_caCredal_image_of_compactSpace
-- closure the other way
#print axioms SuFunctor.Universe.General.isCoherentLP_lowerEnv
#print axioms SuFunctor.Universe.General.sigmaSmoothAtZero_conjUpper_lowerEnv_of_tight
-- witnesses: the excluded class is inhabited
#print axioms SuFunctor.Universe.General.EnvelopeWitness.isCoherentLP_liminfLP
#print axioms SuFunctor.Universe.General.EnvelopeWitness.not_sigmaSmoothAtZero_conjUpper_liminfLP
#print axioms SuFunctor.Universe.General.EnvelopeWitness.caCredal_liminfLP_eq_empty
#print axioms SuFunctor.Universe.General.EnvelopeWitness.not_forall_coherent_caCredal_nonempty
#print axioms SuFunctor.Universe.General.EnvelopeWitness.isCoherentLP_vacuousLP
#print axioms SuFunctor.Universe.General.EnvelopeWitness.caCredal_vacuousLP_eq_univ
#print axioms SuFunctor.Universe.General.EnvelopeWitness.vacuousLP_eq_iInf_dirac
#print axioms SuFunctor.Universe.General.EnvelopeWitness.vacuousLP_not_attained
#print axioms SuFunctor.Universe.General.EnvelopeWitness.not_sigmaSmoothAtZero_conjUpper_vacuousLP
