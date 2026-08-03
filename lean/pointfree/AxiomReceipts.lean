import Pointfree

/-!
# Axiom receipts

`#print axioms` receipts for the headline theorems of the point-free
stochastics library, so the axiom footprint is inspectable at build
time.  Expected footprint for every entry: `propext`,
`Classical.choice`, `Quot.sound` — the standard three, no `sorryAx`,
nothing else.
-/

open Pointfree

-- the dagger chart: round trips, packaged equivalence
#print axioms Pointfree.SubProb.restrict_promote
#print axioms Pointfree.SubProb.promote_restrict
#print axioms Pointfree.SubProb.promoteEquiv

-- the two modular identities that drive the chart
#print axioms Pointfree.Valuation.apply_true_eq_add
#print axioms Pointfree.Valuation.apply_top_false_add_bot_true

-- Scott continuity: transport across the chart, both directions
#print axioms Pointfree.SubProb.isScottContinuous_promoteVal
#print axioms Pointfree.SubProb.isScottContinuous_restrictVal
#print axioms Pointfree.SubProb.isScottContinuous_promote_iff

-- pushforward and Dirac
#print axioms Pointfree.Valuation.IsScottContinuous.map
#print axioms Pointfree.Valuation.isScottContinuous_dirac

-- the topology: polarity by construction, the forcing identity
#print axioms Pointfree.Prob.lowerSemicontinuous_eval
#print axioms Pointfree.SubProb.lowerSemicontinuous_eval
#print axioms Pointfree.SubProb.upperSemicontinuous_mass
#print axioms Pointfree.SubProb.isClosed_liveness_wall
#print axioms Pointfree.SubProb.lowerSemicontinuous_one_sub_mass
#print axioms Pointfree.SubProb.induced_promote_eq
#print axioms Pointfree.SubProb.promoteHomeomorph

-- the bridge: measures restrict to valuations; τ-additivity; naturality; Dirac
#print axioms MeasureTheory.Measure.toValuation
#print axioms MeasureTheory.Measure.toValuation_isScottContinuous
#print axioms MeasureTheory.Measure.toValuation_map
#print axioms Pointfree.dirac_toValuation

-- functoriality: pushforward laws, mass preservation, carrier continuity
#print axioms Pointfree.Valuation.map_id
#print axioms Pointfree.Valuation.map_comp
#print axioms Pointfree.Valuation.map_top
#print axioms Pointfree.SubProb.map_comp
#print axioms Pointfree.SubProb.continuous_map
#print axioms Pointfree.Prob.continuous_map

-- unit naturality: the Dirac square, frame level and continuous-map level
#print axioms Pointfree.Valuation.map_dirac
#print axioms Pointfree.SubProb.push_dirac
#print axioms Pointfree.pointHom_comap

-- the bridge as a natural transformation; the Dirac square as its image
#print axioms MeasureTheory.Measure.toSubProb_map
#print axioms MeasureTheory.Measure.dirac_map_toValuation
#print axioms MeasureTheory.Measure.map_dirac_toValuation_eq
#print axioms MeasureTheory.Measure.push_toSubProb_isScottContinuous

-- the prevision layer: pairing linearity, naturality, indicator evaluation
#print axioms Pointfree.Valuation.pair_add
#print axioms Pointfree.Valuation.pair_smul
#print axioms Pointfree.Valuation.pair_map
#print axioms Pointfree.Valuation.pair_indicator
#print axioms Pointfree.Valuation.toPrevision_map
#print axioms Pointfree.Prevision.map_comp
#print axioms Pointfree.Prevision.iInfEnvelope_isSuperadditive
#print axioms Pointfree.Prevision.le_iInfEnvelope_body

-- the measure algebra: the null-quotient face
#print axioms Pointfree.MeasureAlgebra.mass_eq_zero_iff
#print axioms Pointfree.MeasureAlgebra.ofOpen_mono
#print axioms Pointfree.MeasureAlgebra.isLUB_ofOpen_sSup

-- BridgeContinuity + EscapeWitness receipts
#print axioms MeasureTheory.FiniteMeasure.le_liminf_measure_open_of_tendsto
#print axioms MeasureTheory.FiniteMeasure.lowerSemicontinuous_measure_open
#print axioms MeasureTheory.ProbabilityMeasure.lowerSemicontinuous_measure_open
#print axioms Pointfree.SubProbabilityMeasure.continuous_toSubProb
#print axioms Pointfree.SubProbabilityMeasure.tendsto_toSubProb_of_tendsto
#print axioms Pointfree.continuous_toProb
#print axioms Pointfree.Valuation.ofUltrafilter
#print axioms Pointfree.Valuation.ofUltrafilter_pure
#print axioms Pointfree.Valuation.isScottContinuous_ofUltrafilter_pure
#print axioms Pointfree.not_isScottContinuous_ofUltrafilter_hyperfilter
#print axioms Pointfree.tendsto_dirac_hyperfilter
-- DaggerChart receipts
-- the measure-level dagger chart: legs, round trips, chart
#print axioms Pointfree.promoteMeasure
#print axioms Pointfree.restrictMeasure
#print axioms Pointfree.restrictMeasure_promoteMeasure
#print axioms Pointfree.promoteMeasure_restrictMeasure
#print axioms Pointfree.daggerChartMeasure

-- the integral calculus driving the chart's continuity
#print axioms Pointfree.lintegral_promoteMeasure
#print axioms Pointfree.lintegral_comap_inl
#print axioms Pointfree.testAgainstNN_promoteMeasure
#print axioms Pointfree.testAgainstNN_restrictMeasure

-- the compactness dividend, two independent routes; metrizability
#print axioms Pointfree.instCompactSpaceSubProbabilityMeasure
#print axioms Pointfree.compactSpace_of_daggerChartMeasure
#print axioms Pointfree.metrizableSpace_subProbabilityMeasure

-- Borel glue for the dagger sum
#print axioms Pointfree.measurableEmbedding_inl
#print axioms Pointfree.instBorelSpaceSumUnit
#print axioms Pointfree.instMetrizableSpaceSumUnit

-- presented frames: generators, relations, join-generation
#print axioms Pointfree.presentingNucleus
#print axioms Pointfree.le_presentingNucleus_of_mem
#print axioms Pointfree.gen_inf
#print axioms Pointfree.gen_top
#print axioms Pointfree.restrict_rel_le
#print axioms Pointfree.eq_iSup_gen
#print axioms Pointfree.hom_ext

-- determination: continuous valuations from generator values
#print axioms Pointfree.Valuation.apply_sup_le_add
#print axioms Pointfree.Valuation.finsetSup_ne_top
#print axioms Pointfree.Valuation.agree_on_finsetSup
#print axioms Pointfree.Valuation.ext_of_generators
#print axioms Pointfree.Valuation.exists_generator_ne

-- the presented hyperspace frame and localic Choquet–Matheron
#print axioms Pointfree.nabla_inf
#print axioms Pointfree.nabla_top
#print axioms Pointfree.eq_iSup_nabla
#print axioms Pointfree.nabla_hit_le_of_refines
#print axioms Pointfree.top_le_of_missCovers
#print axioms Pointfree.nabla_miss_le_of_missMono
#print axioms Pointfree.nabla_hitMiss_le_of_diffCovers
#print axioms Pointfree.Valuation.ext_of_nabla
#print axioms Pointfree.Valuation.exists_nabla_ne

-- the spatial shadow: determination on the frame of opens
#print axioms Pointfree.Valuation.opens_eq_iSup_of_isTopologicalBasis
#print axioms Pointfree.Valuation.ext_of_isTopologicalBasis
#print axioms Pointfree.Valuation.exists_basis_ne
#print axioms MeasureTheory.Measure.toValuation_ext_of_isTopologicalBasis
