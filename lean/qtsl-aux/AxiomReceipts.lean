import QtslAux
import QtslAux.Imprecise.PenaltyCoherence
import QtslAux.BagLiftFixture
import QtslAux.BagLiftMultiplicity

/-! # Axiom-closure receipts

A standing build target, kept outside the default `QtslAux`
library, that re-checks the axiom closure of the package's principal
theorems on every build:

    lake build AxiomReceipts

Each `#print axioms` line below is expected to report a subset of
`[propext, Classical.choice, Quot.sound]` — the closure of a complete
proof that uses no additional axioms. New theorems on the package's
certified surface should be paired with a receipt line here, so that a
build of this target constitutes an audit of the whole list.
-/

#print axioms Qtsl.Repar.AffineWitness.t0_soundness
#print axioms Qtsl.Repar.t05_soundness
#print axioms Qtsl.Repar.t05_soundness_gridcx
#print axioms Qtsl.Repar.t1_soundness
#print axioms Qtsl.Repar.t1_soundness_word
#print axioms Qtsl.Repar.totalDegree_bind₁_le_mul
#print axioms Qtsl.Repar.bind₁_vars_eq_self
#print axioms Qtsl.Repar.cell_cofactor_iff
#print axioms Qtsl.Repar.cleared_pullback_soundness
#print axioms Qtsl.ChartCover.phiNeg_covers_arc
#print axioms Qtsl.ChartCover.chartPair_covers_circle
#print axioms Qtsl.ChartCover.covers_x5_arc
#print axioms Qtsl.ChartCover.covers_x5_tube
#print axioms Qtsl.ChartCover.covers_x5_ball_arc

#print axioms Qtsl.BoxBern.boxBern_enclosure
#print axioms Qtsl.BoxBern.boxBern_enclosure_minmax
#print axioms Qtsl.BoxBern.boxBern_nonpos
#print axioms Qtsl.BoxBern.aeval_boxShift
#print axioms Qtsl.BoxBern.sum_aeval_tensorBern

#print axioms Qtsl.Enclosure.encCheck_sound
#print axioms Qtsl.Enclosure.encCheck_sound_bracket
#print axioms Qtsl.Enclosure.encCheck_point
#print axioms Qtsl.Enclosure.hasSum_maclaurin
#print axioms Qtsl.Enclosure.hasSum_maclaurin_erfT
#print axioms Qtsl.Enclosure.integral_exp_neg_sq
#print axioms Qtsl.Enclosure.two_div_sqrt_pi_mem
#print axioms Qtsl.Enclosure.inv_sqrt_two_pi_mem
#print axioms Qtsl.Enclosure.linear_interp_le

#print axioms Qtsl.Aliases.sound_QSatFromRegion
#print axioms Qtsl.Aliases.rootEval_eval_cast
#print axioms Qtsl.Aliases.rootEval_sublevel_iff
#print axioms Qtsl.Aliases.rootEval_box_iff
#print axioms Qtsl.Aliases.sound_QSatFromRegion_sublevel
#print axioms Qtsl.Aliases.taylorLeaf_le_exp
#print axioms Qtsl.Aliases.taylorLeaf_rat_le_exp
#print axioms Qtsl.Aliases.negF_denot_subset
#print axioms Qtsl.Aliases.sound_NegFAlias
#print axioms Qtsl.Aliases.sugarAvoid_denot
#print axioms Qtsl.Aliases.sugarGF_denot
#print axioms Qtsl.Aliases.sugarFG_denot

#print axioms Qtsl.Wasserstein.measure_eq_of_W2edist_eq_zero
#print axioms Qtsl.Wasserstein.W2edist_triangle
#print axioms Qtsl.Wasserstein.exists_limit_of_summable_chain
#print axioms Qtsl.Wasserstein.sound_QFixBall_wasserstein

#print axioms Qtsl.LayerD.pdmp_dynkin_core_dini
#print axioms Qtsl.LayerD.segMeasureFin_outcomeRead_eq
#print axioms Qtsl.LayerD.PDMPFlowFinDini.segD_at
#print axioms Qtsl.LayerD.segmentDynkin_of_pdmp_dini
#print axioms Qtsl.LayerD.dini_row_of_deriv_row

#print axioms Qtsl.LayerD.sound_GSHS_avoid_timed
#print axioms Qtsl.LayerD.sound_GSHS_until
#print axioms Qtsl.LayerD.sound_GSHS_until_battery

#print axioms Qtsl.LayerD.segMeasureIto_live_read
#print axioms Qtsl.LayerD.liminf_sampledRead_of_exit
#print axioms Qtsl.LayerD.le_liminf_sampledRead_of_live
#print axioms Qtsl.LayerD.ItoInterface.segD_at
#print axioms Qtsl.LayerD.segmentDynkin_of_ito
#print axioms Qtsl.LayerD.ItoInterface.ofPDMPFlowFin

#print axioms Qtsl.LayerD.sampled_le_of_supermartingale
#print axioms Qtsl.LayerD.aemeasurable_sampledRead_of_supermartingale
#print axioms Qtsl.LayerD.ItoInterface.ofSupermartingale

#print axioms OptionalSamplingRC.supermartingale_exp_discount
#print axioms OptionalSamplingRC.supermartingale_of_compensator_nonpos
#print axioms Qtsl.LayerD.ItoSupermartingaleData.toItoInterface
#print axioms Qtsl.LayerD.segmentDynkin_of_supermartingale
#print axioms Qtsl.LayerD.segmentDynkin_of_mixed
#print axioms Qtsl.LayerD.MPFlow.certProcess_supermartingale
#print axioms Qtsl.LayerD.MPFlow.toItoSupermartingaleData
#print axioms Qtsl.LayerD.segmentDynkin_of_mp
#print axioms Qtsl.LayerD.segmentDynkin_of_mp_mixed
#print axioms Qtsl.LayerD.rankingSegmentDynkin_of_mp
#print axioms Qtsl.LayerD.ItoSupermartingaleData.ofMPNoAlarm
#print axioms Qtsl.LayerD.sound_GSHS_safety_mp
#print axioms Qtsl.LayerD.sound_GSHS_safety_battery_mp
#print axioms Qtsl.LayerD.sound_GSHS_deadline_mp
#print axioms Qtsl.LayerD.sound_GSHS_deadline_battery_mp
#print axioms Qtsl.LayerD.sound_GSHS_avoid_timed_mp
#print axioms Qtsl.LayerD.sound_GSHS_until_mp
#print axioms Qtsl.LayerD.sound_GSHS_until_battery_mp
#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle_mp

#print axioms OptionalSamplingRC.integral_stoppedValue_min_ge
#print axioms OptionalSamplingRC.integral_stoppedValue_min_eq
#print axioms Qtsl.LayerD.lintegral_outcomeRead_segMeasureIto_le_liminf
#print axioms Qtsl.LayerD.MPFlow.liminf_lintegral_sampledRead_le
#print axioms Qtsl.LayerD.MPFlow.segD_ranking_at
#print axioms Qtsl.LayerD.rankingSegmentDynkin_of_mp_strict
#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle_mp_strict

#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle
#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle_confined
#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle_carved_discharged
#print axioms Qtsl.LayerD.sound_GSHS_streett_bundle_carved_discharged_confined

#print axioms Qtsl.Imprecise.pushPenaltyG_comp
#print axioms Qtsl.Imprecise.pushPenaltyG_mono
#print axioms Qtsl.Imprecise.pushPenaltyG_unique
#print axioms Qtsl.Imprecise.laxPenaltyG_natural
#print axioms Qtsl.Imprecise.laxPenaltyG_assoc
#print axioms Qtsl.Imprecise.laxPenaltyG_zero_left
#print axioms Qtsl.Imprecise.laxPenaltyG_zero_right
#print axioms Qtsl.Imprecise.laxPenaltyG_unit_left
#print axioms Qtsl.Imprecise.laxPenaltyG_unit_right
#print axioms Qtsl.Imprecise.laxPenaltyG_unique_right
#print axioms Qtsl.Imprecise.laxPenaltyG_comm
#print axioms Qtsl.Imprecise.laxPenaltyG_mono
#print axioms Qtsl.Imprecise.le_laxPenaltyG_left
#print axioms Qtsl.Imprecise.le_laxPenaltyG_right
#print axioms Qtsl.Imprecise.laxPenaltyG_indicator
#print axioms Qtsl.Imprecise.laxPenaltyG_eq_compositePenaltyG_bool
#print axioms Qtsl.Imprecise.compositePenaltyG_sum_type
#print axioms Qtsl.Imprecise.compositePenaltyG_reindex
#print axioms Qtsl.Imprecise.compositePenaltyG_sumAssoc
#print axioms Qtsl.Imprecise.doublingLax_not_comm
#print axioms Qtsl.Imprecise.doublingLax_not_assoc
#print axioms Qtsl.Imprecise.laxPenaltyG_assoc_instancePUnit
#print axioms Qtsl.Imprecise.offsetLax_not_unital
#print axioms Qtsl.Imprecise.pointLax_not_natural

#print axioms Qtsl.Imprecise.envelope_coherent
#print axioms Qtsl.Imprecise.IsCoherent.exists_dominating_exp_eq
#print axioms Qtsl.Imprecise.IsCoherent.eq_sInf_credal
#print axioms Qtsl.Imprecise.natExt_coherent
#print axioms Qtsl.Imprecise.assessment_le_natExt
#print axioms Qtsl.Imprecise.natExt_le_coherent
#print axioms Qtsl.Imprecise.natExt_eq_dualVal
#print axioms Qtsl.Imprecise.dominates_natExt_iff
#print axioms Qtsl.Imprecise.avoidsSureLoss_iff_noSureLoss
#print axioms Qtsl.Imprecise.Mutants.natExt_val
#print axioms Qtsl.Imprecise.Mutants.forged_envelope_violates
#print axioms Qtsl.Imprecise.Mutants.QSup_not_coherent
#print axioms Qtsl.Imprecise.Mutants.natExt_gt_vacuous

#print axioms Qtsl.Imprecise.envelopeG_coherent
#print axioms Qtsl.Imprecise.natExtG_coherent
#print axioms Qtsl.Imprecise.assessment_le_natExtG
#print axioms Qtsl.Imprecise.subset_compatibleSetG_of_dominating
#print axioms Qtsl.Imprecise.natExtG_le_lowerEnvG
#print axioms Qtsl.Imprecise.avoidsSureLossG_of_dominating
#print axioms Qtsl.Imprecise.dominates_natExtG_iff
#print axioms Qtsl.Imprecise.setOf_dominatesG_natExtG_eq
#print axioms Qtsl.Imprecise.pmExp_pmMix
#print axioms Qtsl.Imprecise.pmMix_mem_compatibleSetG
#print axioms Qtsl.Imprecise.continuous_pmExp_of_continuous
#print axioms Qtsl.Imprecise.isClosed_compatibleSetG

#print axioms Qtsl.Imprecise.compile_mul_pullback_subset_naturalExtension
#print axioms Qtsl.Imprecise.compile_boxplus_subset_naturalExtension
#print axioms Qtsl.Imprecise.crisp_locus_iff
#print axioms Qtsl.Imprecise.compile_mul_eq_of_indicator
#print axioms Qtsl.Imprecise.witness_containment_strict
#print axioms Qtsl.Imprecise.witness_containment_strict_naturalExtension
#print axioms Qtsl.Imprecise.mutant_identity_fails
#print axioms Qtsl.Imprecise.mutant_glue_not_subset_composite

#print axioms Qtsl.Imprecise.boxplus_proper_iff_marginal_compatible
#print axioms Qtsl.Imprecise.finite_boxplus_proper_iff
#print axioms Qtsl.Imprecise.finpmf_coupling_of_map_eq
#print axioms Qtsl.Imprecise.mutant_no_agreement_fails
#print axioms Qtsl.Imprecise.glue_control

#print axioms Qtsl.LeakAware.safe_mass_lower_bound
#print axioms Qtsl.LeakAware.envelope_safe_mass_lower_bound
#print axioms Qtsl.LeakAware.envelope_safe_mass_lower_bound_barrier_one
#print axioms Qtsl.LeakAware.envelope_safe_mass_lower_bound_isProbability
#print axioms Qtsl.LeakAware.naive_bound_fails

#print axioms Qtsl.DiamondSite.interior_nonempty_iff_thick
#print axioms Qtsl.DiamondSite.interior_pairFiltered
#print axioms Qtsl.DiamondSite.no_interior_of_not_thick
#print axioms Qtsl.DiamondSite.ClockMap.diamond_sub
#print axioms Qtsl.DiamondSite.ClockMap.diamond_thick
#print axioms Qtsl.DiamondSite.ClockMap.diamond_interiorMem
#print axioms Qtsl.DiamondSite.ClockMap.cover_cofinal
#print axioms Qtsl.DiamondSite.EvolutionFamily.spaceTime_zero
#print axioms Qtsl.DiamondSite.EvolutionFamily.spaceTime_add

#print axioms Qtsl.DiamondSite.le_iff_sub
#print axioms Qtsl.DiamondSite.InteriorMem.of_le
#print axioms Qtsl.DiamondSite.InteriorMem.trans_le
#print axioms Qtsl.DiamondSite.InteriorMem.interpolate
#print axioms Qtsl.DiamondSite.diamondTopology
#print axioms Qtsl.DiamondSite.mem_diamondTopology_iff
#print axioms Qtsl.DiamondSite.mem_of_not_thick
#print axioms Qtsl.DiamondSite.mem_diamondTopology_degenerate_iff
#print axioms Qtsl.DiamondSite.minkowskiKit
#print axioms Qtsl.DiamondSite.minkowski_not_thick_degenerate
#print axioms Qtsl.DiamondSite.minkowski_spacelike_incomparable
#print axioms Qtsl.DiamondSite.minkowski_diamond_spacelike_pair
#print axioms Qtsl.DiamondSite.int_lt_no_chronologyKit

#print axioms Qtsl.OpenQuantum.trace_mul_nonneg
#print axioms Qtsl.OpenQuantum.re_trace_drift_le
#print axioms Qtsl.OpenQuantum.exp_contraction_of_deriv_le
#print axioms Qtsl.OpenQuantum.trace_eq_of_flow
#print axioms Qtsl.OpenQuantum.fence_transport
#print axioms Qtsl.OpenQuantum.gamma_mul_re_trace_le_zeta_of_invariant
#print axioms Qtsl.OpenQuantum.gksl_trace_eq_zero
#print axioms Qtsl.OpenQuantum.gksl_pairing
#print axioms Qtsl.QuantumRecords.classOperator_well_defined
#print axioms Qtsl.QuantumRecords.classOperator_well_defined_of_microcausal
#print axioms Qtsl.QuantumRecords.chain_linearization_unique
#print axioms Qtsl.QuantumRecords.records_imply_medium
#print axioms Qtsl.QuantumRecords.perfect_records_imply_medium
#print axioms Qtsl.QuantumRecords.mediumDecoherent_additivity
#print axioms Qtsl.QuantumRecords.weaklyConsistent_additivity
#print axioms Qtsl.QuantumRecords.medium_implies_records_of_exhaustive
#print axioms Qtsl.QuantumRecords.exists_orderDependent_without_commutation
#print axioms Qtsl.QuantumRecords.records_hypothesis_load_bearing
#print axioms Qtsl.QuantumRecords.hermiticity_load_bearing
#print axioms Qtsl.QuantumRecords.exists_weaklyConsistent_without_records
#print axioms Qtsl.QuantumRecords.classOperator_well_defined_minkowski

-- quantum descent on the derived diamond site (QuantumDescent)
#print axioms Qtsl.QuantumDescent.diamondTopology_factors
#print axioms Qtsl.QuantumDescent.diamondTopology_eq_of_chron_eq
#print axioms Qtsl.QuantumDescent.Vee.no_chronologyKit
#print axioms Qtsl.QuantumDescent.separates_of_interior_attained
#print axioms Qtsl.QuantumDescent.bell_mul_bell
#print axioms Qtsl.QuantumDescent.bell_not_product
#print axioms Qtsl.QuantumDescent.qubitNet_pair_not_separating
#print axioms Qtsl.QuantumDescent.exists_states_agreeing_not_equal
#print axioms Qtsl.QuantumDescent.pure_marginal_rigidity
#print axioms Qtsl.QuantumDescent.pair_agreement_determines_at_product
#print axioms Qtsl.QuantumDescent.pairSieve_not_covering
#print axioms Qtsl.QuantumDescent.pairSieve_not_covering_kit
#print axioms Qtsl.QuantumDescent.qubitNet_separates_derived
#print axioms Qtsl.QuantumDescent.span_union_ne_top
#print axioms Qtsl.QuantumDescent.adjoin_union_eq_top
#print axioms Qtsl.QuantumDescent.badNet_not_separating
#print axioms Qtsl.QuantumDescent.badNet_not_interior_attained

-- the outer-storey probe: order-index decoherence + two BFV axioms (QuantumOuterStorey)
#print axioms Qtsl.QuantumOuterStorey.switch_not_mediumDecoherent
#print axioms Qtsl.QuantumOuterStorey.switch_no_records
#print axioms Qtsl.QuantumOuterStorey.controlledSwitch_mediumDecoherent
#print axioms Qtsl.QuantumOuterStorey.controlledSwitch_additivity
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_isState
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_mixed_agree_on_pair
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_ne_mixed
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_not_idempotent
#print axioms Qtsl.QuantumOuterStorey.qubitNet_einstein_causality
#print axioms Qtsl.QuantumOuterStorey.qubitNet_timeslice_surrogate

-- general-stratum containment (ContainmentGeneral)
#print axioms Qtsl.Imprecise.ENNRat.add_eq_max_iff
#print axioms Qtsl.Imprecise.sublevel_compositeG_subset_glueSetG
#print axioms Qtsl.Imprecise.certificate_transfer
#print axioms Qtsl.Imprecise.binaryComposite_eq_glue_iff
#print axioms Qtsl.Imprecise.binaryComposite_eq_glue_of_isCrisp_left
#print axioms Qtsl.Imprecise.forall_sublevel_eq_iff
#print axioms Qtsl.Imprecise.binaryComposite_ne_glue
#print axioms Qtsl.Imprecise.sublevel_ssubset_glue_witness
#print axioms Qtsl.Imprecise.isClosed_glueSetG
#print axioms Qtsl.Imprecise.lowerSemicontinuous_addComposite
#print axioms Qtsl.Imprecise.isClosed_pmGlueSet
#print axioms Qtsl.Imprecise.sublevel_pmComposite_subset_glue

-- covariance transport on the derived diamond site (QuantumCovariance)
#print axioms Qtsl.DiamondSite.Diamond.map_symm_map
#print axioms Qtsl.DiamondSite.Diamond.map_le_map_iff
#print axioms Qtsl.QuantumCovariance.interiorMem_map_iff
#print axioms Qtsl.DiamondSite.ChronologyKit.map_chron_iff
#print axioms Qtsl.QuantumCovariance.toMixingKit_map
#print axioms Qtsl.QuantumCovariance.thick_map_iff
#print axioms Qtsl.QuantumCovariance.mem_diamondTopology_congr
#print axioms Qtsl.QuantumCovariance.mem_diamondTopology_congr_kit
#print axioms Qtsl.QuantumCovariance.coverPreserving_diamondTopology
#print axioms Qtsl.QuantumCovariance.separatesSieve_map_iff
#print axioms Qtsl.QuantumCovariance.map_separates_derived_of_interior_attained
#print axioms Qtsl.QuantumCovariance.minkTranslate_chron_iff
#print axioms Qtsl.QuantumCovariance.minkTranslate_ne_self
#print axioms Qtsl.QuantumCovariance.qubitNet_map_translate_separates_derived
#print axioms Qtsl.QuantumCovariance.qubitNet_map_translate_alg_D₁

-- the state presheaf and the record shadow (QuantumStates)
#print axioms Qtsl.QuantumStates.statePresheaf_ext
#print axioms Qtsl.QuantumStates.statePresheaf_ext_of_interior_attained
#print axioms Qtsl.QuantumStates.exists_distinct_classes_agreeing_on_pair
#print axioms Qtsl.QuantumStates.isSeparatedFor_statePresheaf_of_interior_attained
#print axioms Qtsl.QuantumStates.vecMulVec_polarization
#print axioms Qtsl.QuantumStates.phi_vecMulVec_star_swap
#print axioms Qtsl.QuantumStates.densityMatrixOf_trace_repr
#print axioms Qtsl.QuantumStates.existsUnique_isState_traceRepr
#print axioms Qtsl.QuantumStates.recordShadow_congr
#print axioms Qtsl.QuantumStates.recordShadowQ_restrict
#print axioms Qtsl.QuantumStates.recordShadowPMF_mix
#print axioms Qtsl.QuantumStates.exp_mix_mem_band
#print axioms Qtsl.QuantumStates.recordsBranchPMF
#print axioms Qtsl.QuantumStates.branchWeight_total
#print axioms Qtsl.QuantumStates.exists_branchWeight_coarse_not_additive
#print axioms Qtsl.QuantumStates.locallyEqual_map_iff
#print axioms Qtsl.QuantumStates.statePresheafCongr_restrict
#print axioms Qtsl.QuantumStates.recordShadowQ_map
#print axioms Qtsl.QuantumStates.recordShadowQ_separates_bell_mixed
#print axioms Qtsl.QuantumStates.exists_shadow_lowerE_lt_upperE

-- Cauchy-determinacy under a mechanism profile (QuantumDeterminacy)
#print axioms Qtsl.QuantumDeterminacy.heisenbergNet_alg_eq_top_of_commonSlice
#print axioms Qtsl.QuantumDeterminacy.heisenbergNet_alg_eq_of_commonSlice
#print axioms Qtsl.QuantumDeterminacy.statePresheaf_restriction_bijective_of_alg_eq
#print axioms Qtsl.QuantumDeterminacy.heisenbergNet_commonSlice_restriction_bijective
#print axioms Qtsl.QuantumDeterminacy.alg_eq_transport
#print axioms Qtsl.QuantumDeterminacy.restriction_bijective_transport
#print axioms Qtsl.QuantumDeterminacy.qubitFactors_exhaustive
#print axioms Qtsl.QuantumDeterminacy.heisenbergQubitNet_alg_Eslice
#print axioms Qtsl.QuantumDeterminacy.heisenbergQubitNet_Eslice_restriction_bijective
#print axioms Qtsl.QuantumDeterminacy.qubitNet_alg_Eslice
#print axioms Qtsl.QuantumDeterminacy.qubitNet_Eslice_restriction_not_injective
#print axioms Qtsl.QuantumDeterminacy.heisenbergNet_const_id_alg_eq_qubitNet
#print axioms Qtsl.QuantumDeterminacy.qubitNet_alg_eq_of_sites_mem
#print axioms Qtsl.QuantumDeterminacy.isingU_add
#print axioms Qtsl.QuantumDeterminacy.hasDerivAt_isingEvolution
#print axioms Qtsl.QuantumDeterminacy.isingEvolution_trace
#print axioms Qtsl.QuantumDeterminacy.gkslDag_mul_of_isEmpty
#print axioms Qtsl.QuantumDeterminacy.exists_gkslDag_not_leibniz
#print axioms Qtsl.QuantumDeterminacy.isingQubitNet_slice_determinacy
#print axioms Qtsl.QuantumDeterminacy.isingQubitNet_slice_restriction_bijective
#print axioms Qtsl.QuantumDeterminacy.isingQubitNet_translate_slice_determinacy

-- Assembly: the locally covariant kinematic fragment (QuantumAssembly)
#print axioms Qtsl.QuantumAssembly.qubitNet_alg_def
#print axioms Qtsl.QuantumAssembly.commute_left_right
#print axioms Qtsl.QuantumAssembly.qubitNet_einsteinCausal
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.isotony
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_surrogate_state
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_alg
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_state
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.separation
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.statePresheaf_isSeparatedFor
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.separation_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_alg_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.timeslice_genuine_state_map
#print axioms Qtsl.QuantumAssembly.Dp_Dq_pointwise_spacelike
#print axioms Qtsl.QuantumAssembly.isingQubitFragment
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_mechanismNet_eq
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_slice_determinacy
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_slice_restriction_bijective
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_translate_slice_determinacy
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_causality_point_pair
#print axioms Qtsl.QuantumAssembly.isingQubitFragment_shadow_separates_bell_mixed

-- Functoriality: the fragment pushforward and the Heisenberg-net commute (QuantumFunctoriality)
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_iff
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_iff'
#print axioms Qtsl.QuantumFunctoriality.inDiamond_map_symm_iff
#print axioms Qtsl.QuantumDescent.ObservableNet.ext
#print axioms Qtsl.QuantumDescent.MixingKit.ext
#print axioms Qtsl.DiamondSite.Diamond.map_refl
#print axioms Qtsl.DiamondSite.Diamond.map_trans
#print axioms Qtsl.QuantumDescent.ObservableNet.map_refl
#print axioms Qtsl.QuantumDescent.ObservableNet.map_trans
#print axioms Qtsl.QuantumDescent.MixingKit.map_refl
#print axioms Qtsl.QuantumDescent.MixingKit.map_trans
#print axioms Qtsl.QuantumFunctoriality.heisenbergNet_map_alg
#print axioms Qtsl.QuantumFunctoriality.heisenbergNet_map
#print axioms Qtsl.QuantumDeterminacy.CommonSlice.map
#print axioms Qtsl.QuantumFunctoriality.pointwise_spacelike_map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_refl
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_trans
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_alg
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.map_timeslice_genuine_state
#print axioms Qtsl.QuantumFunctoriality.minkowskiKit_toMixingKit_map_translate
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_slice_determinacy
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_separation
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_causality_point_pair
#print axioms Qtsl.QuantumFunctoriality.isingQubitFragment_map_shadow_separates_bell_mixed

-- Subregion embeddings: the fragment map beyond isomorphisms (QuantumEmbedding)
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.mono
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.injective
#print axioms Qtsl.QuantumEmbedding.CausalEmbedding.comp_assoc
#print axioms OrderIso.toCausalEmbedding
#print axioms Qtsl.DiamondSite.Diamond.push_le_push_iff
#print axioms Qtsl.DiamondSite.Diamond.push_toCausalEmbedding
#print axioms Qtsl.DiamondSite.Diamond.push_id
#print axioms Qtsl.DiamondSite.Diamond.push_comp
#print axioms Qtsl.QuantumEmbedding.inDiamond_push_iff
#print axioms Qtsl.QuantumEmbedding.inDiamond_push_exists
#print axioms Qtsl.DiamondSite.Diamond.inclusionEmbedding
#print axioms Qtsl.DiamondSite.Diamond.liftOfLe_push
#print axioms Qtsl.DiamondSite.Diamond.selfDiamond_push
#print axioms Qtsl.DiamondSite.Diamond.liftOfLe_le_selfDiamond
#print axioms Qtsl.QuantumDescent.MixingKit.pullback
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_interiorMem_iff
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_id
#print axioms Qtsl.QuantumDescent.MixingKit.pullback_comp
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_alg
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_id
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_comp
#print axioms Qtsl.QuantumDescent.ObservableNet.map_restrict
#print axioms Qtsl.QuantumDescent.MixingKit.map_pullback
#print axioms Qtsl.QuantumEmbedding.heisenbergNet_restrict_of_exhaustive
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict
#print axioms Qtsl.QuantumEmbedding.restrict_net_alg
#print axioms Qtsl.QuantumEmbedding.restrict_records
#print axioms Qtsl.QuantumEmbedding.restrict_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_id
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_comp
#print axioms Qtsl.QuantumEmbedding.qubitWorldline_mem_Dstar
#print axioms Qtsl.QuantumEmbedding.sojourn_of_qubitWorldline_mem_Dstar
#print axioms Qtsl.QuantumEmbedding.dstarSites_map
#print axioms Qtsl.QuantumEmbedding.dstarSites_on_worldlines
#print axioms Qtsl.QuantumEmbedding.dstar_attained
#print axioms Qtsl.QuantumEmbedding.dstarSojourn_exhaustive
#print axioms Qtsl.QuantumEmbedding.isingQubitFragmentOnDstar
#print axioms Qtsl.QuantumEmbedding.isingSub_net_alg_self
#print axioms Qtsl.QuantumEmbedding.isingSub_shadow_separates_bell_mixed
#print axioms Qtsl.QuantumEmbedding.isingSub_commonSlice
#print axioms Qtsl.QuantumEmbedding.isingSub_slice_determinacy
#print axioms Qtsl.QuantumEmbedding.isingSub_mechanismNet_restrict
#print axioms Qtsl.QuantumEmbedding.zzRecord_not_mem_leftFactor
#print axioms Qtsl.QuantumEmbedding.record_obligation_fails_at_D₁

-- Subregion extension: the covariant fragment map (QuantumExtension)
#print axioms Qtsl.QuantumDescent.ObservableNet.extend
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg_push
#print axioms Qtsl.QuantumDescent.ObservableNet.restrict_extend
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_restrict_alg_le
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_alg_le_iff
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_id
#print axioms Qtsl.QuantumDescent.ObservableNet.extend_comp
#print axioms Qtsl.QuantumExtension.heisenbergNet_extend
#print axioms Qtsl.QuantumExtension.commute_of_mem_iSup
#print axioms Qtsl.QuantumExtension.extend_alg_eq_sites
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.extend
#print axioms Qtsl.QuantumExtension.extend_net_alg
#print axioms Qtsl.QuantumExtension.extend_records
#print axioms Qtsl.QuantumExtension.extend_sites
#print axioms Qtsl.QuantumExtension.extend_ambient
#print axioms Qtsl.QuantumExtension.extend_mechanismNet
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.ext
#print axioms Qtsl.QuantumExtension.extend_pullback_interiorMem
#print axioms Qtsl.QuantumExtension.extend_push_attained
#print axioms Qtsl.QuantumExtension.extend_push_records
#print axioms Qtsl.QuantumAssembly.LCQFTFragment.restrict_extend
#print axioms Qtsl.QuantumExtension.extend_id_frag
#print axioms Qtsl.QuantumExtension.extend_comp_frag
#print axioms Qtsl.QuantumExtension.extend_restrict_net
#print axioms Qtsl.QuantumExtension.isingExtendedFragment
#print axioms Qtsl.QuantumExtension.isingExtended_net
#print axioms Qtsl.QuantumExtension.isingExtended_restrict
#print axioms Qtsl.QuantumExtension.isingExtended_shadow_separates_bell_mixed
#print axioms Qtsl.QuantumExtension.isingExtended_slice_determinacy
#print axioms Qtsl.QuantumExtension.emptyMixingKit
#print axioms Qtsl.QuantumExtension.emptyMixingKit_pullback_ne

-- Kit-extension non-uniqueness: two chronologies, one region (QuantumExtension)
#print axioms Qtsl.QuantumExtension.mink_chron_of_le_chron
#print axioms Qtsl.QuantumExtension.mink_chron_of_chron_le
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_chron_iff
#print axioms Qtsl.QuantumExtension.zPast
#print axioms Qtsl.QuantumExtension.zPast_chron_lo
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_pullback_eq
#print axioms Qtsl.QuantumExtension.minkowskiFutureKit_ne
#print axioms Qtsl.QuantumExtension.exists_distinct_kits_same_pullback
#print axioms Qtsl.QuantumExtension.extend_kit
#print axioms Qtsl.QuantumExtension.isingExtendedFragmentPast
#print axioms Qtsl.QuantumExtension.isingExtendedPast_net_eq
#print axioms Qtsl.QuantumExtension.isingExtendedPast_net
#print axioms Qtsl.QuantumExtension.isingExtendedPast_ne
#print axioms Qtsl.QuantumExtension.isingExtendedPast_restrict

#print axioms Qtsl.SdeGenerator.SdeProfile.gram_symm
#print axioms Qtsl.SdeGenerator.SdeProfile.gram_quadForm_nonneg
#print axioms Qtsl.SdeGenerator.generator_no_drivers
#print axioms Qtsl.SdeGenerator.generator_pure_drift
#print axioms Qtsl.SdeGenerator.generator_no_jump
#print axioms Qtsl.SdeGenerator.lam_nonneg_of_rate_row
#print axioms Qtsl.SdeGenerator.SdeDynkinVille.avoid_row
#print axioms Qtsl.SdeGenerator.SdeDynkinVille.avoid_row_div
#print axioms Qtsl.SdeGenerator.SdeDynkinVille.avoid_row_init
#print axioms Qtsl.SdeGenerator.SdeDynkinVille.discounted_deadline_row
#print axioms Qtsl.SdeGeneratorPoly.transferMix_add
#print axioms Qtsl.SdeGeneratorPoly.PolyProfile.gram_symm
#print axioms Qtsl.SdeGeneratorPoly.genPoly_eval_eq_generator
#print axioms Qtsl.SdeGeneratorPoly.continuous_aeval_real
#print axioms Qtsl.SdeMartingaleProblem.polyGradCLM_apply
#print axioms Qtsl.SdeMartingaleProblem.hasFDerivAt_eval_poly
#print axioms Qtsl.SdeMartingaleProblem.hasFDerivAt_aeval_poly
#print axioms Qtsl.SdeMartingaleProblem.rowCLM_pderiv_eq_polyGradCLM
#print axioms Qtsl.SdeMartingaleProblem.isC2Fn_poly
#print axioms Qtsl.SdeMartingaleProblem.MpSolution.supermartingale_of_gen_nonpos
#print axioms Qtsl.SdeMartingaleProblem.MpSolution.toSdeDynkinVille
#print axioms Qtsl.SdeMartingaleProblem.mp_avoid_row_of_genPoly
#print axioms Qtsl.SdeMartingaleProblem.mp_avoid_init_of_genPoly
#print axioms Qtsl.SdeMartingaleProblem.genPoly_zeroPoly
#print axioms Qtsl.SdeMartingaleProblem.generator_toSde_zeroPoly
#print axioms Qtsl.SdeMartingaleProblem.mp_control
#print axioms Qtsl.JumpDiffusion.transferSum_nil
#print axioms Qtsl.JumpDiffusion.transferSum_cons
#print axioms Qtsl.JumpDiffusion.transferSum_sub_self
#print axioms Qtsl.JumpDiffusion.JdProfile.gram_symm
#print axioms Qtsl.JumpDiffusion.JdProfile.gram_quadForm_nonneg
#print axioms Qtsl.JumpDiffusion.generator_one_dirac
#print axioms Qtsl.JumpDiffusion.generator_no_legs
#print axioms Qtsl.JumpDiffusion.lam_nonneg_of_rate_rows
#print axioms Qtsl.JumpDiffusion.aeval_transferMix
#print axioms Qtsl.JumpDiffusion.aeval_jump_sum
#print axioms Qtsl.JumpDiffusion.genPoly_eval_eq_generator
#print axioms Qtsl.JumpDiffusion.toJd_generator_one_dirac
#print axioms Qtsl.JumpDiffusion.two_leg_control
#print axioms Qtsl.JumpDiffusion.JdDynkinVille.avoid_row
#print axioms Qtsl.JumpDiffusion.JdDynkinVille.avoid_row_div
#print axioms Qtsl.JumpDiffusion.JdDynkinVille.avoid_row_init
#print axioms Qtsl.JumpDiffusion.JdDynkinVille.discounted_deadline_row
#print axioms Qtsl.JumpDiffusion.MpSolution.supermartingale_of_gen_nonpos
#print axioms Qtsl.JumpDiffusion.MpSolution.toJdDynkinVille
#print axioms Qtsl.JumpDiffusion.mp_avoid_row_of_genPoly
#print axioms Qtsl.JumpDiffusion.mp_avoid_init_of_genPoly
#print axioms Qtsl.JumpDiffusion.generator_toJd
#print axioms Qtsl.SdeMartingaleProblem.MpSolution.toJd
#print axioms Qtsl.JumpDiffusion.genPoly_idResetPoly
#print axioms Qtsl.JumpDiffusion.generator_toJd_idResetPoly
#print axioms Qtsl.JumpDiffusion.mp_control

-- Sheaf-grade descent: gluing and the intertwiner contrast (QuantumSheaf)
#print axioms Qtsl.QuantumSheaf.locallyEqual_of_alg_le
#print axioms Qtsl.QuantumSheaf.locallyEqual_of_alg_le_bot
#print axioms Qtsl.QuantumSheaf.stateClass_exists_rep
#print axioms Qtsl.QuantumSheaf.pureProd_ne_mixed
#print axioms Qtsl.QuantumSheaf.OverlapAttained.attained
#print axioms Qtsl.QuantumSheaf.statePresheaf_isSheafFor_of_overlap_attained
#print axioms Qtsl.QuantumSheaf.p_mem_Dpq
#print axioms Qtsl.QuantumSheaf.q_mem_Dpq
#print axioms Qtsl.QuantumSheaf.Dpq_le_of_mem
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dp
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dq
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dpq
#print axioms Qtsl.QuantumSheaf.qubitNet_overlapAttained
#print axioms Qtsl.QuantumSheaf.qubitNet_isSheafFor_derived
#print axioms Qtsl.QuantumSheaf.qubitNet_not_isSheafFor_pair
#print axioms Qtsl.QuantumSheaf.badNet_not_isSheafFor_interior
#print axioms Qtsl.QuantumSheaf.intertwinerDescends_of_interior_attained
#print axioms Qtsl.QuantumSheaf.intertwinerDescends_of_le_adjoin
#print axioms Qtsl.QuantumSheaf.qubitNet_pairSieve_intertwinerDescends
#print axioms Qtsl.QuantumSheaf.qubitNet_pair_contrast

-- Categorified descent: the attained-regime equivalence and the
-- multiplicity obstruction (QuantumStack)
#print axioms Qtsl.QuantumStack.FinRep.dim_eq_of_iso
#print axioms Qtsl.QuantumStack.repFunctor
#print axioms Qtsl.QuantumStack.tautRep
#print axioms Qtsl.DiamondSite.ChronologyKit.interior_directed
#print axioms Qtsl.QuantumStack.theta_app_val_eq
#print axioms Qtsl.QuantumStack.descentComparison_faithful
#print axioms Qtsl.QuantumStack.descentComparison_full_interior
#print axioms Qtsl.QuantumStack.descentComparison_essSurj_interior
#print axioms Qtsl.QuantumStack.descentComparison_isEquivalence_interior
#print axioms Qtsl.QuantumStack.qubitNet_stack_attained
#print axioms Qtsl.QuantumStack.intertwines_of_le_adjoin
#print axioms Qtsl.QuantumStack.descentComparison_pair_full
#print axioms Qtsl.QuantumStack.overlap_scalar
#print axioms Qtsl.QuantumStack.wingPi_compat
#print axioms Qtsl.QuantumStack.wingDatum
#print axioms Qtsl.QuantumStack.no_unital_hom_top_to_dim_two
#print axioms Qtsl.QuantumStack.wingDatum_not_in_essImage
#print axioms Qtsl.QuantumStack.descentComparison_pair_not_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_gapped_not_full
#print axioms Qtsl.QuantumStack.emptySieve_covering_corner
#print axioms Qtsl.QuantumStack.descentComparison_corner_not_faithful
#print axioms Qtsl.QuantumStack.badNet_not_full_interior

-- Necessity of the attained-regime hypotheses: the two-island site and
-- the padded fence (QuantumStackNecessity)
#print axioms Qtsl.QuantumStack.DescentDatum.componentIso
#print axioms Qtsl.QuantumStack.rectOne_eq_one
#print axioms Qtsl.QuantumStack.Theta.mixingKit
#print axioms Qtsl.QuantumStack.Theta.no_chronologyKit
#print axioms Qtsl.QuantumStack.theta_not_interiorDirected
#print axioms Qtsl.QuantumStack.thetaNet_attained
#print axioms Qtsl.QuantumStack.theta_member_shape
#print axioms Qtsl.QuantumStack.islandDatum
#print axioms Qtsl.QuantumStack.islandDatum_not_in_essImage
#print axioms Qtsl.QuantumStack.descentComparison_theta_not_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_theta_faithful
#print axioms Qtsl.QuantumStack.descentComparison_theta_not_full
#print axioms Qtsl.QuantumStack.not_interiorReachable_of_le_cornerD
#print axioms Qtsl.QuantumStack.paddedSieve_covering
#print axioms Qtsl.QuantumStack.paddedDatum
#print axioms Qtsl.QuantumStack.paddedDatum_not_in_essImage
#print axioms Qtsl.QuantumStack.descentComparison_padded_not_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_padded_faithful

-- Sufficiency of directedness: the joined two-strand site
-- (QuantumStackSufficiency)
#print axioms Qtsl.QuantumStack.ThetaJoined.chronologyKit
#print axioms Qtsl.QuantumStack.ThetaJoined.pt_false_not_le_pt_true
#print axioms Qtsl.QuantumStack.ThetaJoined.pt_true_not_le_pt_false
#print axioms Qtsl.QuantumStack.leftIslandJ_interior
#print axioms Qtsl.QuantumStack.islandRoofJ_interior
#print axioms Qtsl.QuantumStack.thetaJNet_attained
#print axioms Qtsl.QuantumStack.thetaJ_interiorDirected
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_isEquivalence
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_full
#print axioms Qtsl.QuantumStack.thetaJ_datum_in_essImage
#print axioms Qtsl.QuantumStack.thetaJ_datum_island_dim_eq
#print axioms Qtsl.QuantumStack.thetaJ_no_island_datum

-- Normality: the directed-regime fence — the tail-character datum on
-- the canonical interior cover (QuantumStackNormality)
#print axioms Qtsl.QuantumStack.Dchain_interior
#print axioms Qtsl.QuantumStack.Dchain_le_iff
#print axioms Qtsl.QuantumStack.Dstar_not_le_Dchain
#print axioms Qtsl.QuantumStack.interior_le_Dchain
#print axioms Qtsl.QuantumStack.chainSieve_eq_interiorSieve
#print axioms Qtsl.QuantumStack.chainSieve_covering
#print axioms Qtsl.QuantumStack.chainSieve_no_top
#print axioms Qtsl.QuantumStack.blockIndicator_mem
#print axioms Qtsl.QuantumStack.blockIndicator_not_mem
#print axioms Qtsl.QuantumStack.singleIndicator_not_mem
#print axioms Qtsl.QuantumStack.tailHom
#print axioms Qtsl.QuantumStack.tailNet_Dchain
#print axioms Qtsl.QuantumStack.tailNet_Dstar
#print axioms Qtsl.QuantumStack.tailNet_not_interior_attained
#print axioms Qtsl.QuantumStack.qubitNet_attained_on_chain
#print axioms Qtsl.QuantumStack.tailDatum
#print axioms Qtsl.QuantumStack.tailDatum_in_essImage
#print axioms Qtsl.QuantumStack.glue_dim_one
#print axioms Qtsl.QuantumStack.tail_restriction_no_density
#print axioms Qtsl.QuantumStack.tailDatum_no_density_glue
#print axioms Qtsl.QuantumStack.glue_π_member
#print axioms Qtsl.QuantumStack.glue_π_unique
#print axioms Qtsl.QuantumStack.subalgebraChain_stabilizes
#print axioms Qtsl.QuantumStack.observableNet_chain_stabilizes
#print axioms Qtsl.QuantumStack.subalgebraFamily_directed_attains
#print axioms Qtsl.QuantumStack.observableNet_directed_attains
#print axioms Qtsl.QuantumStack.subalgebraFamily_generated_attains
#print axioms Qtsl.QuantumStack.observableNet_generated_attains

-- Holonomy: the second obstruction at the pair cover — the
-- controlled-Z twist at matched multiplicity, and the product
-- vanishing class (QuantumStackHolonomy)
#print axioms Qtsl.QuantumStackHolonomy.cz_mul_self
#print axioms Qtsl.QuantumStackHolonomy.cz_not_kronecker
#print axioms Qtsl.QuantumStackHolonomy.key_noncomm
#print axioms Qtsl.QuantumStackHolonomy.twistDatum
#print axioms Qtsl.QuantumStackHolonomy.twistDatum_obj_dim
#print axioms Qtsl.QuantumStackHolonomy.czDatum_dim_eq_restriction
#print axioms Qtsl.QuantumStackHolonomy.czDatum_not_in_essImage
#print axioms Qtsl.QuantumStackHolonomy.descentComparison_pair_not_essSurj_matched
#print axioms Qtsl.QuantumStackHolonomy.productTwist_in_essImage

-- Full faithfulness at operator grade against mathlib's von Neumann
-- algebras (QuantumStackVonNeumann)
#print axioms VonNeumannAlgebra.generate
#print axioms VonNeumannAlgebra.coe_generate
#print axioms VonNeumannAlgebra.subset_generate
#print axioms VonNeumannAlgebra.generate_le
#print axioms VonNeumannAlgebra.commutant_anti
#print axioms VonNeumannAlgebra.mem_top
#print axioms VonNeumannAlgebra.commute_all_of_forall_commute
#print axioms Qtsl.QuantumStack.SubRep.Hom.proj_left
#print axioms Qtsl.QuantumStack.SubRep.Hom.proj_right
#print axioms Qtsl.QuantumStack.descentComparisonW
#print axioms Qtsl.QuantumStack.thetaW_app_val_eq
#print axioms Qtsl.QuantumStack.descentComparisonW_faithful
#print axioms Qtsl.QuantumStack.app_val_eq_of_connected
#print axioms Qtsl.QuantumStack.netUnion_star_closed
#print axioms Qtsl.QuantumStack.descentComparisonW_full
#print axioms Qtsl.QuantumStack.interiorSieve_connected
#print axioms Qtsl.QuantumStack.descentComparisonW_full_interior
#print axioms Qtsl.QuantumStack.descentComparisonW_faithful_interior
#print axioms Qtsl.QuantumStack.le_generate_of_attained
#print axioms Qtsl.QuantumStack.constWNet_full_interior
#print axioms Qtsl.QuantumStack.unitSubRep
#print axioms Qtsl.QuantumStack.descentComparisonW_empty_not_faithful

-- The (ℰ, D)-structure: quantum measures on a finite index and the
-- conservativity of records-forced classicalization (QuantumDForm)
#print axioms Qtsl.QuantumDForm.QuantumMeasure.eventForm_conj
#print axioms Qtsl.QuantumDForm.QuantumMeasure.eventForm_union_left
#print axioms Qtsl.QuantumDForm.QuantumMeasure.eventGram_posSemidef
#print axioms Qtsl.QuantumDForm.QuantumMeasure.sorkinMeasure_union
#print axioms Qtsl.QuantumDForm.QuantumMeasure.sorkin_grade3
#print axioms Qtsl.QuantumDForm.presentationGram_posSemidef
#print axioms Qtsl.QuantumDForm.QuantumMeasure.probRow_nonneg
#print axioms Qtsl.QuantumDForm.QuantumMeasure.classical_eventForm
#print axioms Qtsl.QuantumDForm.QuantumMeasure.isDiagonal_eventForm_inter
#print axioms Qtsl.QuantumDForm.QuantumMeasure.isDiagonal_additive
#print axioms Qtsl.QuantumDForm.QuantumMeasure.isDiagonal_eq_classical
#print axioms Qtsl.QuantumDForm.QuantumMeasure.records_conservativity
#print axioms Qtsl.QuantumDForm.QuantumMeasure.records_eventForm
#print axioms Qtsl.QuantumDForm.QuantumMeasure.gnsForm_self_nonneg
#print axioms Qtsl.QuantumDForm.QuantumMeasure.mem_gnsNull_iff
#print axioms Qtsl.QuantumDForm.QuantumMeasure.defectVector_mem_gnsNull
#print axioms Qtsl.QuantumDForm.QuantumMeasure.mk_single_union
#print axioms Qtsl.QuantumDForm.QuantumMeasure.span_atomClasses
#print axioms Qtsl.QuantumDForm.switchMeasure_interference
#print axioms Qtsl.QuantumDForm.switchMeasure_not_isDiagonal
#print axioms Qtsl.QuantumDForm.controlledMeasure_eq_classical
#print axioms Qtsl.QuantumDForm.zMeasure_conservative
#print axioms Qtsl.QuantumDForm.zMeasure_probRow

-- The GMH converse completed on the two-fibre toy: the reconstruction
-- theorem's hypothesis landscape below exhaustiveness (QuantumConverse)
#print axioms Qtsl.QuantumConverse.records_force_real_overlap
#print axioms Qtsl.QuantumConverse.projective_records_force_weight_overlap
#print axioms Qtsl.QuantumConverse.medium_implies_records_of_real_overlap
#print axioms Qtsl.QuantumConverse.exhaustive_overlap_eq_weight
#print axioms Qtsl.QuantumConverse.records_of_exhaustive_via_overlap
#print axioms Qtsl.QuantumConverse.branchProjector_idem
#print axioms Qtsl.QuantumConverse.medium_implies_projective_records_of_exhaustive
#print axioms Qtsl.QuantumConverse.phaseFamily_mediumDecoherent
#print axioms Qtsl.QuantumConverse.phaseFamily_no_records
#print axioms Qtsl.QuantumConverse.roomFamily_mediumDecoherent
#print axioms Qtsl.QuantumConverse.roomFamily_no_records
#print axioms Qtsl.QuantumConverse.controlledSwitch_not_exhaustive
#print axioms Qtsl.QuantumConverse.controlledSwitch_records
#print axioms Qtsl.QuantumConverse.controlledSwitch_no_projective_records
#print axioms Qtsl.QuantumConverse.controlled_records_iff_isDiagonal
#print axioms Qtsl.QuantumConverse.switch_records_iff_isDiagonal
#print axioms Qtsl.QuantumConverse.zPair_projective_records

-- (QuantumHierarchy)
#print axioms Qtsl.QuantumHierarchy.RecordSupported.mediumDecoherent
#print axioms Qtsl.QuantumHierarchy.phaseFamily_not_recordSupported
#print axioms Qtsl.QuantumHierarchy.zyFamily_weaklyConsistent
#print axioms Qtsl.QuantumHierarchy.zyFamily_not_mediumDecoherent
#print axioms Qtsl.QuantumHierarchy.records_medium_weak_strict_hierarchy
#print axioms Qtsl.QuantumHierarchy.projectiveRecords_of_mediumDecoherent_of_exhaustive
#print axioms Qtsl.QuantumHierarchy.recordSupported_iff_mediumDecoherent_of_exhaustive
#print axioms Qtsl.QuantumHierarchy.companion_exhaustiveness_load_bearing

-- The completeness tier: GMH's ∑R = 1 located exactly at exhaustiveness
-- (QuantumCompleteness)
#print axioms Qtsl.QuantumCompleteness.complete_records_force_exhaustive
#print axioms Qtsl.QuantumCompleteness.complete_orthogonal_records_idem
#print axioms Qtsl.QuantumCompleteness.complete_records_force_weight_overlap
#print axioms Qtsl.QuantumCompleteness.complete_records_norm
#print axioms Qtsl.QuantumCompleteness.complete_records_conservativity
#print axioms Qtsl.QuantumCompleteness.projective_records_complete_of_exhaustive
#print axioms Qtsl.QuantumCompleteness.medium_implies_complete_records_of_exhaustive
#print axioms Qtsl.QuantumCompleteness.complete_records_iff_exhaustive
#print axioms Qtsl.QuantumCompleteness.controlledSwitch_no_complete_records
#print axioms Qtsl.QuantumCompleteness.zPair_exhaustive
#print axioms Qtsl.QuantumCompleteness.zPair_mediumDecoherent
#print axioms Qtsl.QuantumCompleteness.zPair_complete_projective_records
#print axioms Qtsl.QuantumCompleteness.zState_unit
#print axioms Qtsl.QuantumCompleteness.zMeasure_norm_from_completeness
#print axioms Qtsl.QuantumCompleteness.soloFamily_projective_records
#print axioms Qtsl.QuantumCompleteness.soloFamily_not_exhaustive
#print axioms Qtsl.QuantumCompleteness.soloFamily_no_complete_records

-- Dowker–Kent consistent sets: the domain of set selection, the history
-- cap, and the kernel-checked instance of the DK profligacy construction
-- (QuantumConsistentSets)
#print axioms Qtsl.QuantumConsistentSets.dkSet_exhaustive
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_projective_records
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_complete_records
#print axioms Qtsl.QuantumConsistentSets.extend_decoherence_same_base
#print axioms Qtsl.QuantumConsistentSets.dkConsistent_card_nonzero_le
#print axioms Qtsl.QuantumConsistentSets.maximallyExtended_of_card_eq
#print axioms Qtsl.QuantumConsistentSets.sigma0_consistent
#print axioms Qtsl.QuantumConsistentSets.dkRotation_consistent
#print axioms Qtsl.QuantumConsistentSets.dkRotation_nontrivial
#print axioms Qtsl.QuantumConsistentSets.sigma0_not_maximallyExtended
#print axioms Qtsl.QuantumConsistentSets.dkFamily_nontrivial
#print axioms Qtsl.QuantumConsistentSets.dkFamily_extension_records
#print axioms Qtsl.QuantumConsistentSets.dkFamily_injOn
#print axioms Qtsl.QuantumConsistentSets.dkFamily_continuous

-- Dowker–Kent Lemma 2, fully quantified: the profligacy of consistent sets
-- (QuantumProfligacy)
#print axioms Qtsl.QuantumProfligacy.outer_mulVec
#print axioms Qtsl.QuantumProfligacy.exists_smul_unit
#print axioms Qtsl.QuantumProfligacy.exists_unit_dotProduct_orthogonal
#print axioms Qtsl.QuantumProfligacy.card_nonzero_lt_of_not_maximallyExtended
#print axioms Qtsl.QuantumProfligacy.genPhiPlus_orth_genPhiMinus
#print axioms Qtsl.QuantumProfligacy.genP3_mulVec_target
#print axioms Qtsl.QuantumProfligacy.genRotation_consistent
#print axioms Qtsl.QuantumProfligacy.genRotation_nontrivialExtension
#print axioms Qtsl.QuantumProfligacy.dkGeneralFamily_injOn
#print axioms Qtsl.QuantumProfligacy.dkGeneralFamily_continuous
#print axioms Qtsl.QuantumProfligacy.dowkerKent_lemma2
#print axioms Qtsl.QuantumProfligacy.dowkerKent_lemma2_of_not_maximallyExtended
#print axioms Qtsl.QuantumProfligacy.maximallyExtended_iff_card_eq

-- (ℰ,D)-transport: the quantum measure riding the covariance machinery
-- (QuantumTransport)
#print axioms Qtsl.QuantumTransport.map_gram
#print axioms Qtsl.QuantumTransport.map_refl
#print axioms Qtsl.QuantumTransport.map_symm_map
#print axioms Qtsl.QuantumTransport.map_map_symm
#print axioms Qtsl.QuantumTransport.map_trans
#print axioms Qtsl.QuantumTransport.map_eventForm
#print axioms Qtsl.QuantumTransport.map_sorkinMeasure
#print axioms Qtsl.QuantumTransport.map_interference
#print axioms Qtsl.QuantumTransport.map_isDiagonal_iff
#print axioms Qtsl.QuantumTransport.map_probRow
#print axioms Qtsl.QuantumTransport.classical_map
#print axioms Qtsl.QuantumTransport.map_isDiagonal_eq_classical
#print axioms Qtsl.QuantumTransport.classicalization_map_comm
#print axioms Qtsl.QuantumTransport.ofPresentation_map
#print axioms Qtsl.QuantumTransport.records_conservativity_map
#print axioms Qtsl.QuantumTransport.mapDiamond_gram
#print axioms Qtsl.QuantumTransport.mapDiamond_isDiagonal_iff
#print axioms Qtsl.QuantumTransport.switchMeasure_map_interference
#print axioms Qtsl.QuantumTransport.controlledMeasure_map_isDiagonal
#print axioms Qtsl.QuantumTransport.zMeasure_map_conservative
#print axioms Qtsl.QuantumCoarseGraining.sum_fiberEvent
#print axioms Qtsl.QuantumCoarseGraining.sum_fiber
#print axioms Qtsl.QuantumCoarseGraining.pushforward_gram
#print axioms Qtsl.QuantumCoarseGraining.pushforward_eventForm
#print axioms Qtsl.QuantumCoarseGraining.pushforward_sorkinMeasure
#print axioms Qtsl.QuantumCoarseGraining.pushforward_interference
#print axioms Qtsl.QuantumCoarseGraining.pushforward_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.pushforward_probRow
#print axioms Qtsl.QuantumCoarseGraining.pushforward_probRow_of_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.classical_pushforward
#print axioms Qtsl.QuantumCoarseGraining.pushforward_isDiagonal_eq_classical
#print axioms Qtsl.QuantumCoarseGraining.classicalization_pushforward_comm
#print axioms Qtsl.QuantumCoarseGraining.pushforward_id
#print axioms Qtsl.QuantumCoarseGraining.pushforward_equiv
#print axioms Qtsl.QuantumCoarseGraining.pushforward_comp
#print axioms Qtsl.QuantumCoarseGraining.map_pushforward
#print axioms Qtsl.QuantumCoarseGraining.pushforward_map
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_isHermitian
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_orthogonal
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_correlated
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_complete
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_idem
#print axioms Qtsl.QuantumCoarseGraining.strong_records_coarsen
#print axioms Qtsl.QuantumCoarseGraining.decoherenceFunctional_coarsenFamily
#print axioms Qtsl.QuantumCoarseGraining.pushforward_ofPresentation
#print axioms Qtsl.QuantumCoarseGraining.records_conservativity_pushforward
#print axioms Qtsl.QuantumCoarseGraining.coarsenFamily_idem_needs_orthogonality
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_not_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_pushforward_isDiagonal
#print axioms Qtsl.QuantumCoarseGraining.mergeMeasure_pushforward_probRow
#print axioms Qtsl.QuantumCoarseGraining.zMeasure_pushforward_conservative

-- (QuantumDiamondMeasure)
#print axioms Qtsl.QuantumDiamondMeasure.degeneracy_map
#print axioms Qtsl.QuantumDiamondMeasure.mapDiamond_pushforward_degeneracy
#print axioms Qtsl.QuantumDiamondMeasure.diamond_cases
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_pointLo
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_pointHi
#print axioms Qtsl.QuantumDiamondMeasure.diamondEquiv_symm_span
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_gram_pointLo_span
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_not_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_eq
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_probRow_point
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_probRow_extended
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_pushforward_classical
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_mapDiamond_gram
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_mapDiamond_not_isDiagonal
#print axioms Qtsl.QuantumDiamondMeasure.diamondMeasure_covariant_coarse
#print axioms Qtsl.QuantumDiamondMeasure.pushforward_diamondEquiv

-- (QuantumTower)
#print axioms Qtsl.QuantumTower.offDiagMass_nonneg
#print axioms Qtsl.QuantumTower.offDiagMass_eq_zero_iff
#print axioms Qtsl.QuantumTower.fiberEvent_disjoint
#print axioms Qtsl.QuantumTower.offDiagMass_pushforward_le
#print axioms Qtsl.QuantumTower.zero_mem_interferenceSpectrum
#print axioms Qtsl.QuantumTower.interferenceSpectrum_of_isDiagonal
#print axioms Qtsl.QuantumTower.interferenceSpectrum_pushforward_subset
#print axioms Qtsl.QuantumTower.DFormStorey.id_val
#print axioms Qtsl.QuantumTower.DFormStorey.comp_val
#print axioms Qtsl.QuantumTower.towerFunctor_obj
#print axioms Qtsl.QuantumTower.towerLeg_pushforward
#print axioms Qtsl.QuantumTower.towerLeg_self
#print axioms Qtsl.QuantumTower.towerLeg_succ
#print axioms Qtsl.QuantumTower.towerLeg_trans
#print axioms Qtsl.QuantumTower.stageMeasure_isDiagonal_mono
#print axioms Qtsl.QuantumTower.stageMeasure_classical_absorbing
#print axioms Qtsl.QuantumTower.offDiagMass_stageMeasure_antitone
#print axioms Qtsl.QuantumTower.interferenceSpectrum_stageMeasure_antitone
#print axioms Qtsl.QuantumTower.towerMeasure_zero
#print axioms Qtsl.QuantumTower.towerMeasure_one
#print axioms Qtsl.QuantumTower.towerMeasure_zero_not_isDiagonal
#print axioms Qtsl.QuantumTower.towerMeasure_one_isDiagonal
#print axioms Qtsl.QuantumTower.towerMeasure_isDiagonal_of_pos
#print axioms Qtsl.QuantumTower.towerMeasure_classical_of_pos
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_one
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_pos
#print axioms Qtsl.QuantumTower.towerMeasure_offDiagMass_lt
#print axioms Qtsl.QuantumTower.diamondMeasure_interference_pointLo_span
#print axioms Qtsl.QuantumTower.towerMeasure_interferenceSpectrum_ssubset

-- (QuantumStrictness)
#print axioms Qtsl.QuantumStrictness.blockMass_nonneg
#print axioms Qtsl.QuantumStrictness.blockMass_of_ne
#print axioms Qtsl.QuantumStrictness.blockContribution_le
#print axioms Qtsl.QuantumStrictness.offDiagMass_eq_sum_blockMass
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_eq_iff
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_iff
#print axioms Qtsl.QuantumStrictness.nonCancelling_iff
#print axioms Qtsl.QuantumStrictness.not_nonCancelling_of_merged_pair
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_of_merged_pair
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_lt_of_cancellation
#print axioms Qtsl.QuantumStrictness.nonCancelling_of_injective
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_of_injective
#print axioms Qtsl.QuantumStrictness.nonCancelling_of_isDiagonal
#print axioms Qtsl.QuantumStrictness.offDiagMass_pushforward_of_isDiagonal
#print axioms Qtsl.QuantumStrictness.offDiagMass_stageMeasure_succ_lt_iff
#print axioms Qtsl.QuantumStrictness.diamondMeasure_not_nonCancelling
#print axioms Qtsl.QuantumStrictness.diamondMeasure_pushforward_gram_true_false
#print axioms Qtsl.QuantumStrictness.diamondMeasure_cancellation_strict
#print axioms Qtsl.QuantumStrictness.diamondMeasure_gram_pointLo_pointHi
#print axioms Qtsl.QuantumStrictness.diamondMeasure_merged_pair_strict
#print axioms Qtsl.QuantumStrictness.towerMeasure_nonCancelling_of_pos
#print axioms Qtsl.QuantumStrictness.towerMeasure_offDiagMass_succ_eq_of_pos
#print axioms Qtsl.QuantumStrictness.alignMeasure_not_isDiagonal
#print axioms Qtsl.QuantumStrictness.alignMeasure_offDiagMass_pos
#print axioms Qtsl.QuantumStrictness.alignMeasure_nonCancelling
#print axioms Qtsl.QuantumStrictness.alignMeasure_offDiagMass_pushforward_eq
#print axioms Qtsl.QuantumStrictness.alignMeasure_pushforward_not_isDiagonal

-- (QuantumAlignment)
#print axioms Qtsl.QuantumAlignment.re_conj_mul_le_norm
#print axioms Qtsl.QuantumAlignment.eq_norm_mul_of_re_conj_mul_eq
#print axioms Qtsl.QuantumAlignment.norm_sum_eq_sum_norm_iff
#print axioms Qtsl.QuantumAlignment.crossBlock_norm_additive_iff
#print axioms Qtsl.QuantumAlignment.nonCancelling_iff_aligned
#print axioms Qtsl.QuantumAlignment.offDiagMass_pushforward_eq_iff_aligned
#print axioms Qtsl.QuantumAlignment.offDiagMass_pushforward_lt_iff_aligned
#print axioms Qtsl.QuantumAlignment.alignMeasure_crossAligned
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_gram_12
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_isDiagonal
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_crossAligned
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_not_nonCancelling
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_offDiagMass_pushforward_lt
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_pushforward_gram_01_ne_zero
#print axioms Qtsl.QuantumAlignment.dephaseMeasure_pushforward_gram_10_ne_zero

-- (QuantumSpectrum)
#print axioms Qtsl.QuantumSpectrum.saturated_fiberEvent
#print axioms Qtsl.QuantumSpectrum.saturated_of_injective
#print axioms Qtsl.QuantumSpectrum.fiberEvent_image_of_saturated
#print axioms Qtsl.QuantumSpectrum.disjoint_image_of_saturated
#print axioms Qtsl.QuantumSpectrum.interference_empty_left
#print axioms Qtsl.QuantumSpectrum.interference_empty_right
#print axioms Qtsl.QuantumSpectrum.mem_interferenceSpectrum_pushforward
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_eq
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_ssubset_iff
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_pushforward_of_injective
#print axioms Qtsl.QuantumSpectrum.interferenceSpectrum_stageMeasure_succ_ssubset_iff
#print axioms Qtsl.QuantumSpectrum.alignMeasure_interference_zero_two
#print axioms Qtsl.QuantumSpectrum.alignMeasure_pushforward_interference_cases
#print axioms Qtsl.QuantumSpectrum.alignMeasure_interferenceSpectrum_pushforward_ssubset
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interference_cases
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_pushforward_interference_zero_one
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interferenceSpectrum_pushforward_eq
#print axioms Qtsl.QuantumSpectrum.dephaseMeasure_interference_zero_two
#print axioms Qtsl.QuantumSpectrum.mergeCoarse_singleton_not_saturated

-- Essential surjectivity from a common implementer: the certified
-- W*-descent clause (QuantumStackImplementer)
#print axioms Qtsl.QuantumStack.mem_netUnion_of_member
#print axioms Qtsl.QuantumStack.implementer_mem_commutant_member
#print axioms Qtsl.QuantumStack.implementerDatum
#print axioms Qtsl.QuantumStack.implementer_mem_commutant
#print axioms Qtsl.QuantumStack.implementerSubRep
#print axioms Qtsl.QuantumStack.implementerComparisonIso
#print axioms Qtsl.QuantumStack.implementerDatum_in_essImage
#print axioms Qtsl.QuantumStack.descentComparisonW_essImage_of_commonImplementer
#print axioms Qtsl.QuantumStack.one_commutes
#print axioms Qtsl.QuantumStack.constWNet_implementerDatum_in_essImage

-- (BagLift) the polymorphic Bag-lift square (BagLift + fixture + the
-- multiplicity dictionary). Expected: std-three on every line.
#print axioms Qtsl.BagLift.pderiv_bind₁
#print axioms Qtsl.BagLift.pderiv_pderiv_bind₁
#print axioms Qtsl.BagLift.contOp_compile
#print axioms Qtsl.BagLift.gramOp_compile
#print axioms Qtsl.BagLift.ColorModel.models_square
#print axioms Qtsl.BagLift.atomic_flatGen_eq_genPoly
#print axioms Qtsl.BagLift.sum_survivors
#print axioms Qtsl.BagLift.ColorModel.bind₁_jumpKer_poolC
#print axioms Qtsl.BagLift.ColorModel.contOp_block
#print axioms Qtsl.BagLift.ColorModel.gramOp_block
#print axioms Qtsl.BagLift.ColorModel.lift_inner_coherence
#print axioms Qtsl.BagLift.ColorModel.kill_coherence
#print axioms Qtsl.BagLift.ColorModel.edge_coherence
#print axioms Qtsl.BagLift.ColorModel.bag_square
#print axioms Qtsl.BagLift.ColorModel.mu_compat_pool
#print axioms Qtsl.BagLift.sum_embeddings_factorial
#print axioms Qtsl.BagLift.sum_embeddings_two
#print axioms Qtsl.BagLift.Fixture.hdRep₁
#print axioms Qtsl.BagLift.Fixture.hGRep₁
#print axioms Qtsl.BagLift.Fixture.hdRep₂
#print axioms Qtsl.BagLift.Fixture.hGRep₂
#print axioms Qtsl.BagLift.Fixture.hdRepμ
#print axioms Qtsl.BagLift.Fixture.hGRepμ
#print axioms Qtsl.BagLift.Fixture.twoLevel_square
#print axioms Qtsl.BagLift.Fixture.muTower_square
#print axioms Qtsl.BagLift.Fixture.twoLevel_V
#print axioms Qtsl.BagLift.Fixture.twoLevel_W
#print axioms Qtsl.BagLift.Fixture.mu_coherence_cell

-- (QuantumApproxConsistency)
#print axioms Qtsl.QuantumApproxConsistency.decoherenceFunctional_eq_inner
#print axioms Qtsl.QuantumApproxConsistency.decoherenceFunctional_diag_re
#print axioms Qtsl.QuantumApproxConsistency.norm_decoherenceFunctional_le
#print axioms Qtsl.QuantumApproxConsistency.approxMediumDecoherent_zero_iff
#print axioms Qtsl.QuantumApproxConsistency.ApproxMediumDecoherent.mono
#print axioms Qtsl.QuantumRecords.MediumDecoherent.approxMediumDecoherent
#print axioms Qtsl.QuantumApproxConsistency.approxMediumDecoherent_of_one_le
#print axioms Qtsl.QuantumApproxConsistency.approxMediumDecoherentAbs_zero_iff
#print axioms Qtsl.QuantumApproxConsistency.ApproxMediumDecoherent.abs_of_diag_le_one

-- (QuantumApproxCap)
#print axioms Qtsl.QuantumApproxCap.diagonal_im_zero
#print axioms Qtsl.QuantumApproxCap.diagonal_re_eq_sum_normSq
#print axioms Qtsl.QuantumApproxCap.diagonal_re_pos_iff
#print axioms Qtsl.QuantumApproxCap.decoherenceFunctional_eq_sum
#print axioms Qtsl.QuantumApproxCap.conj_decoherenceFunctional_eq_sum
#print axioms Qtsl.QuantumApproxCap.gram_expansion
#print axioms Qtsl.QuantumApproxCap.welch_sq_of_nonnull
#print axioms Qtsl.QuantumApproxCap.welch_of_nonnull
#print axioms Qtsl.QuantumApproxCap.nonnull_card_welch
#print axioms Qtsl.QuantumApproxCap.donaldStratum_card_le
#print axioms Qtsl.QuantumApproxCap.qubit_floor
#print axioms Qtsl.QuantumApproxCap.mediumDecoherent_nonnull_card_le
#print axioms Qtsl.QuantumApproxCap.dkApproxConsistent_zero_iff
#print axioms Qtsl.QuantumApproxCap.DKConsistent.dkApproxConsistent
#print axioms Qtsl.QuantumApproxCap.dkApproxConsistent_nonnull_card_le
#print axioms Qtsl.QuantumApproxCap.dkApproxConsistent_qubit_floor

-- (QuantumApproxExactInstance)
#print axioms Qtsl.QuantumApproxExactInstance.pi_norm_pair
#print axioms Qtsl.QuantumApproxExactInstance.pz0_eq_diagonal
#print axioms Qtsl.QuantumApproxExactInstance.pz1_eq_diagonal
#print axioms Qtsl.QuantumApproxExactInstance.sqrt3_mul_self
#print axioms Qtsl.QuantumApproxExactInstance.sqrt3_sq
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_sum_eq_one
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_mulVec_zero
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_mulVec_one
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_D_off
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_D_off'
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_D_zero
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_D_one
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_approxMediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_approx_sharp
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_not_mediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.pointerFamily_mediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.symmetricLeakFamily_dist
#print axioms Qtsl.QuantumApproxExactInstance.approxToExact_instance_symmetricLeak
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_mulVec_zero
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_mulVec_one
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_mulVec_two
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_approxMediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_not_mediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_approx_sharp
#print axioms Qtsl.QuantumApproxExactInstance.trineExactWitness_mediumDecoherent
#print axioms Qtsl.QuantumApproxExactInstance.trineFamily_dist
#print axioms Qtsl.QuantumApproxExactInstance.approxToExact_instance_trine
#print axioms Qtsl.QuantumApproxExactInstance.approx_implies_exact_of_rank_one_final

#print axioms Qtsl.Guard.sound_QGuardIntro
#print axioms Qtsl.Guard.sound_QGuardElim
#print axioms Qtsl.Guard.qsatFromRegion_derived
#print axioms Qtsl.Guard.guardSat_singleton_iff
#print axioms Qtsl.Guard.GuardSat.mono_region
#print axioms Qtsl.Guard.GuardSat.mono_init
#print axioms Qtsl.Guard.GuardSat.mono_sat
#print axioms Qtsl.Guard.guardSat_of_disjoint
#print axioms Qtsl.Guard.GuardSat.toBlanket
#print axioms Qtsl.Guard.exists_blanket_not_guardSat
#print axioms Qtsl.Guard.exists_guardSat_not_unguarded
#print axioms Qtsl.Guard.exists_not_guardSat_wrong_region
#print axioms Qtsl.Guard.sound_QGuardIntro_sublevel
#print axioms Qtsl.Guard.guard_eval_sublevel
#print axioms Qtsl.Guard.sound_QGuardIntro_prob

#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.claimA
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.claimB
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.regret_le
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.regret_le_graded
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.regret_le_const
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.regret_le_graded_const
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.eps_zero_exact
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.regret_zero_terminal
#print axioms Qtsl.Imprecise.BellmanGap.bound_mono_bracket
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.fh_regret
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.fh_regret_sum
#print axioms Qtsl.Imprecise.BellmanGap.RobustMDP.fh_exact
#print axioms Qtsl.Imprecise.BellmanGapCrystal.once_drawn_rule_false
#print axioms Qtsl.Imprecise.BellmanGapCrystal.crystal_perfiring_verdict
#print axioms Qtsl.Imprecise.BellmanGapCrystal.greediness_load_bearing

/-! ## Penalty-kernel tier (`QtslAux.Imprecise.PenaltyEnvelope` and kin) -/

#print axioms Qtsl.Imprecise.FinPMF.exp_dirac
#print axioms Qtsl.Imprecise.FinPMF.exp_sub
#print axioms Qtsl.Imprecise.penUpperE_zero_cost
#print axioms Qtsl.Imprecise.penUpperE_unique
#print axioms Qtsl.Imprecise.penUpperE_eq_neg_penLowerE_neg
#print axioms Qtsl.Imprecise.penUpperE_add_const
#print axioms Qtsl.Imprecise.penUpperE_mix_le
#print axioms Qtsl.Imprecise.penUpperE_smul
#print axioms Qtsl.Imprecise.penUpperE_const
#print axioms Qtsl.Imprecise.exp_sub_exp_le_sup_sub
#print axioms Qtsl.Imprecise.penUpperE_dirac_family
#print axioms Qtsl.Imprecise.dirac_attains_sup_sub
#print axioms Qtsl.Imprecise.penUpperE_eq_sup_levelProfile
#print axioms Qtsl.Imprecise.Mutants.penUpperE_not_posHomogeneous
#print axioms Qtsl.Imprecise.penUpperE_compFam
#print axioms Qtsl.Imprecise.penLowerE_compFam
#print axioms Qtsl.Imprecise.penUpperE_compFam_zero_recovers_tower
#print axioms Qtsl.Imprecise.penUpperE_le_of_subfamily
#print axioms Qtsl.Imprecise.penUpperE_diag_le_compFam
#print axioms Qtsl.Imprecise.penUpperE_compFam_dirac_left
#print axioms Qtsl.Imprecise.penUpperE_compFam_dirac_right
#print axioms Qtsl.Imprecise.precise_compFam_penUpperE
#print axioms Qtsl.Imprecise.precise_compFam_upper_eq_lower
#print axioms Qtsl.Imprecise.dirac_compFam_penUpperE
#print axioms Qtsl.Imprecise.Mutants.mutant_unweighted_cost_breaks_square
#print axioms Qtsl.Imprecise.Mutants.mutant_sup_cost_breaks_square
#print axioms Qtsl.Imprecise.Mutants.diag_lt_perFiring
#print axioms Qtsl.Imprecise.sup'_const_add
#print axioms Qtsl.Imprecise.penUpperE_mixedFam
#print axioms Qtsl.Imprecise.sup_exp_le_exp_sup
#print axioms Qtsl.Imprecise.exchange_of_separated
#print axioms Qtsl.Imprecise.Mutants.exchange_strict
#print axioms Qtsl.Imprecise.PrevEq.lower
#print axioms Qtsl.Imprecise.wingRace_penUpperE
#print axioms Qtsl.Imprecise.wingForced_penUpperE
#print axioms Qtsl.Imprecise.wingDemonic_penUpperE
#print axioms Qtsl.Imprecise.wingDemonic_penLowerE
#print axioms Qtsl.Imprecise.wingCarvedGraded_penUpperE
#print axioms Qtsl.Imprecise.wingCarved_point_prevEq_forced
#print axioms Qtsl.Imprecise.wingCarved_full_prevEq_demonic
#print axioms Qtsl.Imprecise.le_hurwicz_of_chord
#print axioms Qtsl.Imprecise.hurwicz_ge_iff_exists_chord
#print axioms Qtsl.Imprecise.hurwiczSuperlevel_eq_iUnion_crescents
#print axioms Qtsl.Imprecise.finite_chords_strict

-- killed time-indexed reads: construction, dichotomy, factorization,
-- comparison lift, exponential pin (KilledTimeIndexed)
#print axioms Qtsl.KilledTimeIndexed.killedRead_add_accum
#print axioms Qtsl.KilledTimeIndexed.killedRead_univ_eq_one_iff
#print axioms Qtsl.KilledTimeIndexed.lintegral_timed_prefix
#print axioms Qtsl.KilledTimeIndexed.mapped_timed_prefix_eq
#print axioms Qtsl.KilledTimeIndexed.killedRead_eq_of_prefix_eq
#print axioms Qtsl.KilledTimeIndexed.accum_eq_of_prefix_eq
#print axioms Qtsl.KilledTimeIndexed.isMarkovKernel_expHold
