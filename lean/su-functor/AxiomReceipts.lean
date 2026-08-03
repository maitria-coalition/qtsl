import SuFunctor.Plain.Battery
import SuFunctor.Plain.Comparison
import SuFunctor.Plain.MeasJoint
import SuFunctor.Plain.GeneralFunctor
import SuFunctor.Plain.GeneralSeam
import SuFunctor.Plain.SeamDensity
import SuFunctor.Plain.SeamDensityCore
import SuFunctor.Site.GeneralWindow
import SuFunctor.Site.ClassDescent
import SuFunctor.Site.TemporalTypeTheory
import SuFunctor.Site.WavyCoverage
import SuFunctor.Site.BehaviorSpec
import SuFunctor.Site.Battery
import SuFunctor.Site.MatchingFork
import SuFunctor.SingleSiteSemanticUniverse
import SuFunctor.WiringModes
import SuFunctor.Universe.StochasticWitnesses
import SuFunctor.Universe.CertificateLayer
import SuFunctor.SpatialPlates.WaveAction
import SuFunctor.Universe.General.EnvelopeIdentification
import SuFunctor.Universe.General.EnvelopeWitness
import SuFunctor.Universe.EpistemicStates

/-!
# Axiom receipts, spec-class tier

`#print axioms` receipts for the plain spec-class decoration tier: the
functor, its total under the plain double Grothendieck construction, the
projection facts, the element-level coherence cores, and the acceptance
battery (positive twins and refuted mutants), so the axiom footprint is
inspectable at build time.
-/

open CategoryTheory SuFunctor.Plain

universe u

/-- Witness: the plain total of the spec-class functor is a pseudo double
category, by instance search. -/
theorem specTotalLawfulWitness :
    CategoryTheory.PseudoDoubleCategory (SpecTotal PUnit.{u + 1}) :=
  inferInstance

#print axioms SuFunctor.Plain.specFunctor
#print axioms SuFunctor.Plain.specTotal_pseudoDoubleCategory
#print axioms SuFunctor.Plain.specProj_isPseudo
#print axioms SuFunctor.Plain.specProj_discreteOpfibration
#print axioms SuFunctor.Plain.pull_tot_hComp_boxplus
#print axioms SuFunctor.Plain.pull_tot_lAssoc_boxplus
#print axioms SuFunctor.Plain.pull_tot_lLeftUnitor_boxplus
#print axioms SuFunctor.Plain.pull_tot_lRightUnitor_boxplus
#print axioms SuFunctor.Plain.cast_apply_const
#print axioms SuFunctor.Plain.unitClass_transparent
#print axioms SuFunctor.Plain.singleton_boxplus
#print axioms SuFunctor.Plain.transport_singleton
#print axioms SuFunctor.Plain.idealPoint_le_iff
#print axioms SuFunctor.Plain.mem_boxplusClass_iff
#print axioms SuFunctor.Plain.boxplusClass_mono
#print axioms SuFunctor.Plain.mapCellClass_mono
#print axioms SuFunctor.Plain.taxedBoxplus_breaks_unit_transparency
#print axioms SuFunctor.Plain.funnelComp_breaks_unit_coherence
#print axioms specTotalLawfulWitness

/-!
# Axiom receipts, site-indexed tier

The sheaf upgrade of the spec-class tier: the site-indexed functor over
the unchanged wiring base, its plain total, the projection facts, the
window coherence cores and site-direction exchanges, the class-descent
stratum (the landed descent homeomorphism consumed at the class level),
and the acceptance battery with the matching-fork mutant.
-/

open SuFunctor.Site

/-- Witness: the total of the site-indexed spec functor is a pseudo
double category, by instance search. -/
theorem siteSpecTotalLawfulWitness :
    CategoryTheory.PseudoDoubleCategory
      (SiteSpecTotal (fun _ : PUnit.{u + 1} => (Set.univ : Set PUnit.{u + 1}))
        PUnit.{u + 1}) :=
  inferInstance

#print axioms SuFunctor.Site.siteSpecFunctor
#print axioms SuFunctor.Site.siteSpecTotal_pseudoDoubleCategory
#print axioms SuFunctor.Site.siteSpecProj_isPseudo
#print axioms SuFunctor.Site.siteSpecProj_discreteOpfibration
#print axioms siteSpecTotalLawfulWitness
#print axioms SuFunctor.Site.pullW_tot_hComp_boxplusW
#print axioms SuFunctor.Site.pullW_tot_lAssoc_boxplusW
#print axioms SuFunctor.Site.pullW_tot_lLeftUnitor_boxplusW
#print axioms SuFunctor.Site.pullW_tot_lRightUnitor_boxplusW
#print axioms SuFunctor.Site.penExt_refl
#print axioms SuFunctor.Site.penExt_penExt
#print axioms SuFunctor.Site.penExt_pull_trajMap
#print axioms SuFunctor.Site.penExt_boxplusW
#print axioms SuFunctor.Site.penExt_unitPenW
#print axioms SuFunctor.Site.IsMatching.isPersistent
#print axioms SuFunctor.Site.IsPersistent.image_pull_trajMap
#print axioms SuFunctor.Site.IsPersistent.image2_boxplusW
#print axioms SuFunctor.Site.isPersistent_unitPenW
#print axioms SuFunctor.Site.mem_wComp_iff
#print axioms SuFunctor.Site.wComp_nonempty
#print axioms SuFunctor.Site.wUnit_transparent
#print axioms SuFunctor.Site.singleton_boxplusW
#print axioms SuFunctor.Site.transport_singletonW
#print axioms SuFunctor.Site.wIdealPoint_le_iff
#print axioms SuFunctor.Site.wComp_mono
#print axioms SuFunctor.Site.wCellMap_mono
#print axioms SuFunctor.Site.taxedBoxplusW_breaks_unit_transparency
#print axioms SuFunctor.Site.funnelCompW_breaks_unit_coherence
#print axioms SuFunctor.Site.isOpenMap_inclusion
#print axioms SuFunctor.Site.continuous_preimage_inclusion
#print axioms SuFunctor.Site.continuous_clipLE
#print axioms SuFunctor.Site.clip_mem_classExt_iff
#print axioms SuFunctor.Site.IsLocallyClosed.classExt
#print axioms SuFunctor.Site.IsConstructibleUnion.classExt
#print axioms SuFunctor.Site.isLocallyClosed_image_homeomorph
#print axioms SuFunctor.Site.isConstructibleUnion_image_homeomorph
#print axioms SuFunctor.Site.classDescent
#print axioms SuFunctor.Site.isConstructibleUnion_classDescent_iff
#print axioms SuFunctor.Site.bijective_toProjLim
#print axioms SuFunctor.Site.push_apply_ne_zero
#print axioms SuFunctor.Site.MatchingFork.penExt_qFalse
#print axioms SuFunctor.Site.MatchingFork.not_penExt_wallPM
#print axioms SuFunctor.Site.MatchingFork.not_penExt_wallQN
#print axioms SuFunctor.Site.MatchingFork.isMatching_famM
#print axioms SuFunctor.Site.MatchingFork.isMatching_famN
#print axioms SuFunctor.Site.MatchingFork.matching_not_closed_under_compositor


/-- Witness: the semantic universe is a pseudo double category, by
instance search. -/
theorem singleSiteSemanticUniverseLawfulWitness :
    CategoryTheory.PseudoDoubleCategory (SuFunctor.SingleSiteSemanticUniverse PUnit.{u + 1}) :=
  inferInstance

#print axioms SuFunctor.dnfSpecFunctor
#print axioms SuFunctor.singleSiteSemanticUniverse_pseudoDoubleCategory
#print axioms SuFunctor.singleSiteUniverseProj_isPseudo
#print axioms SuFunctor.singleSiteUniverseProj_discreteOpfibration
#print axioms SuFunctor.atomPull_tot_hComp_boxplus
#print axioms SuFunctor.atomPull_tot_lAssoc_boxplus
#print axioms SuFunctor.atomPull_tot_lLeftUnitor_boxplus
#print axioms SuFunctor.atomPull_tot_lRightUnitor_boxplus
#print axioms SuFunctor.atomPull_tot_hId_unitAtom
#print axioms SuFunctor.Plain.Joint.push_surjective
#print axioms SuFunctor.specMap_modelClass_eq
#print axioms SuFunctor.specMap_modelClass_subset
#print axioms SuFunctor.cellMap_modelClass_eq
#print axioms SuFunctor.cellMap_modelClass_subset
#print axioms SuFunctor.Universe.SpecDnf.isConstructibleUnion_probRead

/-!
# Axiom receipts, stochastic witnesses

The point-native exhibits of the probability stratum: mass as the
narrowly continuous coordinate, the escape witness (σ-additivity
refusal), the event-evaluation fixture (portmanteau polarity is sharp),
and the noncompactness of the carrier over `ℕ`.
-/

#print axioms SuFunctor.Universe.tendsto_mass
#print axioms SuFunctor.Universe.mass_of_tendsto
#print axioms SuFunctor.Universe.not_tendsto_diracProb_atTop
#print axioms SuFunctor.Universe.not_exists_tendsto_diracProb
#print axioms SuFunctor.Universe.tendsto_diracProb_one_div_add_one
#print axioms SuFunctor.Universe.not_tendsto_diracProb_apply_singleton
#print axioms SuFunctor.Universe.not_isClosed_setOf_apply_singleton_le
#print axioms SuFunctor.Universe.not_compactSpace_probabilityMeasure_nat

#print axioms SuFunctor.dnfPull_mono
#print axioms SuFunctor.dnfBoxplus_mono
#print axioms SuFunctor.boxplus_mem_modelClass_dnfBoxplus

/-! ## The temporal-type-theory inclusion (site + spec legs) -/

#print axioms SuFunctor.Site.TTT.anchorQuot
#print axioms SuFunctor.Site.TTT.existsUnique_lift_up
#print axioms SuFunctor.Site.TTT.existsUnique_lift_down
#print axioms SuFunctor.Site.TTT.wavy_iff_strictlyInterior
#print axioms SuFunctor.Site.TTT.anchorTrajIso
#print axioms SuFunctor.Site.satAt_specOfBehavior_iff
#print axioms SuFunctor.Site.wSpecMap_specOfBehavior
#print axioms SuFunctor.Site.boxplusW_indPen
#print axioms SuFunctor.Site.satAt_wComp_iff_glue

/-!
# Axiom receipts, general stratum of the composition tier

The subprobability-measure stratum: the joint calculus (pushforward
functorial along measurable maps, weakly continuous along continuous
ones), the base-free coherence cores, the lower-semicontinuity closure
calculus with compact attainment, the tight-tier decoration functor
over measurable carriers, the transposed acceptance battery with its
refutation pins, and the seam exhibiting the finite stratum as a
sub-instance of the general one.
-/

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
#print axioms SuFunctor.Plain.munitClass_transparent
#print axioms SuFunctor.Plain.taxedMboxplus_breaks_unit_transparency
#print axioms SuFunctor.Plain.funnelMComp_breaks_unit_coherence
#print axioms SuFunctor.Plain.Joint.toMeas_mass
#print axioms SuFunctor.Plain.Joint.toMeas_injective
#print axioms SuFunctor.Plain.Joint.toMeas_push
#print axioms SuFunctor.Plain.Joint.pull_toMeas
#print axioms SuFunctor.Plain.Joint.image_pull_toMeas

/-! ## The wavy coverage (topology stratum of the site leg) -/

#print axioms SuFunctor.Site.TTT.wavyCoverage_toGrothendieck
#print axioms SuFunctor.Site.TTT.wavyTopology_zero
#print axioms SuFunctor.Site.TTT.bot_mem_of_le_wavy
#print axioms SuFunctor.Site.TTT.compatiblePreserving_anchorQuot
#print axioms SuFunctor.Site.TTT.isContinuous_anchorQuot
#print axioms SuFunctor.Site.TTT.mem_interiorTopology_iff
#print axioms SuFunctor.Site.TTT.isSheaf_zero_unique

/-! ## Density completion across the seam, and the general window assembly -/

#print axioms SuFunctor.Plain.Joint.lintegral_toMeas
#print axioms SuFunctor.Plain.isClosed_le_of_lsc_usc
#print axioms SuFunctor.Plain.MeasPen.le_of_seam_le
#print axioms SuFunctor.Plain.MeasPen.eq_of_seam_eq
#print axioms SuFunctor.Plain.MeasPen.iSup_seam_eq
#print axioms SuFunctor.Plain.Joint.dense_ratSeam
#print axioms SuFunctor.Plain.Joint.toMeas_surjective
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas_nat
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas
#print axioms SuFunctor.Plain.Joint.denseRange_toMeas_of_pseudoMetrizable
#print axioms SuFunctor.Plain.not_seam_ge_transport
#print axioms SuFunctor.Plain.iInf_seam_ne_iInf
#print axioms SuFunctor.Plain.dense_seam_inf_gap
#print axioms SuFunctor.Site.penExtM_penExtM
#print axioms SuFunctor.Site.penExtM_pull_trajMap
#print axioms SuFunctor.Site.penExtM_mboxplusW
#print axioms SuFunctor.Site.IsPersistentM.image2_mboxplusW
#print axioms SuFunctor.Site.penExtM_comp_toMeas
#print axioms SuFunctor.Site.IsPersistentM.seamRestrict

/-! ## Spatial plates: the wave-equation fixture (stationary action) -/

#print axioms SuFunctor.SpatialPlates.totalDerivT_mul
#print axioms SuFunctor.SpatialPlates.totalDerivX_mul
#print axioms SuFunctor.SpatialPlates.noether_time_translation
#print axioms SuFunctor.SpatialPlates.wave_euler_lagrange
#print axioms SuFunctor.SpatialPlates.energy_density_as_charge
#print axioms SuFunctor.SpatialPlates.flux_as_current
#print axioms SuFunctor.SpatialPlates.wave_energy_flux_row
#print axioms SuFunctor.SpatialPlates.wave_power_balance_torus
#print axioms SuFunctor.SpatialPlates.torus_wall_load_bearing

/-! ## The countably additive envelope theorem (general stratum) -/

#print axioms SuFunctor.Universe.General.IsCoherentLP.exists_dominatesLP_eq
#print axioms SuFunctor.Universe.General.DominatesLP.sigmaSmoothAtZero
#print axioms SuFunctor.Universe.General.IsCoherentLP.sigmaSmoothAtZero_conjUpper_of_compact
#print axioms SuFunctor.Universe.General.exists_probabilityMeasure_of_sigmaSmooth
#print axioms SuFunctor.Universe.General.DominatesLP.exists_probabilityMeasure
#print axioms SuFunctor.Universe.General.IsCoherentLP.exists_mem_caCredal_integral_eq
#print axioms SuFunctor.Universe.General.IsCoherentLP.isLeast_caCredal_image
#print axioms SuFunctor.Universe.General.IsCoherentLP.isLeast_caCredal_image_of_compactSpace
#print axioms SuFunctor.Universe.General.isCoherentLP_lowerEnv
#print axioms SuFunctor.Universe.General.sigmaSmoothAtZero_conjUpper_lowerEnv_of_tight
#print axioms SuFunctor.Universe.General.EnvelopeWitness.caCredal_liminfLP_eq_empty
#print axioms SuFunctor.Universe.General.EnvelopeWitness.not_forall_coherent_caCredal_nonempty
#print axioms SuFunctor.Universe.General.EnvelopeWitness.vacuousLP_not_attained

/-! ## Wiring modes (the transport trio's naturality statements) -/

#print axioms SuFunctor.WiringModes.WireRows.ofList_perm
#print axioms SuFunctor.WiringModes.WireRows.ofList_pair_left
#print axioms SuFunctor.WiringModes.WireRows.swapEquiv
#print axioms SuFunctor.WiringModes.WireRows.swapTot
#print axioms SuFunctor.WiringModes.WireRows.cellOf_vId
#print axioms SuFunctor.WiringModes.WireRows.cellOf_vComp
#print axioms SuFunctor.WiringModes.SetRows.pat_eq_share
#print axioms SuFunctor.WiringModes.pull_tot_hComp_image2_boxplus
#print axioms SuFunctor.WiringModes.dnfPull_tot_hComp_dnfBoxplus
#print axioms SuFunctor.WiringModes.share_transport_boxplus
#print axioms SuFunctor.WiringModes.set_transport_boxplus
#print axioms SuFunctor.WiringModes.pairDec
#print axioms SuFunctor.WiringModes.compDec
#print axioms SuFunctor.WiringModes.shareBoxplus
#print axioms SuFunctor.WiringModes.boxplus_mono
#print axioms SuFunctor.WiringModes.boxplus_add_const
#print axioms SuFunctor.WiringModes.boxplus_le_slack
#print axioms SuFunctor.WiringModes.atomBoxplus_floor_le_slack
#print axioms SuFunctor.WiringModes.switchIncl_factor
#print axioms SuFunctor.WiringModes.switchMap_id
#print axioms SuFunctor.WiringModes.switchMap_comp
#print axioms SuFunctor.WiringModes.switchIncl_natural
#print axioms SuFunctor.WiringModes.dnfPull_switch_natural

/-! Epistemic-states tier (the Semantic Universe chapter's
conditional/independence-beliefs example, finite stratum): the joint
convexity + joint lower semicontinuity engines, the three zero-set
characterizations, and the exact witnesses. -/

#print axioms SuFunctor.Universe.EpistemicStates.two_point_log_sum
#print axioms SuFunctor.Universe.EpistemicStates.klq_mix_mix_le
#print axioms SuFunctor.Universe.EpistemicStates.klq_eq_iSup_klBelow
#print axioms SuFunctor.Universe.EpistemicStates.lowerSemicontinuous_klq_pair
#print axioms SuFunctor.Universe.EpistemicStates.mutualInfoQ_eq_zero_iff
#print axioms SuFunctor.Universe.EpistemicStates.continuous_mutualInfoQ
#print axioms SuFunctor.Universe.EpistemicStates.indepPenalty_eq_zero_iff
#print axioms SuFunctor.Universe.EpistemicStates.condTarget_mix
#print axioms SuFunctor.Universe.EpistemicStates.klq_condTarget_eq_zero_iff
#print axioms SuFunctor.Universe.EpistemicStates.penaltyConvex_condPenalty
#print axioms SuFunctor.Universe.EpistemicStates.lowerSemicontinuous_condPenalty
#print axioms SuFunctor.Universe.EpistemicStates.marginalSum_eq_zero_iff
#print axioms SuFunctor.Universe.EpistemicStates.compile_marginalWallSum
#print axioms SuFunctor.Universe.EpistemicStates.Witness.chi_not_isProductLaw
#print axioms SuFunctor.Universe.EpistemicStates.Witness.not_penaltyConvex_indepPenalty
#print axioms SuFunctor.Universe.EpistemicStates.Witness.frechet_does_not_imply_independence
#print axioms SuFunctor.Universe.EpistemicStates.indepBody_credalBody_not_convex
