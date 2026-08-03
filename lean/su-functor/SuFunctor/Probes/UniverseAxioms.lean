import SuFunctor.Universe.SpecDnf
import SuFunctor.Universe.ReachAvoid
import SuFunctor.Universe.CertificateLayer
import SuFunctor.Universe.CoupledJudgment
import SuFunctor.Universe.Fragments
import SuFunctor.Universe.Generation
import SuFunctor.Universe.VietorisDictionary
import SuFunctor.Universe.VietorisStratum
import SuFunctor.Universe.ImageChar
import SuFunctor.Universe.IdealPoint
import SuFunctor.Universe.Sector
import SuFunctor.Universe.Hypograph
import SuFunctor.Universe.TransposedGeneration
import SuFunctor.Universe.AtomMirrors
import SuFunctor.Universe.RadialGeneration
import SuFunctor.Universe.Points
import SuFunctor.Universe.RecordLens
import SuFunctor.Universe.RecordLensContinuum
import SuFunctor.Universe.FellTopology
import SuFunctor.Universe.FellRestrict
import SuFunctor.Universe.FellSeamWitness
import SuFunctor.Universe.FellDescent
import SuFunctor.Universe.FellDescentEqualizer
import SuFunctor.Universe.FellCapacity
import SuFunctor.Universe.FellRecordLocus
import SuFunctor.Universe.FellRecordWitness
import SuFunctor.Universe.RecordLensFell
import SuFunctor.Universe.Riesz
import SuFunctor.Universe.LocallyClosedLayer
import SuFunctor.Universe.NablaDictionary
import SuFunctor.Universe.DisjunctionElim
import SuFunctor.Universe.TransportCitizenship
import SuFunctor.Universe.TopologicalCitizenship
import SuFunctor.Universe.TotalCitizenship
import SuFunctor.Universe.ValuationUnit
import SuFunctor.Universe.DemonicClock
import SuFunctor.Universe.MeshCompositor
import SuFunctor.Universe.SpacelikeSeam
import SuFunctor.Universe.StochasticWitnesses
import SuFunctor.Universe.PairSequent
import SuFunctor.Plain.Seam

/-! # Axiom audit for the flat-carrier universe modules

Prints the axiom footprint of the headline theorems of the flat
carrier, the coupled judgment, the generation theorem, the radial
compile dictionary, its topological stratum, the definability
refutations, and the Riesz presentation.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe

#print axioms lowerSemicontinuous_probWall_iff
#print axioms not_coupledSat_top_system
#print axioms coupledSat_zero_topSpec_iff
#print axioms not_coupledSat_of_zero_mem
#print axioms exists_coupledSat_iff_con
#print axioms exists_refinement_destroys_liveness
#print axioms dip_sup_iff
#print axioms coupledSat_and_iff
#print axioms no_safety_disjunction
#print axioms no_safety_disjunction_coordinates
#print axioms no_liveness_conjunction
#print axioms coupled_refinement_iff
#print axioms diamond_splitting
#print axioms matching_not_necessary
#print axioms dip_probWall_compl_iff
#print axioms coupledSat_affRow_iff
#print axioms boxRow_eq_inf
#print axioms iSup_boxRows_eq_self
#print axioms grade_add
#print axioms compile_subset_compile_iff
#print axioms dip_iff_compile_escape
#print axioms coupledSat_iff_compile
#print axioms compile_inf
#print axioms compile_sup
#print axioms mem_compile_add_iff
#print axioms rieszEquiv
#print axioms pairing_dirac
#print axioms pairing_injective
#print axioms isClosed_compile_iff
#print axioms toBel_mem_compile_iff
#print axioms isClosed_setOf_isRadial
#print axioms isCompact_setOf_isRadial
#print axioms compileNC_mem_crescentClass_iff
#print axioms isLocallyClosed_crescentClass
#print axioms escape_face_sup
#print axioms lowerSemicontinuous_supAtom
#print axioms lowerSemicontinuous_infAtom
#print axioms compile_rayPenalty
#print axioms exists_lsc_compile_eq_iff
#print axioms compile_injective
#print axioms rayPenalty_compile
#print axioms upperSemicontinuous_rayGauge
#print axioms eq_compile_of_subset_of_escapes
#print axioms notMem_compile_scaledIndicator_iff
#print axioms exists_sector_of_hit
#print axioms generateFrom_sectorHit_eq_openHit
#print axioms isClosed_hypoSet
#print axioms map_polarLift
#print axioms polarLift_map
#print axioms hypoHomeo
#print axioms infAtom_indicator
#print axioms supAtom_indicator
#print axioms hyperRow_index_countable
#print axioms iSup_hyperRows_eq_self
#print axioms infAtom_lt_iff
#print axioms supAtom_lt_iff
#print axioms upperSemicontinuous_supAtom
#print axioms upperSemicontinuous_infAtom
#print axioms continuous_supAtom
#print axioms continuous_infAtom
#print axioms lowerSemicontinuous_extendTop
#print axioms iSup_hyperRows_restrict_eq_self
#print axioms iSup_hyperRows_radial_eq_self
#print axioms exists_ne_model_of_proper
#print axioms singletons_not_definable
#print axioms upper_open_not_definable
#print axioms isClosed_recordCon
#print axioms isCompact_recordCon
#print axioms support_uniformLift_iff
#print axioms lowerSemicontinuous_touchWall
#print axioms lowerSemicontinuous_dwellWall
#print axioms touch_dwell_separation
#print axioms lowerSemicontinuous_probabilityMeasure_apply
#print axioms mem_narrowCon_iff_forall_isOpen
#print axioms isClosed_narrowCon
#print axioms isCompact_narrowCon
#print axioms lowerSemicontinuous_touchWallNarrow
#print axioms lowerSemicontinuous_dwellWallNarrow
#print axioms touch_dwell_separation_narrow
#print axioms no_rectangle_coupling
#print axioms no_rectangle_coupling_lsc
#print axioms atMostOneRealizable_eq_iInter
#print axioms isClosed_atMostOneRealizable
#print axioms atMostOneRealizable_not_definable
#print axioms atMostOneRealizable_not_definable_lsc
#print axioms coupled_union_refinement_iff
#print axioms dip_sup_floor_iff
#print axioms coupledSat_image_sup_floor_iff
#print axioms exists_naive_cover_incomplete
#print axioms exists_essential_floor_raise
#print axioms IsLocallyClosed.isConstructibleUnion
#print axioms IsConstructibleUnion.union
#print axioms isConstructibleUnion_dnfClass
#print axioms compileNC_mem_dnfClass_iff
#print axioms crescentClass_inter_crescentClass
#print axioms crescentClass_dipTheory_inter_radial
#print axioms compileNC_top_notMem_crescentClass
#print axioms fell.isCompact_setOf_isClosed
#print axioms fell.continuous_restrictOpen
#print axioms fell.preimage_image_hit
#print axioms fell.preimage_image_miss
#print axioms fell.continuous_image_of_isProperMap
#print axioms fell.tendsto_jumpRecord
#print axioms fell.not_continuous_restrictOpen_seamBand
#print axioms fell.tendsto_singleton_natCast_bot
#print axioms fell.not_continuous_image_const
#print axioms vietoris_le_fell
#print axioms fell_eq_vietoris
#print axioms FellCloseds.compactSpace
#print axioms FellCloseds.t2Space
#print axioms FellCloseds.isOpen_disjoint_of_isCompact
#print axioms FellCloseds.isClosed_subsets_of_isClosed
#print axioms FellCloseds.isClosed_singleton_bot
#print axioms FellCloseds.isOpen_singleton_bot_iff_compactSpace
#print axioms mem_fellCon_iff_forall_isOpen
#print axioms bot_notMem_fellCon
#print axioms isClosed_fellCon
#print axioms isCompact_fellCon_inter
#print axioms lowerSemicontinuous_touchWallFell
#print axioms lowerSemicontinuous_dwellWallFell
#print axioms touch_dwell_separation_fell
#print axioms mem_nablaClass_iff
#print axioms nablaClass_of_isEmpty
#print axioms boxClass_eq_nablaClass
#print axioms diaClass_eq_nablaClass
#print axioms crescentClass_eq_box_inter_dia
#print axioms crescentClass_eq_nablaClass
#print axioms dnfClass_eq_iUnion_nablaClass
#print axioms exists_nabla_presentation_of_finite
#print axioms dirac_notMem_compile_top
#print axioms bare_escape_dictionary_false
#print axioms containerless_dictionary_false
#print axioms fell.map_dirac_restrictOpen
#print axioms FellCloseds.projLimHomeomorph
#print axioms FellCloseds.isHomeomorph_toProjLim_of_directed
#print axioms FellCloseds.not_surjective_toProjLim_nondirectedPair
#print axioms FellCloseds.not_isOpen_iInf_induced_singleton_bot
#print axioms FellCloseds.not_iInf_induced_le_vietoris
#print axioms FellCloseds.equalizerHomeomorph
#print axioms FellCloseds.isHomeomorph_toEqualizer
#print axioms FellCloseds.not_isOverlapCompat_nondirectedFamily
#print axioms FellCloseds.preimage_glueSet_nondirectedFamily_ne
#print axioms FellCloseds.isHomeomorph_toEqualizer_nondirectedPair
#print axioms emLift_id
#print axioms emLift_comp
#print axioms emLift_relImage
#print axioms relImage_comp
#print axioms exists_no_functional_transport
#print axioms exists_emLift_inf_not
#print axioms selSup_sup_left
#print axioms coupledSat_sup_wall_iff
#print axioms cross_site_union_refinement_iff
#print axioms lowerSemicontinuous_selSup
#print axioms cross_site_union_refinement_iff_lsc
#print axioms crescentClass_inter_wall
#print axioms cross_site_union_refinement_iff_probWall
-- spacelike seam (SpacelikeSeam): the carrier-generic wall's
-- citizenship iff, the canonical closed trace relation, the
-- one-more-conjunct reading, the instantiated criterion at the
-- two-cell joint carrier, and the open-half-space refusal witness
#print axioms lowerSemicontinuous_seamWall_iff
#print axioms isClosed_traceAgree
#print axioms coupledSat_sup_seamWall_iff
#print axioms spacelike_seam_union_refinement_iff
#print axioms spacelike_seam_trace_union_refinement_iff
#print axioms not_lowerSemicontinuous_seamWall_halfSpace
#print axioms lowerSemicontinuous_seamWall_diagonal
-- capacity presentation (FellCapacity): the ∇-generator basis, second
-- countability, Borel-law and Scott-continuous determination, and the
-- two boundary theorems (miss-face compactness; hit-face insufficiency)
#print axioms FellCloseds.nablaGen_inter_nablaGen
#print axioms FellCloseds.nablaGen_anti
#print axioms FellCloseds.isOpen_nablaGen
#print axioms FellCloseds.isTopologicalBasis_nablaGen
#print axioms FellCloseds.secondCountableTopology_of_basis
#print axioms FellCloseds.exists_countable_basis_isCompact_closure
#print axioms FellCloseds.instSecondCountableTopology
#print axioms FellCloseds.measure_ext_of_nablaGen
#print axioms FellCloseds.exists_nablaGen_measure_ne
#print axioms FellCloseds.scottContinuous_ext_of_nablaGen
#print axioms FellCloseds.not_isOpen_disjoint_univ
#print axioms FellCloseds.exists_scottContinuous_eq_on_lower_ne
#print axioms FellCloseds.IsLocalLocus.isClosed
#print axioms FellCloseds.IsLocalLocus.isCompact
#print axioms FellCloseds.IsLocalLocus.glue_mem
#print axioms FellCloseds.IsLocalLocus.homeomorph
#print axioms FellCloseds.isClosed_levelLocus
#print axioms isClosed_speedLocus
#print axioms isCompact_speedLocus
#print axioms isLocallyClosed_speedLocus
#print axioms bot_mem_speedLocus
#print axioms isSpeedGraph_iff_forall_clip
#print axioms speedLocus_isLocalLocus
#print axioms glue_mem_speedLocus
#print axioms speedLocusHomeomorph
#print axioms isClosed_image_fst_of_isSpeedGraph
#print axioms isSpeedGraph_iff_exists_lipschitzOnWith
#print axioms tendsto_steepGraphF
#print axioms not_isClosed_graphLocus
#print axioms not_isClosed_iUnion_speedLocus
#print axioms not_isLocalLocus_nondirected
#print axioms not_isSpeedGraph_glueSet_nondirected

-- the seam (Plain.Seam): the identification of the exact and semantic
-- subprobability stocks over a finite carrier, its mass correspondence
-- and flat-stratum restriction, penalty transport as an order
-- isomorphism, and the judgment bridge
#print axioms SuFunctor.Plain.jointEquivBel
#print axioms SuFunctor.Plain.jointEquivBel_mass
#print axioms SuFunctor.Plain.jointEquivBel_zero
#print axioms SuFunctor.Plain.jointEquivProb
#print axioms SuFunctor.Plain.coe_jointEquivProb
#print axioms SuFunctor.Plain.toBel_jointEquivProb
#print axioms SuFunctor.Plain.penEquiv
#print axioms SuFunctor.Plain.singleton_subset_iff_penEquiv_mem

/-! Disjunction elimination over the class fibres: the forcing
theorems, the constructible-stratum validation, the body-reading
separation, and the locally-closed availability witness. -/

#print axioms ctxOrE_of_subset_union
#print axioms subset_union_of_ctxOrE
#print axioms ctxOrE_valid_iff
#print axioms orI_ctxOrE_valid_iff
#print axioms exists_ctxOrE_countermodel_of_ssubset
#print axioms dnfClass_append
#print axioms mem_dnfClass_append_iff
#print axioms dnfClass_subset_append_left
#print axioms dnfClass_subset_append_right
#print axioms inter_dnfClass_append
#print axioms ctxOrE_dnfClass
#print axioms isConstructibleUnion_dnfClass_append
#print axioms exists_mem_boxClass_pair_not_mem_union
#print axioms boxClass_mono
#print axioms boxClass_union_ssubset
#print axioms exists_ctxOrE_countermodel_body_reading
#print axioms dirac_true_ne_dirac_false
#print axioms exists_ctxOrE_countermodel_body_reading_carrier
#print axioms compile_zero
#print axioms continuous_singletonNC
#print axioms tendsto_mkBel_of_tendsto
#print axioms exists_union_crescentClass_not_isLocallyClosed

-- transport citizenship
#print axioms compile_pullPen
#print axioms lowerSemicontinuous_pullPen
#print axioms transportClass_union
#print axioms transportClass_iUnion
#print axioms transportClass_singleton_compileNC
#print axioms transport_safety_face
#print axioms transport_escape_iff
#print axioms saturated_preimage
#print axioms BelState.push_surjective
#print axioms ProbState.push_surjective
#print axioms coupledSat_pullPen_iff
#print axioms transportClass_crescentClass
#print axioms exists_transport_not_subset_pulled_crescent
#print axioms compile_add_radProd
#print axioms lowerSemicontinuous_add_penalty
#print axioms lowerSemicontinuous_boxplus
#print axioms compositorClass_union_left
#print axioms compositorClass_union_right
#print axioms compositor_singleton
#print axioms isConstructibleUnion_singleton

/-! Coupled DNF presentations: atom and DNF transport, the model-class
structure theorem with its two seam witnesses, the compositor's
separated faces, and constructibility of presented classes. -/

#print axioms SuFunctor.Universe.SpecAtom.comap_comp
#print axioms SuFunctor.Universe.SpecAtom.not_coupledSat_top
#print axioms SuFunctor.Universe.SpecDnf.comap_comp
#print axioms SuFunctor.Universe.SpecDnf.modelClass_mono
#print axioms SuFunctor.Universe.SpecDnf.top_notMem_modelClass
#print axioms SuFunctor.Universe.dip_comap_iff
#print axioms SuFunctor.Universe.coupledSat_comap_iff
#print axioms SuFunctor.Universe.image_comap_modelClass
#print axioms SuFunctor.Universe.SpecAtom.image_comap_modelClass
#print axioms SuFunctor.Universe.SpecDnf.image_comap_modelClass
#print axioms SuFunctor.Universe.SpecAtom.image_modelClass_subset
#print axioms SuFunctor.Universe.SpecDnf.image_modelClass_subset
#print axioms SuFunctor.Universe.exists_image_modelClass_not_subset
#print axioms SuFunctor.Universe.exists_modelClass_comap_not_subset_image
#print axioms SuFunctor.Universe.add_comp_safety_le
#print axioms SuFunctor.Universe.exists_coupledSat_add_fails
#print axioms SuFunctor.Universe.compile_pullPen_add_pullPen
#print axioms SuFunctor.Universe.isConstructibleUnion_empty
#print axioms SuFunctor.Universe.isConstructibleUnion_biUnion_finset
#print axioms SuFunctor.Universe.SpecDnf.isConstructibleUnion_crescentClass
#print axioms SuFunctor.Universe.SpecDnf.compileNC_mem_crescentClass_iff

/-! Graded reach-avoid (ReachAvoid): the singleton-liveness atoms
generate the constructible stratum — conjunctive decomposition with
the disjunctive reading refuted, exact connectives at both strata,
the characterization theorems, constructibility of the generated
algebra, and the strict generalization of crisp reach-avoid. -/

#print axioms SuFunctor.Universe.mem_modelClass_reachAvoid_iff
#print axioms SuFunctor.Universe.modelClass_eq_iInter_reachAvoid
#print axioms SuFunctor.Universe.exists_modelClass_ne_iUnion_reachAvoid
#print axioms SuFunctor.Universe.SpecAtom.modelClass_merge
#print axioms SuFunctor.Universe.SpecDnf.modelClass_disj
#print axioms SuFunctor.Universe.SpecDnf.modelClass_conj
#print axioms SuFunctor.Universe.genClosure_reachAvoid_iff_exists_specDnf
#print axioms SuFunctor.Universe.crescentClass_eq_iInter_reachAvoid
#print axioms SuFunctor.Universe.SpecDnf.crescentClass_disj
#print axioms SuFunctor.Universe.SpecDnf.crescentClass_conj
#print axioms SuFunctor.Universe.genClosure_reachAvoidCres_iff_exists_specDnf
#print axioms SuFunctor.Universe.IsConstructibleUnion.inter
#print axioms SuFunctor.Universe.isConstructibleUnion_of_genClosure_reachAvoidCrescentsLsc
#print axioms SuFunctor.Universe.coupledSat_crispRA_iff
#print axioms SuFunctor.Universe.crisp_agree
#print axioms SuFunctor.Universe.exists_genClosure_reachAvoid_not_crispGenerated

-- mesh compositor (MeshCompositor): seam-order independence of the
-- conjoin-all-then-envelope-once discipline, the per-seam contrast
-- witnesses, and the mesh consistency obligation
#print axioms seamFold_comp_equiv
#print axioms seamFold_perm
#print axioms coupledSat_sup_meshWall_iff
#print axioms mesh_union_refinement_iff_lsc
#print axioms mesh_union_refinement_iff_probWall
#print axioms meshWall_probWall
#print axioms compile_iSup
#print axioms crescentClass_inter_meshWall
#print axioms relImage_sharedComp_subset_perSeam
#print axioms exists_perSeam_envelope_strict
#print axioms exists_perSeam_envelope_order_dependent
#print axioms MeshCon.pairwiseCon
#print axioms not_meshCon_iff_meshWall_eq_top
#print axioms exists_pairwiseCon_not_meshCon
#print axioms exists_drop_wall_weakens

-- stochastic witnesses (StochasticWitnesses): mass is the narrowly
-- continuous coordinate; escaping point masses have no narrow limit
-- (σ-additivity refusal); event evaluation at a general Borel set is
-- not narrowly continuous and its sublevel walls are not closed; the
-- carrier over ℕ is noncompact
#print axioms tendsto_mass
#print axioms mass_of_tendsto
#print axioms not_tendsto_diracProb_atTop
#print axioms not_exists_tendsto_diracProb
#print axioms tendsto_diracProb_one_div_add_one
#print axioms not_tendsto_diracProb_apply_singleton
#print axioms not_isClosed_setOf_apply_singleton_le
#print axioms not_compactSpace_probabilityMeasure_nat

-- certificate layer (CertificateLayer): the fibrewise-infimum transport
-- dictionary at arbitrary carrier maps, unconditional spec-to-spec
-- monotonicity, system-point transport with its non-surjective fence,
-- the witness-carrying composite, and the compositor's
-- presentation-sensitivity
#print axioms SuFunctor.Universe.le_fibInf_iff
#print axioms SuFunctor.Universe.dip_fibInf_iff
#print axioms SuFunctor.Universe.coupledSat_comap_iff_fibInf
#print axioms SuFunctor.Universe.fibInf_precomp
#print axioms SuFunctor.Universe.coupledSat_comp_iff_of_surjective
#print axioms SuFunctor.Universe.SpecAtom.comap_modelClass_eq_preimage
#print axioms SuFunctor.Universe.SpecDnf.comap_modelClass_eq_preimage
#print axioms SuFunctor.Universe.SpecDnf.comap_modelClass_mono
#print axioms SuFunctor.Universe.SpecAtom.comp_mem_modelClass_comap
#print axioms SuFunctor.Universe.SpecDnf.comp_mem_modelClass_comap
#print axioms SuFunctor.Universe.exists_comp_notMem_modelClass_comap
#print axioms SuFunctor.Universe.SpecDnf.comap_mono
#print axioms SuFunctor.Universe.coupledSat_comp_add_of_dips
#print axioms SuFunctor.Universe.dip_unit_iff
#print axioms SuFunctor.Universe.exists_boxplus_not_semantically_monotone

-- topological citizenship (TopologicalCitizenship): sections of the
-- pushforward through every point, openness of the pushforward, the
-- saturation locus closed under open continuous maps, per-piece local
-- closedness of transported crescents on the surjective stratum,
-- constructibility preservation for transport and for the atom-level
-- compositor at any liveness assignment, and the
-- constructible-not-locally-closed exhibit
#print axioms SuFunctor.Universe.isOpenMap_belPush
#print axioms SuFunctor.Universe.isClosed_setOf_saturated
#print axioms SuFunctor.Universe.isClosed_satClass
#print axioms SuFunctor.Universe.isLocallyClosed_transportClass_crescentClass
#print axioms SuFunctor.Universe.IsConstructibleUnion.iUnion_fin
#print axioms SuFunctor.Universe.isConstructibleUnion_transportClass_dnfClass
#print axioms SuFunctor.Universe.isConstructibleUnion_boxplusDnf
#print axioms SuFunctor.Universe.transportClass_id
#print axioms SuFunctor.Universe.not_isLocallyClosed_exhibitClass
#print axioms SuFunctor.Universe.exists_transportClass_constructible_not_locallyClosed

#print axioms SuFunctor.Universe.Dip.proper
#print axioms SuFunctor.Universe.dip_top_iff_proper
#print axioms SuFunctor.Universe.coupledSat_insert_top_iff
#print axioms SuFunctor.Universe.coupledSat_insert_top_of_nonempty
#print axioms SuFunctor.Universe.SpecAtom.coupledSat_safetyOnly_iff
#print axioms SuFunctor.Universe.SpecAtom.coupledSat_single_iff
#print axioms SuFunctor.Universe.matching_blocked
#print axioms SuFunctor.Universe.splitting_blocked
#print axioms SuFunctor.Universe.blocked_famClass_subset
#print axioms SuFunctor.Universe.EntDeriv.sound
#print axioms SuFunctor.Universe.SatDeriv.sound
#print axioms SuFunctor.Universe.entDeriv_of_famClass_subset
#print axioms SuFunctor.Universe.entDeriv_of_valid
#print axioms SuFunctor.Universe.EntDeriv.refl
#print axioms SuFunctor.Universe.EntDeriv.cut
#print axioms SuFunctor.Universe.EntDeriv.of_not_con
#print axioms SuFunctor.Universe.satDeriv_self_of_con
#print axioms SuFunctor.Universe.SatDeriv.proper
#print axioms SuFunctor.Universe.not_satDeriv_top
#print axioms SuFunctor.Universe.SpecDnf.ofFam_modelClass
#print axioms SuFunctor.Universe.SpecDnf.exists_ofFam_eq
#print axioms SuFunctor.Universe.SatDeriv.compileNC_mem

-- total citizenship (TotalCitizenship): functoriality of the
-- pushforward, contravariant factoring of class transport, injectivity
-- of the pushforward along injective outcome maps, saturation on the
-- injective stratum and its invariance under the range factorization,
-- closedness of the saturated locus along every outcome map, the biting
-- case split with the total structure theorem and its injective-stratum
-- exact-crescent corollary, per-piece local closedness and
-- constructibility preservation along every outcome map, and the
-- non-biting seam exhibit
#print axioms SuFunctor.Universe.BelState.push_comp
#print axioms SuFunctor.Universe.transportClass_comp
#print axioms SuFunctor.Universe.BelState.push_injective
#print axioms SuFunctor.Universe.saturated_of_injective
#print axioms SuFunctor.Universe.saturated_rangeFactorization_iff
#print axioms SuFunctor.Universe.isClosed_satClass_total
#print axioms SuFunctor.Universe.biting_of_surjective
#print axioms SuFunctor.Universe.transportClass_crescentClass_total
#print axioms SuFunctor.Universe.transportClass_crescentClass_of_injective
#print axioms SuFunctor.Universe.isLocallyClosed_transportClass_crescentClass_total
#print axioms SuFunctor.Universe.isConstructibleUnion_transportClass_dnfClass_total
#print axioms SuFunctor.Universe.exists_not_biting_transportClass_ne
