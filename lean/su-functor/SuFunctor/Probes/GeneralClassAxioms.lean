import SuFunctor.Universe.General.CrescentStratum
import SuFunctor.Universe.General.TransportGeneral
import SuFunctor.Universe.General.DemonicGeneral

/-! # Axiom audit for the general class/transport/seam stratum

Prints the axiom footprint of the headline theorems of the class
stratum at the general carrier (crescent geometry, judgment transport,
constructible algebra), the transport tier (dictionary, invariance,
structure theorem, off-surjective failures), the compositor dictionary,
and the seam conjunct's general wall species.  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor.Universe.General

#print axioms compile_sup
#print axioms compile_inf
#print axioms compile_zero
#print axioms dip_iff_compile_escape
#print axioms coupledSat_iff_compile
#print axioms compileF_mem_crescentClass_iff
#print axioms isClosed_safety_face
#print axioms isOpen_escape_face
#print axioms isLocallyClosed_crescentClass
#print axioms isConstructibleUnion_crescentClass
#print axioms escape_face_sup
#print axioms crescentClass_inter_crescentClass
#print axioms compileF_mem_dnfClass_iff
#print axioms isConstructibleUnion_dnfClass
#print axioms dnfClass_append
#print axioms ctxOrE_dnfClass
#print axioms mass_push
#print axioms push_scalePoint
#print axioms compile_pullPen
#print axioms lowerSemicontinuous_pullPen
#print axioms probPush_surjective_of_section
#print axioms push_surjective_of_probPush_surjective
#print axioms coupledSat_pullPen_iff
#print axioms transportClass_singleton_compileF
#print axioms transportClass_crescentClass_subset
#print axioms mem_transportClass_of_closed_image
#print axioms transportClass_crescentClass
#print axioms exists_coupledSat_not_pullPen
#print axioms exists_coupledSat_pullPen_not
#print axioms exists_transport_not_subset_pulled_crescent
#print axioms mem_compile_add_iff
#print axioms compile_add_radProd
#print axioms lowerSemicontinuous_boxplus
#print axioms lowerSemicontinuous_probWall_iff
#print axioms crescentClass_inter_wall
#print axioms cross_site_union_refinement_iff_probWall
