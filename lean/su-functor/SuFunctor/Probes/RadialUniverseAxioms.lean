import SuFunctor.Universe.RadialUniverse

/-! # Axiom audit for the radial universe

Prints the axiom footprint of the radial-universe module: the
definitional isomorphism at the general carrier, the type-level
exclusions, the exact-stratum membership characterization, the radial
wall and ray entry with their bridge, universal properness, and the
contradictory-equality composite.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.Universe.General.compileEquiv
#print axioms SuFunctor.Universe.General.compile_top_eq_bot
#print axioms SuFunctor.Universe.General.RadialUniverse.coe_bot
#print axioms SuFunctor.Universe.General.isClosed_singleton_zero
#print axioms SuFunctor.Universe.General.not_isCredalBody_empty
#print axioms SuFunctor.Universe.General.not_isRadial_singleton
#print axioms SuFunctor.Universe.General.not_isCredalBody_singleton
#print axioms SuFunctor.Universe.General.compile_ne_singleton
#print axioms SuFunctor.Adequacy.cwall_toJoint_eq_top
#print axioms SuFunctor.Adequacy.radialPen_cwall_iff
#print axioms SuFunctor.Adequacy.radialPen_rwall
#print axioms SuFunctor.Adequacy.rwall_eq_cwall_of_downClosed
#print axioms SuFunctor.Adequacy.rwall_and_of_downClosed
#print axioms SuFunctor.Adequacy.cwall_singletonC
#print axioms SuFunctor.Adequacy.not_radialPen_pinningFloor
#print axioms SuFunctor.Adequacy.rwall_singletonC
#print axioms SuFunctor.Adequacy.radialPen_rayPoint
#print axioms SuFunctor.Adequacy.rayPoint_zero
#print axioms SuFunctor.Adequacy.rwall_toJoint_zero
#print axioms SuFunctor.Adequacy.rwall_ne_top
#print axioms SuFunctor.Adequacy.coupledSat_rayPoint_rwall_iff
#print axioms SuFunctor.Adequacy.coupledSat_rayPoint_zero_rwall
#print axioms SuFunctor.Adequacy.credalCompile_iff_of_mass_one
#print axioms SuFunctor.Adequacy.coupledSat_rayPoint_rwall_iff_of_mass_one
#print axioms SuFunctor.Adequacy.coupledSat_rayPoint_rwall_iff_of_downClosed
#print axioms SuFunctor.Adequacy.rayPoint_mem_radialDnf_iff
#print axioms SuFunctor.Adequacy.top_notMem_radialDnf
#print axioms SuFunctor.Adequacy.downClosed_asC
#print axioms SuFunctor.Adequacy.asC_zero
#print axioms SuFunctor.Adequacy.asC_dirac
#print axioms SuFunctor.Adequacy.xyEqC_and_xFalseC_dirac
#print axioms SuFunctor.Adequacy.xyEqC_and_yTrueC_dirac
#print axioms SuFunctor.Adequacy.xFalseC_and_yTrueC_dirac
#print axioms SuFunctor.Adequacy.eq_zero_of_contradictory
#print axioms SuFunctor.Adequacy.contradictory_looseConj_iff
#print axioms SuFunctor.Adequacy.contradictory_composite_denotes_bot
#print axioms SuFunctor.Adequacy.contradictory_composite_ne_top
#print axioms SuFunctor.Adequacy.coupledSat_bot_contradictory
