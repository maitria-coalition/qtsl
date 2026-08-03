import SuFunctor.Universe.General.Closedness
import SuFunctor.Universe.General.CheckerAnchor
import SuFunctor.Universe.General.CredalPoset
import SuFunctor.Universe.General.Richardson
import SuFunctor.Universe.General.Riesz
import SuFunctor.Universe.General.WallTaxonomy

/-!
# Axiom receipts, general-carrier dictionary tier

`#print axioms` receipts for the penalty↔body dictionary over the
general subprobability carrier: the closedness⟺lsc equivalence, the
image characterization and its inverse laws, the checker anchor, and
the credal-body atlas inclusions — so the axiom footprint is
inspectable at build time.
-/

open SuFunctor.Universe.General

#print axioms SuFunctor.Universe.General.isClosed_compile
#print axioms SuFunctor.Universe.General.isClosed_compile_iff
#print axioms SuFunctor.Universe.General.exists_lsc_compile_eq_iff
#print axioms SuFunctor.Universe.General.compile_rayPenalty
#print axioms SuFunctor.Universe.General.rayPenalty_compile
#print axioms SuFunctor.Universe.General.compile_injective
#print axioms SuFunctor.Universe.General.compile_subset_compile_iff
#print axioms SuFunctor.Universe.General.rayGauge_mem_raySet
#print axioms SuFunctor.Universe.General.lowerSemicontinuous_rayPenalty
#print axioms SuFunctor.Universe.General.upperSemicontinuous_rayGauge
#print axioms SuFunctor.Universe.General.sat_wall_iff
#print axioms SuFunctor.Universe.General.sat_wall_wall_iff
#print axioms SuFunctor.Universe.General.sat_iff_sublevel_subset
#print axioms SuFunctor.Universe.General.CredalPoset.IsUltra.isConvexCredalBody
#print axioms SuFunctor.Universe.General.CredalPoset.IsHL.isUltra
#print axioms SuFunctor.Universe.General.CredalPoset.convexBody_compile_of_gradeConvex
#print axioms SuFunctor.Universe.General.CredalPoset.scaleSegment_eq_compile_dirWall
#print axioms SuFunctor.Universe.General.CredalPoset.IsCozman.isConvexCredalBody
#print axioms SuFunctor.Universe.General.CredalPoset.IsPrevisionBody.isUltra
#print axioms SuFunctor.Universe.General.CredalPoset.isClosed_ptwiseDownHull
#print axioms SuFunctor.Universe.General.CredalPoset.IsMVS.isUltra
#print axioms SuFunctor.Universe.General.CredalPoset.gradeConvex_of_penaltyConvex
#print axioms SuFunctor.Universe.General.CredalPoset.IsRichardsonBody.isConvexCredalBody
#print axioms SuFunctor.Universe.General.SubProbabilityMeasure.toRadon_injective
#print axioms SuFunctor.Universe.General.SubProbabilityMeasure.rieszMeasure_toRadon
#print axioms SuFunctor.Universe.General.WallTaxonomy.possibilisticBody_eq_leRegion_zero
#print axioms SuFunctor.Universe.General.WallTaxonomy.isUltra_leRegion
#print axioms SuFunctor.Universe.General.WallTaxonomy.isUltra_possibilisticBody
#print axioms SuFunctor.Universe.General.WallTaxonomy.isClosed_geRegion
#print axioms SuFunctor.Universe.General.WallTaxonomy.not_ptwiseDown_geRegion
#print axioms SuFunctor.Universe.General.WallTaxonomy.leRegion_half_ne_possibilisticBody
