import SuFunctor.Universe.General.Faces
import SuFunctor.Universe.General.ClosureGeneral
import SuFunctor.Universe.General.GenerationGeneral

/-!
# Axiom receipts, general-carrier judgment tier

`#print axioms` receipts for the general-carrier siblings of the finite
judgment storey: the connective order faces, the closure table, and the
gamble-row generation theorems — so the axiom footprint is inspectable
at build time.  Expected: `[propext, Classical.choice, Quot.sound]`
throughout, `sorryAx` nowhere.
-/

open SuFunctor.Universe.General

-- faces
#print axioms SuFunctor.Universe.General.sat_sup_iff
#print axioms SuFunctor.Universe.General.sat_iSup_iff
#print axioms SuFunctor.Universe.General.entails_inf_iff
#print axioms SuFunctor.Universe.General.exists_sat_inf_not_sat
#print axioms SuFunctor.Universe.General.wall_sup_wall
#print axioms SuFunctor.Universe.General.wall_inf_wall
#print axioms SuFunctor.Universe.General.wall_le_wall_iff
#print axioms SuFunctor.Universe.General.eq_wall_of_two_valued
#print axioms SuFunctor.Universe.General.lowerSemicontinuous_wall_iff
#print axioms SuFunctor.Universe.General.gradedObligation_iff_le
#print axioms SuFunctor.Universe.General.gradedObligation_wall_iff
#print axioms SuFunctor.Universe.General.conj_disj_distrib

-- closure table
#print axioms SuFunctor.Universe.General.lsc_add
#print axioms SuFunctor.Universe.General.lsc_sup
#print axioms SuFunctor.Universe.General.lsc_inf
#print axioms SuFunctor.Universe.General.lsc_iSup
#print axioms SuFunctor.Universe.General.lsc_comp
#print axioms SuFunctor.Universe.General.continuous_tilt
#print axioms SuFunctor.Universe.General.lsc_tilt
#print axioms SuFunctor.Universe.General.continuous_tiltDir
#print axioms SuFunctor.Universe.General.lsc_tiltDir

-- generation
#print axioms SuFunctor.Universe.General.isOpen_gambleAtomSet
#print axioms SuFunctor.Universe.General.lowerSemicontinuous_gambleRow
#print axioms SuFunctor.Universe.General.isInducing_testProfile
#print axioms SuFunctor.Universe.General.exists_gambleRowSet_subset
#print axioms SuFunctor.Universe.General.iSup_gambleRows_eq_self
#print axioms SuFunctor.Universe.General.exists_countable_gambleRows_eq_self
#print axioms SuFunctor.Universe.General.iSup_gambleRows_eq_self_prob
#print axioms SuFunctor.Universe.General.iSup_gambleRows_eq_self_state
#print axioms SuFunctor.Universe.General.exists_countable_gambleRows_eq_self_prob
#print axioms SuFunctor.Universe.General.exists_countable_gambleRows_eq_self_state
#print axioms SuFunctor.Universe.General.secondCountableTopology_probabilityMeasure
