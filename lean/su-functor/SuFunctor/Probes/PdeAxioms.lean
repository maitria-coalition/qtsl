import SuFunctor.Adequacy.Pde

/-! # Axiom audit for the frame-level PDE adequacy square

Prints the axiom footprint of the headline theorems of the
frame-level PDE square: the concept-generic mesh engine (paste,
periodization, ring glue, bundling, the wiring theorem, the square,
the consistency witness), the heat specialization ties, the jet-grain
interface lemmas and the formation-rule square, the instance
corollaries and equilibrium receipts, the rung ladder, and the
semantic-universe wiring.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.LocalRows.SolOn.mono
#print axioms SuFunctor.Adequacy.LocalRows.paste_isSolOn
#print axioms SuFunctor.Adequacy.LocalRows.chain_glues
#print axioms SuFunctor.Adequacy.LocalRows.periodize_isSolOn
#print axioms SuFunctor.Adequacy.LocalRows.mesh_glues
#print axioms SuFunctor.Adequacy.LocalRows.meshAtoms_iff
#print axioms SuFunctor.Adequacy.LocalRows.meshSols_eq_classical
#print axioms SuFunctor.Adequacy.LocalRows.mesh_adequacy
#print axioms SuFunctor.Adequacy.LocalRows.isMeshSol_recOf
#print axioms SuFunctor.Adequacy.LocalRows.recOf_mem_classicalRecs
#print axioms SuFunctor.Adequacy.LocalRows.meshAtoms_dirac_of_torusSol
#print axioms SuFunctor.Adequacy.LocalRows.diracC_recOf_entails
#print axioms SuFunctor.Adequacy.LocalRows.meshAtoms_consistent_of
#print axioms SuFunctor.Adequacy.heatAtoms_eq_meshAtoms
#print axioms SuFunctor.Adequacy.isHeatTorusSol_iff
#print axioms SuFunctor.Adequacy.heatClassicalRecs_eq
#print axioms SuFunctor.Adequacy.heat_adequacy_of_mesh
#print axioms SuFunctor.Adequacy.iteratedDeriv_congr_on
#print axioms SuFunctor.Adequacy.iteratedDeriv_comp_sub_const
#print axioms SuFunctor.Adequacy.iteratedDeriv_const_of_pos
#print axioms SuFunctor.Adequacy.PdeAt.congr
#print axioms SuFunctor.Adequacy.PdeAt.comp_sub_const
#print axioms SuFunctor.Adequacy.pde_adequacy
#print axioms SuFunctor.Adequacy.jetEval_const
#print axioms SuFunctor.Adequacy.pdeAt_const
#print axioms SuFunctor.Adequacy.PdeMechanism.isTorusSol_const
#print axioms SuFunctor.Adequacy.pdeAtoms_consistent_of_equilibrium
#print axioms SuFunctor.Adequacy.heatMechanism_eval
#print axioms SuFunctor.Adequacy.iteratedDeriv_two
#print axioms SuFunctor.Adequacy.heatAt_iff_pdeAt
#print axioms SuFunctor.Adequacy.burgers_adequacy
#print axioms SuFunctor.Adequacy.kpp_adequacy
#print axioms SuFunctor.Adequacy.coupled_adequacy
#print axioms SuFunctor.Adequacy.burgers_equilibrium
#print axioms SuFunctor.Adequacy.kpp_equilibrium_zero
#print axioms SuFunctor.Adequacy.kpp_equilibrium_one
#print axioms SuFunctor.Adequacy.kpp_not_equilibrium_half
#print axioms SuFunctor.Adequacy.coupled_equilibrium_zero
#print axioms SuFunctor.Adequacy.rung_adequacy
#print axioms SuFunctor.Adequacy.meshSols_le_rung
#print axioms SuFunctor.Adequacy.pde_rung_transfer
#print axioms SuFunctor.Adequacy.su_mesh_wiring
#print axioms SuFunctor.Adequacy.su_mesh_adequacy
#print axioms SuFunctor.Adequacy.su_pde_wiring
#print axioms SuFunctor.Adequacy.su_pde_adequacy
#print axioms SuFunctor.Adequacy.su_pde_dirac_mem
#print axioms SuFunctor.Adequacy.su_pde_vacuous_mem
#print axioms SuFunctor.Adequacy.su_pde_bottom
