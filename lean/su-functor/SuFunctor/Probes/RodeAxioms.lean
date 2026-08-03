import SuFunctor.Adequacy.Rode

/-! # Axiom audit for the RODE adequacy square

Prints the axiom footprint of the headline theorems of the
random-differential-equation square: the per-draw connector, square,
and pinning specializations of the ODE seam, the parameter-box union
face (set identities, bundling, and the square proper), the boundary
and monotonicity lemmas, the per-draw Dirac face and the properness
witness, the demonic rectangle, and the semantic-universe wiring.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.isRodeSol_iff_integralCurve
#print axioms SuFunctor.Adequacy.rode_draw_adequacy
#print axioms SuFunctor.Adequacy.rodeSols_eqOn_of_lipschitzOnWith
#print axioms SuFunctor.Adequacy.mem_rodeSols_iff
#print axioms SuFunctor.Adequacy.odeSols_eq_inter
#print axioms SuFunctor.Adequacy.rodeSols_eq
#print axioms SuFunctor.Adequacy.rodeAtoms_iff
#print axioms SuFunctor.Adequacy.rodeSols_eq_integralCurves
#print axioms SuFunctor.Adequacy.rode_adequacy
#print axioms SuFunctor.Adequacy.rodeSols_mono
#print axioms SuFunctor.Adequacy.rodeSols_empty
#print axioms SuFunctor.Adequacy.rodeAtoms_dirac_of_mem
#print axioms SuFunctor.Adequacy.rodeAtoms_dirac_const
#print axioms SuFunctor.Adequacy.rodeBoxSols_eq
#print axioms SuFunctor.Adequacy.rodeBoxAtoms_iff
#print axioms SuFunctor.Adequacy.rode_box_adequacy
#print axioms SuFunctor.Adequacy.su_rode_wiring
#print axioms SuFunctor.Adequacy.su_rode_adequacy
#print axioms SuFunctor.Adequacy.su_rode_dirac_mem
#print axioms SuFunctor.Adequacy.su_rode_vacuous_mem
#print axioms SuFunctor.Adequacy.su_rode_bottom
