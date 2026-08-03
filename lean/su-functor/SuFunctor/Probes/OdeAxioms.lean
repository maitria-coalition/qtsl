import SuFunctor.Adequacy.Ode

/-! # Axiom audit for the ODE adequacy square

Prints the axiom footprint of the headline theorems of the ODE
square: the delay-line tie, the connector in both directions (FTC-2
for the forward rows, FTC-1 at interior points), the community-form
equivalences (integral-curve and Picard integral forms), the pinning
theorems, the bundling lemmas, the square proper and its demonic
initial-box face, the per-solution Dirac face, the properness
witnesses, and the semantic-universe wiring.  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.isOdeCell_iff_rows
#print axioms SuFunctor.Adequacy.IsOdeRows.integral_eq
#print axioms SuFunctor.Adequacy.IsOdeRows.hasDerivAt
#print axioms SuFunctor.Adequacy.isOdeRows_iff_integralCurve
#print axioms SuFunctor.Adequacy.isOdeSol_iff_integral
#print axioms SuFunctor.Adequacy.isOdeSol_iff_integralCurve
#print axioms SuFunctor.Adequacy.odeSols_eqOn_of_lipschitzOnWith
#print axioms SuFunctor.Adequacy.odeSols_eqOn_of_lipschitz
#print axioms SuFunctor.Adequacy.odeAtoms_iff
#print axioms SuFunctor.Adequacy.odeSols_eq_integralCurves
#print axioms SuFunctor.Adequacy.ode_adequacy
#print axioms SuFunctor.Adequacy.odeAtoms_dirac_of_mem
#print axioms SuFunctor.Adequacy.diracC_sol_entails
#print axioms SuFunctor.Adequacy.isOdeSol_const
#print axioms SuFunctor.Adequacy.odeAtoms_dirac_const
#print axioms SuFunctor.Adequacy.odeBoxSols_eq
#print axioms SuFunctor.Adequacy.odeBoxAtoms_iff
#print axioms SuFunctor.Adequacy.ode_box_adequacy
#print axioms SuFunctor.Adequacy.su_ode_wiring
#print axioms SuFunctor.Adequacy.su_ode_adequacy
#print axioms SuFunctor.Adequacy.su_ode_dirac_mem
#print axioms SuFunctor.Adequacy.su_ode_vacuous_mem
#print axioms SuFunctor.Adequacy.su_ode_bottom
