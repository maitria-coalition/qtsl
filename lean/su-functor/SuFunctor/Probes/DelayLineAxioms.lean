import SuFunctor.Adequacy.DelayLine

/-! # Axiom audit for the delay-line adequacy square

Prints the axiom footprint of the headline theorems of the delay-line
square: the left edge in both directions (constancy along
characteristics; reparameterization satisfies the rows), the wiring
theorem and its projections, the history-descent statement, the
bundling lemma, the square itself, the per-solution Dirac face, and
the properness witnesses.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.IsTransportSol.trace_const
#print axioms SuFunctor.Adequacy.isTransportSol_reparam
#print axioms SuFunctor.Adequacy.IsCompositeSol.field_eq
#print axioms SuFunctor.Adequacy.IsCompositeSol.outflow_delay
#print axioms SuFunctor.Adequacy.IsCompositeSol.field_slice_is_history
#print axioms SuFunctor.Adequacy.composite_iff_dde
#print axioms SuFunctor.Adequacy.composite_path_proj
#print axioms SuFunctor.Adequacy.delayAtoms_iff
#print axioms SuFunctor.Adequacy.compositeSols_eq_classical
#print axioms SuFunctor.Adequacy.delayline_adequacy
#print axioms SuFunctor.Adequacy.delayAtoms_dirac_of_dde
#print axioms SuFunctor.Adequacy.diracC_recOf_entails
#print axioms SuFunctor.Adequacy.suppC_zero
#print axioms SuFunctor.Adequacy.suppC_dirac
#print axioms SuFunctor.Adequacy.isDdeSol_const
#print axioms SuFunctor.Adequacy.composite_const
