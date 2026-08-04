import SuFunctor.Adequacy.StochasticPetriColouredDirected

/-! # Axiom audit for the coloured flatten-facing directed faces

Prints the axiom footprint of the flatten-facing transfer forms at
colour: the interface tier (both directed cells and both verdict
transfers, agreement in), the composed tier at the community grain,
the discharged tier at the constructed coloured flattening, and the
premise-bundle entry points.  Expected footprint for every entry:
within `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Adequacy.FinCISPN.flatten_demonic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_angelic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_angelic_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_demonic_verdict_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_demonic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_angelic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_demonic_directed
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_angelic_directed
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_demonic_directed_of_premises
#print axioms SuFunctor.Adequacy.FinCISPN.flatten_composed_angelic_directed_of_premises
