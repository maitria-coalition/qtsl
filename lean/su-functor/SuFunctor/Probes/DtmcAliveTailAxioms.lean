import SuFunctor.Adequacy.DtmcAliveTail

/-! # Axiom audit for the alive-mass tail module

Prints the axiom footprint of the regional-decay lemma, the alive-mass
tail, and the two countermodel teeth.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.massAt_expect_on_le_of_regionContraction
#print axioms SuFunctor.Adequacy.dtmcAliveTail_of_regionContraction
#print axioms SuFunctor.Adequacy.aliveTail_needs_floor
#print axioms SuFunctor.Adequacy.aliveTail_needs_no_reentry
