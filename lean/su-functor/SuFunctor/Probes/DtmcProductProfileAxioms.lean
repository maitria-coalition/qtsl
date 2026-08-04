import SuFunctor.Adequacy.DtmcProductProfile

/-! # Axiom audit for the product-profile collapse

Prints the axiom footprint of the product-profile collapse module —
the d-dimensional face of the template collapse: per-coordinate
factorization, profile stabilization, and the class-bound composition
by which the transfer inequalities of an infinite window-exterior
region reduce to finitely many exact-rational checks, plus the
necessity witness for the window-reach side condition.  Expected
footprint: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.aliveStep_factor
#print axioms SuFunctor.Adequacy.transferRatio_of_ge
#print axioms SuFunctor.Adequacy.transferRatio_le_rMax
#print axioms SuFunctor.Adequacy.productProfile_collapse
#print axioms SuFunctor.Adequacy.productProfile_collapse_window
#print axioms SuFunctor.Adequacy.rampProfile_needs_window_reach
