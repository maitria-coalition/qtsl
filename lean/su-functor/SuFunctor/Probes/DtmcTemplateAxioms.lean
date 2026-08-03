import SuFunctor.Adequacy.DtmcTemplate

/-! # Axiom audit for the geometric template collapse

Prints the axiom footprint of the template-collapse module: the one
lemma by which a geometric template's unboundedly many per-instance
contraction inequalities reduce to a single exact-rational check.
Expected footprint: `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.genFormTemplate_collapse
