import SuFunctor.Adequacy.Funnel

/-! # Axiom audit for the funnel pattern (certificate-layer conjunction)

Prints the axiom footprint of the funnel pattern's statements: the
assembly refusal exactness, the shared-citation equations, the positive
same-subject composite certificate, the monotone-conjunction package
with its strictness witness, the demanded-dip-family refusal, the
presentations fence, and the restated compositor refusal.  Expected
footprint for every entry: within `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

#print axioms SuFunctor.Adequacy.FunnelParts.assemble_isSome_iff
#print axioms SuFunctor.Adequacy.FunnelParts.assemble_gate_shared
#print axioms SuFunctor.Adequacy.funnel_gate_shared
#print axioms SuFunctor.Adequacy.funnel_coupledSat_of_parts
#print axioms SuFunctor.Adequacy.funnel_floor_ge_transit
#print axioms SuFunctor.Adequacy.funnel_floor_ge_hold
#print axioms SuFunctor.Adequacy.funnel_marks_superset
#print axioms SuFunctor.Adequacy.exists_funnel_floor_ne_transit
#print axioms SuFunctor.Adequacy.exists_funnel_parts_not_coupledSat
#print axioms SuFunctor.Adequacy.exists_funnel_split_strengthens
#print axioms SuFunctor.Adequacy.funnelDecl_not_system_former
