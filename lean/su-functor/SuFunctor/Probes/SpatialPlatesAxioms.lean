import SuFunctor.SpatialPlates.StokesRows
import SuFunctor.SpatialPlates.MeshLowering

/-! # Axiom audit for the spatial-plates mechanization

Prints the axiom footprint of the headline theorems of the
spatial-plates development: T-POLY (existence, degree data, and the
refusal's necessity), the S1 row with its FTC soundness and Jacobian
block, the S2 jet-edition rows (chain rule through declared jets,
Stokes with boundary terms, wrap wall, x-free discharge), the
heat-torus acid rows at the symbolic stratum, and the T-MESH lowering
with its one-identity per-mesh obligation and replay theorem.
Expected footprint for every entry: `propext`, `Classical.choice`,
`Quot.sound` — the standard three, no `sorryAx`, nothing else. -/

open SuFunctor.SpatialPlates

-- T-POLY
#print axioms SuFunctor.SpatialPlates.Body.den_eq_eval
#print axioms SuFunctor.SpatialPlates.Body.poly_totalDegree_le
#print axioms SuFunctor.SpatialPlates.indicator_not_polynomial
-- S1 + Jacobian block
#print axioms SuFunctor.SpatialPlates.s1_welldef
#print axioms SuFunctor.SpatialPlates.s1_chain
#print axioms SuFunctor.SpatialPlates.s1_sound
#print axioms SuFunctor.SpatialPlates.s1_cov_gate
#print axioms SuFunctor.SpatialPlates.s1_cov_value
#print axioms SuFunctor.SpatialPlates.s1_dilation_refused
-- S2, jet edition
#print axioms SuFunctor.SpatialPlates.totalDeriv_sound
#print axioms SuFunctor.SpatialPlates.s2_stokes_sound
#print axioms SuFunctor.SpatialPlates.s2_wrap_sound
#print axioms SuFunctor.SpatialPlates.xfree_wrap
-- the acid test, symbolic stratum
#print axioms SuFunctor.SpatialPlates.heat_witness_identity
#print axioms SuFunctor.SpatialPlates.heat_by_parts_sound
#print axioms SuFunctor.SpatialPlates.heat_dissipation_symbolic
-- T-MESH
#print axioms SuFunctor.SpatialPlates.meshBody_eq_den
#print axioms SuFunctor.SpatialPlates.sbp_cycle
#print axioms SuFunctor.SpatialPlates.discrete_by_parts
#print axioms SuFunctor.SpatialPlates.t_mesh_replay
