import SuFunctor.Adequacy.CheckerCarrier

/-! # Axiom audit for the checker carrier

Prints the axiom footprint of the carrier tie: the wall-dialect
equation, the coupled judgment between wall systems, the valuation
embedding with its range identification, the transport of the face
calculus along an injection of carriers, and the verdict read at the
record space — membership form and fibre form.  Expected footprint for
every entry: at most `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.possWall_eq_wallPen
#print axioms SuFunctor.Adequacy.wallPen_le_wallPen_iff
#print axioms SuFunctor.Adequacy.suppIn_subset_suppIn_iff
#print axioms SuFunctor.Adequacy.coupledSat_wallPen_wallPen_iff
#print axioms SuFunctor.Adequacy.semanticallyValid_iff_mem_modelClass
#print axioms SuFunctor.Adequacy.valState_injective
#print axioms SuFunctor.Adequacy.range_valState
#print axioms SuFunctor.Adequacy.massOn_push
#print axioms SuFunctor.Adequacy.suppIn_image
#print axioms SuFunctor.Adequacy.upperProb_image
#print axioms SuFunctor.Adequacy.semanticallyValid_iff_face_valWire
#print axioms SuFunctor.Adequacy.semanticallyValid_iff_mem_modelClass_valWire
#print axioms SuFunctor.Adequacy.semanticallyValid_iff_fibre
