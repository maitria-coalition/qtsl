import SuFunctor.Plain.CheckerFace

/-! # Axiom audit for the checker face

Prints the axiom footprint of the exact-stratum checker face: the
credal compile and its bottom corner, the possibilistic wall's zero
set, the Boolean upper probability (both dialects), and the verdict
identification with its *ex falso* corner.  Expected footprint for
every entry: `propext`, `Classical.choice`, `Quot.sound` — the
standard three, no `sorryAx`, nothing else. -/

open SuFunctor.Plain

#print axioms SuFunctor.Plain.suppIn_empty
#print axioms SuFunctor.Plain.possWall_eq_zero_iff
#print axioms SuFunctor.Plain.Joint.massOn_eq_zero_iff
#print axioms SuFunctor.Plain.Joint.massOn_dirac_of_mem
#print axioms SuFunctor.Plain.upperProb_eq_zero_iff_forall
#print axioms SuFunctor.Plain.upperProb_eq_zero_iff
#print axioms SuFunctor.Plain.semanticallyValid_iff_subset
#print axioms SuFunctor.Plain.semanticallyValid_iff_face
#print axioms SuFunctor.Plain.face_ex_falso
