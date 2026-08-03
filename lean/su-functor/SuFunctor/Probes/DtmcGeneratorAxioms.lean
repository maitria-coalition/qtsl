import SuFunctor.Adequacy.DtmcGenerator

/-! # Axiom audit for the DTMC one-step generator form

Prints the axiom footprint of the generator-form module: the recompute
form and its compiled reading, the segment-Dynkin identity with its
premise wrapper and supermartingale corollaries, the mark-polarity
lemma, the bottom fixtures (all safety, no liveness, and the
polarity-control wrong direction), the live-subject two-face fixture,
and the trajectory-stratum verdict tie.  Expected footprint for every
entry: `propext`, `Classical.choice`, `Quot.sound` — the standard
three, no `sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.Adequacy.transferRow_compile
#print axioms SuFunctor.Adequacy.genRow_compile
#print axioms SuFunctor.Adequacy.rowsLaw_expect_succ
#print axioms SuFunctor.Adequacy.rowsLaw_expect_step
#print axioms SuFunctor.Adequacy.rowsLaw_expect_step_of_genForm
#print axioms SuFunctor.Adequacy.rowsLaw_expect_succ_le_of_nonpos
#print axioms SuFunctor.Adequacy.rowsLaw_expect_le_of_nonpos
#print axioms SuFunctor.SubPMF.dirac_prob_of_not_mem
#print axioms SuFunctor.Adequacy.cwall_pos_at_idealPoint_iff
#print axioms SuFunctor.Adequacy.bottom_sat_massLE_floor
#print axioms SuFunctor.Adequacy.bottom_refutes_liveMark
#print axioms SuFunctor.Adequacy.bottom_sat_unNegated_mark
#print axioms SuFunctor.Adequacy.dirac_sat_two_faces
#print axioms SuFunctor.Adequacy.rowsLaw_sat_floor_iff
