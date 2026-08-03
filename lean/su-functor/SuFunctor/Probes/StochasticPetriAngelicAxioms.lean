import SuFunctor.Adequacy.StochasticPetriAngelic

/-! # Axiom audit for the angelic face and the law-level plurality

Prints the axiom footprint of the headline statements: the angelic
verdict operator's slice discipline (the zero-mass fact, the
zero-threshold atom at zero, the un-sliced degeneracy, the equal-mass
transfer on unions of rays and on exact families), the net-level
angelic face (the feeding equivalence, the witness and restriction
transfers, both flatten-facing transfer forms, the angelic directed
cell, the wired verdict), and the `net₁` controls (the always-discard
closed chain's absorption, rate, exit, and step; the drain-trajectory
weights; the law-level plurality; the polarity-split pair; the
slice-teeth control).  Expected footprint for every entry: within
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

#print axioms SuFunctor.SubPMF.zero_mass
#print axioms SuFunctor.leC_zero_of_zero
#print axioms SuFunctor.satAngelic_whole_degenerate
#print axioms SuFunctor.satAngelic_unionRays
#print axioms SuFunctor.satAngelic_unionSingletons
#print axioms SuFunctor.Adequacy.FinISPN.satAngelic_ispnDemonicCredal
#print axioms SuFunctor.Adequacy.FinISPN.ispn_angelic_of_member
#print axioms SuFunctor.Adequacy.FinISPN.ispn_demonic_verdict_to_member
#print axioms SuFunctor.Adequacy.FinISPN.ispn_demonic_upper_to_member
#print axioms SuFunctor.Adequacy.FinISPN.satAngelic_unsliced_degenerate
#print axioms SuFunctor.Adequacy.FinISPN.satAngelic_unsliced_leC_degenerate
#print axioms SuFunctor.Adequacy.FinISPN.flatten_angelic_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_demonic_verdict_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.flatten_angelic_directed_of_agree
#print axioms SuFunctor.Adequacy.FinISPN.su_ispn_angelic_verdict
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_discard_zenoFree
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_tangibleInit
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_close_init
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_imStep_discard
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_discard_absorb_i10
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_discard_rate
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_discard_exit
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_step_uniform
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_step_discard
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_wt_uniform
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_wt_discard
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_laws_differ
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_demonic_laws_plural
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_angelic_pos
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_not_demonic_split
#print axioms SuFunctor.Adequacy.SpnAngelicControls.net₁_not_satAngelic_leC_univ_zero
