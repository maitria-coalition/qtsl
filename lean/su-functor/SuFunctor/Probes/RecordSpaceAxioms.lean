import SuFunctor.Adequacy.RecordSpace

/-! # Axiom audit for the record-space tie

Prints the axiom footprint of the wire objects of the compiled
systems: the pushforward of laws and constraints with the transported
judgment bridge, the trajectory interface with its definitional state
identification and prefix-reading tight calculus, the wired squares
re-read in the fibres over their own wire objects, and the assignment
interface's erasure identification with the graphical-model square at
its record space.  Expected footprint for every entry: at most
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor.Adequacy

#print axioms SuFunctor.SubPMF.map_injective
#print axioms SuFunctor.Adequacy.cmap_map_iff
#print axioms SuFunctor.Adequacy.looseConj_map
#print axioms SuFunctor.Adequacy.idealPoint_map_mem_diagramDnf_iff
#print axioms SuFunctor.Adequacy.states_trajWire
#print axioms SuFunctor.Adequacy.res_trajTight
#print axioms SuFunctor.Adequacy.su_dtmc_adequacy_fibre
#print axioms SuFunctor.Adequacy.su_dtmc_pathLaw_mem_fibre
#print axioms SuFunctor.Adequacy.su_dtmc_bottom_fibre
#print axioms SuFunctor.Adequacy.su_dtmc_slice_fibre
#print axioms SuFunctor.Adequacy.su_mdp_adequacy_fibre
#print axioms SuFunctor.Adequacy.su_mdp_pathLaw_mem_fibre
#print axioms SuFunctor.Adequacy.su_mdp_bottom_fibre
#print axioms SuFunctor.Adequacy.su_mdp_slice_fibre
#print axioms SuFunctor.Adequacy.su_mdp_demonic_fibre
#print axioms SuFunctor.Adequacy.su_mdp_demonic_fibre'
#print axioms SuFunctor.Adequacy.su_mdp_demonic_bottom_fibre
#print axioms SuFunctor.Adequacy.su_mdp_demonic_slice_fibre
#print axioms SuFunctor.Adequacy.asnState_injective
#print axioms SuFunctor.Adequacy.range_asnState
#print axioms SuFunctor.Adequacy.su_pgm_wiring_asnWire
#print axioms SuFunctor.Adequacy.su_pgm_adequacy_asnWire
#print axioms SuFunctor.Adequacy.su_pgm_jointLaw_mem_asnWire
#print axioms SuFunctor.Adequacy.su_pgm_bottom_asnWire
