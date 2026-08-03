import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Axiom audit for the semantic-universe wiring of the adequacy squares

Prints the axiom footprint of the wiring layer: the scalar seam, the
wall-system reading of the coupled judgment, the ideal-point entry and
its judgment bridge, the presentation algebra (safety merge, fold, and
the refuted `⊓`-merge), the transport layer, the ray-vs-singleton
fence, and the four squares' wiring theorems with their option-A
corners and slice corollaries.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor SuFunctor.Adequacy

#print axioms SuFunctor.SubPMF.toJoint_injective
#print axioms SuFunctor.Adequacy.coupledSat_wallPen_iff
#print axioms SuFunctor.Adequacy.wallPen_inter
#print axioms SuFunctor.Adequacy.coupledSat_idealPoint_iff
#print axioms SuFunctor.Adequacy.idealPoint_proper
#print axioms SuFunctor.Adequacy.idealPoint_ne_top
#print axioms SuFunctor.Adequacy.cwall_toJoint_eq_zero_iff
#print axioms SuFunctor.Adequacy.coupledSat_idealPoint_cwall_iff
#print axioms SuFunctor.Adequacy.cwall_and
#print axioms SuFunctor.Adequacy.cwall_looseConj
#print axioms SuFunctor.Adequacy.exists_cwall_and_ne_inf
#print axioms SuFunctor.Adequacy.idealPoint_mem_diagramDnf_iff
#print axioms SuFunctor.Adequacy.top_notMem_diagramDnf
#print axioms SuFunctor.Adequacy.coupledSat_rayWall_singleton_floor_fails
#print axioms SuFunctor.Adequacy.su_dtmc_wiring
#print axioms SuFunctor.Adequacy.su_dtmc_adequacy
#print axioms SuFunctor.Adequacy.su_dtmc_pathLaw_mem
#print axioms SuFunctor.Adequacy.su_dtmc_vacuous
#print axioms SuFunctor.Adequacy.su_dtmc_bottom
#print axioms SuFunctor.Adequacy.FinDTMC.pathLaw_ne_zero
#print axioms SuFunctor.Adequacy.su_dtmc_slice
#print axioms SuFunctor.Adequacy.su_mdp_adequacy
#print axioms SuFunctor.Adequacy.su_mdp_pathLaw_mem
#print axioms SuFunctor.Adequacy.su_mdp_bottom
#print axioms SuFunctor.Adequacy.FinMDP.pathLaw_ne_zero
#print axioms SuFunctor.Adequacy.su_mdp_slice
#print axioms SuFunctor.Adequacy.su_mdp_demonic_wiring
#print axioms SuFunctor.Adequacy.su_mdp_demonic_wiring'
#print axioms SuFunctor.Adequacy.su_mdp_demonic_bottom
#print axioms SuFunctor.Adequacy.su_mdp_demonic_slice
#print axioms SuFunctor.Adequacy.su_pgm_wiring
#print axioms SuFunctor.Adequacy.su_pgm_adequacy
#print axioms SuFunctor.Adequacy.su_pgm_jointLaw_mem
#print axioms SuFunctor.Adequacy.su_pgm_bottom
#print axioms SuFunctor.Adequacy.Pgm.FinBN.jointLaw_ne_zero
#print axioms SuFunctor.Adequacy.su_pgm_slice
