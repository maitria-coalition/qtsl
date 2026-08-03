import SuFunctor.Adequacy.CtmcJumpChain
import SuFunctor.Adequacy.SemanticUniverseWiring

/-! # Axiom audit for the CTMC jump-chain square

Prints the axiom footprint of the continuous-time adequacy square at
its jump-chain face: the derived-stochasticity theorems, the
compile-commutes triangle, the square, the blindness receipts, the
rate-factorization identity, the transported connector, and the
semantic-universe wiring.  Expected footprint for every entry:
`propext`, `Classical.choice`, `Quot.sound` — the standard three, no
`sorryAx`, nothing else. -/

open SuFunctor

#print axioms SuFunctor.Adequacy.FinCTMC.offRate_nonneg
#print axioms SuFunctor.Adequacy.FinCTMC.offRate_diag
#print axioms SuFunctor.Adequacy.FinCTMC.offRate_of_ne
#print axioms SuFunctor.Adequacy.FinCTMC.exitRate_nonneg
#print axioms SuFunctor.Adequacy.FinCTMC.offRate_eq_zero_of_exitRate_eq_zero
#print axioms SuFunctor.Adequacy.jumpStep_nonneg
#print axioms SuFunctor.Adequacy.jumpStep_row_sum
#print axioms SuFunctor.Adequacy.FinCTMC.jumpChain_init
#print axioms SuFunctor.Adequacy.FinCTMC.jumpChain_step
#print axioms SuFunctor.Adequacy.FinCTMC.jumpChain_step_mul_exit
#print axioms SuFunctor.Adequacy.FinCTMC.absorbing_iff
#print axioms SuFunctor.Adequacy.FinCTMC.jumpLaw_mass
#print axioms SuFunctor.Adequacy.CtmcRows.rateAt_nonneg
#print axioms SuFunctor.Adequacy.CtmcRows.rateAt_diag
#print axioms SuFunctor.Adequacy.compileCtmc_rateRow
#print axioms SuFunctor.Adequacy.compileCtmc_initRow
#print axioms SuFunctor.Adequacy.compileCtmc_wf
#print axioms SuFunctor.Adequacy.compileCtmc_rateAt
#print axioms SuFunctor.Adequacy.jumpRows_outcome
#print axioms SuFunctor.Adequacy.jumpRows_initRow
#print axioms SuFunctor.Adequacy.jumpRows_wf
#print axioms SuFunctor.Adequacy.compile_jump_comm
#print axioms SuFunctor.Adequacy.ctmc_jump_adequacy
#print axioms SuFunctor.Adequacy.compileCtmc_diag_blind
#print axioms SuFunctor.Adequacy.FinCTMC.offRate_diag_blind
#print axioms SuFunctor.Adequacy.FinCTMC.jumpLaw_diag_blind
#print axioms SuFunctor.Adequacy.FinCTMC.jumpTrajPMF_eq
#print axioms SuFunctor.Adequacy.su_ctmc_jump_adequacy
#print axioms SuFunctor.Adequacy.su_ctmc_jump_jumpLaw_mem
#print axioms SuFunctor.Adequacy.su_ctmc_jump_bottom
#print axioms SuFunctor.Adequacy.FinCTMC.jumpLaw_ne_zero
#print axioms SuFunctor.Adequacy.su_ctmc_jump_slice
