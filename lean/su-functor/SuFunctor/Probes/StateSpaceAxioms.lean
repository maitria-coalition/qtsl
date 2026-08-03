import SuFunctor.StateSpace.Limits
import SuFunctor.StateSpace.CountableCoproducts
import SuFunctor.StateSpace.Citizens
import SuFunctor.StateSpace.Adjudication
/-!
# Axiom receipts, ω-semialgebraic state-space tier

The category of ω-semialgebraic spaces: carving closure, composition
closure, the finite-limit and countable-coproduct census, the citizen
lcsc receipts, and the adjudication counterexamples (the countability
witness, the `√` morphism-definition pair, the balance refutation).
-/

section StateSpaceReceipts

open SuFunctor.StateSpace CategoryTheory.Limits

/-- Witness: the ω-semialgebraic category has all finite limits, by
instance search. -/
theorem stateSpaceFiniteLimitsWitness :
    HasFiniteLimits SuFunctor.StateSpace.OmegaSA :=
  inferInstance

/-- Witness: the carving alphabet of the class is countable (the
exact-fragment receipt), by instance search. -/
theorem stateSpacePieceDataCountableWitness (n : ℕ) :
    Countable (SuFunctor.StateSpace.PolyCond n) :=
  inferInstance

#print axioms SuFunctor.StateSpace.IsOmegaSA.iUnion
#print axioms SuFunctor.StateSpace.IsOmegaSA.inter
#print axioms SuFunctor.StateSpace.IsOmegaSA.compl_basic
#print axioms SuFunctor.StateSpace.isLocallyClosed_basicSet
#print axioms SuFunctor.StateSpace.basicSet_subst
#print axioms SuFunctor.StateSpace.countable_pieceData
#print axioms SuFunctor.StateSpace.IsPiecewisePolyOn.comp
#print axioms SuFunctor.StateSpace.IsOmegaSA.graphSet
#print axioms SuFunctor.StateSpace.IsOmegaSA.eqLocus
#print axioms SuFunctor.StateSpace.prodFanIsLimit
#print axioms SuFunctor.StateSpace.eqForkIsLimit
#print axioms SuFunctor.StateSpace.coprodIsColimit
#print axioms SuFunctor.StateSpace.hasCoproduct_of_commonAmbient
#print axioms SuFunctor.StateSpace.natSet_isOmegaSA
#print axioms SuFunctor.StateSpace.natSet_isClosed
#print axioms SuFunctor.StateSpace.natSet_not_finiteSA
#print axioms SuFunctor.StateSpace.counterSet_isOmegaSA
#print axioms SuFunctor.StateSpace.counterSet_isCompact
#print axioms SuFunctor.StateSpace.counterHomeo
#print axioms SuFunctor.StateSpace.locallyCompactSpace_of_isLocallyClosed
#print axioms SuFunctor.StateSpace.isLocallyClosed_prodObj
#print axioms SuFunctor.StateSpace.graphSet_sqrtRaw_eq_basic
#print axioms SuFunctor.StateSpace.isOmegaSA_graphSet_sqrtRaw
#print axioms SuFunctor.StateSpace.sqrt_not_piecewisePoly
#print axioms SuFunctor.StateSpace.mono_cubeHom
#print axioms SuFunctor.StateSpace.epi_cubeHom
#print axioms SuFunctor.StateSpace.not_isIso_cubeHom
#print axioms SuFunctor.StateSpace.omegaSA_not_balanced
#print axioms stateSpaceFiniteLimitsWitness
#print axioms stateSpacePieceDataCountableWitness

end StateSpaceReceipts
