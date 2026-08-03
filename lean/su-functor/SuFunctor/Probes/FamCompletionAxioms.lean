import SuFunctor.StateSpace.FamCompletion

/-!
# Axiom receipts, completed state-space tier

The free countable coproduct completion of the ω-semialgebraic
category: the census (finite limits, all countable coproducts,
disjointness, universality, strict initial, not balanced), the bag
space `∐ₙ Symⁿ(ℝ)` as a first-class object with its lcsc realization,
the dimension-tagged exact fragment, and the comparison with the
concrete tagged unions.
-/

section FamCompletionReceipts

open SuFunctor.StateSpace SuFunctor.StateSpace.FamObj CategoryTheory
  CategoryTheory.Limits

/-- Witness: the completion has all finite limits, by instance search. -/
theorem famFiniteLimitsWitness : HasFiniteLimits FamOmegaSA :=
  inferInstance

/-- Witness: the completion has all countable coproducts, by instance
search — including families of unbounded ambient dimension. -/
theorem famCountableCoproductsWitness : HasCountableCoproducts FamOmegaSA :=
  inferInstance

/-- Witness: the initial object is strict, by instance search. -/
theorem famStrictInitialWitness : HasStrictInitialObjects FamOmegaSA :=
  inferInstance

/-- Witness: countable coproducts are disjoint, by instance search. -/
theorem famDisjointWitness (F : ℕ → FamOmegaSA) : CoproductDisjoint F :=
  inferInstance

#print axioms SuFunctor.StateSpace.FamObj.famCofanIsColimit
#print axioms SuFunctor.StateSpace.FamObj.famDescEquiv
#print axioms SuFunctor.StateSpace.FamObj.famComponentsIsColimit
#print axioms SuFunctor.StateSpace.FamObj.famIsIso_reindex_bijective
#print axioms SuFunctor.StateSpace.FamObj.famInjPullbackIsLimit
#print axioms SuFunctor.StateSpace.FamObj.famCoproductDisjoint
#print axioms SuFunctor.StateSpace.FamObj.famSectorIsPullback
#print axioms SuFunctor.StateSpace.FamObj.famSectorCofanIsColimit
#print axioms SuFunctor.StateSpace.FamObj.famIsInitial_of_hom_to_initial
#print axioms SuFunctor.StateSpace.FamObj.ySing_not_initial
#print axioms SuFunctor.StateSpace.FamObj.famProdFanIsLimit
#print axioms SuFunctor.StateSpace.FamObj.famEqForkIsLimit
#print axioms famFiniteLimitsWitness
#print axioms famCountableCoproductsWitness
#print axioms famStrictInitialWitness
#print axioms famDisjointWitness
#print axioms SuFunctor.StateSpace.famOmegaSA_not_balanced
#print axioms SuFunctor.StateSpace.ySing_emptyObj_not_initial
#print axioms SuFunctor.StateSpace.countable_famPieceAlphabet
#print axioms SuFunctor.StateSpace.mem_sortedCone_iff_monotone
#print axioms SuFunctor.StateSpace.sortedCone_isLocallyClosed
#print axioms SuFunctor.StateSpace.bagIsColimit
#print axioms SuFunctor.StateSpace.bagDesc
#print axioms SuFunctor.StateSpace.bagSpace_locallyCompactSpace
#print axioms SuFunctor.StateSpace.famSpace_locallyCompactSpace
#print axioms SuFunctor.StateSpace.sigma_locallyCompactSpace
#print axioms SuFunctor.StateSpace.famCmpHomEquiv
#print axioms SuFunctor.StateSpace.famCmp_not_isIso

end FamCompletionReceipts
