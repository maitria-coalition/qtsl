import SuFunctor.Universe.CredalPoset

/-!
# Axiom receipts, Richardson re-pin tier

`#print axioms` receipts for the Richardson-class strictness pair: the
compile of the boundary-jump convex penalty is no Richardson body (the
lsc conjunct of `IsRichardsonBody` is not implied by convexity), and
the existential packaging of that witness, together with the landed
neighbors the pair leans on.
-/

open SuFunctor.Universe.CredalPoset

#print axioms SuFunctor.Universe.CredalPoset.not_isRichardsonBody_compile_f₇
#print axioms SuFunctor.Universe.CredalPoset.exists_penaltyConvex_compile_not_richardson
#print axioms SuFunctor.Universe.CredalPoset.penaltyConvex_f₇
#print axioms SuFunctor.Universe.CredalPoset.not_isClosed_compile_f₇
#print axioms SuFunctor.Universe.CredalPoset.IsRichardsonBody.isConvexCredalBody
