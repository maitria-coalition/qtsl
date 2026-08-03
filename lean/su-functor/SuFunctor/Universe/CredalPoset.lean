import SuFunctor.Universe.CredalPoset.Defs
import SuFunctor.Universe.CredalPoset.Inclusions
import SuFunctor.Universe.CredalPoset.Witnesses
import SuFunctor.Universe.CredalPoset.Adjudication
import SuFunctor.Universe.CredalPoset.Previsions
import SuFunctor.Universe.CredalPoset.Parabola

/-! # The credal-body poset, assembled

The umbrella of the `CredalPoset` development: importing every leg forces
the whole development into one environment, and this module states the
facts that consume more than one leg.  The resulting Hasse diagram of
strict inclusions, exact for every carrier with at least two outcomes:

```
                credal bodies                 (closed radial; the lsc universe)
                     │
             convex credal bodies             (the outgoing convexity axiom)
              ┌──────┴────────────┐
        Richardson bodies   ultracontributions  = prevision bodies
        (convex lsc penalties)   ┌──┴─────────────┐
              │             MWER bodies      C^↓ bodies
         credal sets     (= homogeneous
      (radially embedded)  ultradistributions)
```

Edges downward are strict inclusions; every unordered pair is
incomparable, each direction refuted by an explicit rational witness on
the two-outcome carrier.  The individual memberships and refutations
live in `Witnesses`/`Parabola`; the general inclusion theorems in
`Defs`/`Inclusions`/`Previsions`; the penalty-convexity adjudication in
`Adjudication`.
-/

namespace SuFunctor.Universe.CredalPoset

open scoped ENNReal

/-! ## The house-includes-all theorem -/

/-- **Every named subclass is contained in the credal bodies.**  The six
classes of the development — convex credal bodies, Richardson bodies,
ultracontributions (equivalently prevision bodies), `C^↓` bodies, MWER
bodies, and radially embedded credal sets — all live inside the house
class.  (Each conjunct is the composite of the development's inclusion
edges; none of the reverse inclusions holds, by the witness zoo.) -/
theorem house_includes_all {V : Type*} [Fintype V] [Nonempty V]
    (S : Set (BelState V)) :
    (IsConvexCredalBody S → IsCredalBody S) ∧
    (IsRichardsonBody S → IsCredalBody S) ∧
    (IsUltra S → IsCredalBody S) ∧
    (IsMVS S → IsCredalBody S) ∧
    (IsHL S → IsCredalBody S) ∧
    (IsCozman S → IsCredalBody S) :=
  ⟨fun h => h.isCredalBody, fun h => h.isCredalBody, fun h => h.isCredalBody,
    fun h => h.isCredalBody, fun h => h.isCredalBody, fun h => h.isCredalBody⟩

/-- Prevision bodies are credal bodies (the seventh conjunct, through the
`Previsions` identification). -/
theorem IsPrevisionBody.isCredalBody {V : Type*} [Fintype V]
    {S : Set (BelState V)} (h : IsPrevisionBody S) : IsCredalBody S :=
  h.isUltra.isCredalBody

/-! ## Cross-leg cells of the witness matrix -/

/-- The ray segment is a Richardson body: it is a radially embedded
credal set (`Witnesses.isCozman_segBody`), and credal sets compile from
wall penalties of closed convex sets (`Inclusions.IsCozman.isRichardsonBody`). -/
theorem isRichardsonBody_segBody : IsRichardsonBody segBody :=
  isCozman_segBody.isRichardsonBody

theorem isConvexCredalBody_segBody : IsConvexCredalBody segBody :=
  isRichardsonBody_segBody.isConvexCredalBody

/-! ## The strict edges and incomparabilities that consume two legs -/

/-- Richardson bodies are not all ultracontributions (with
`Witnesses.ka_not_subset_r`: the pair {R, KA} is incomparable). -/
theorem r_not_subset_ka :
    ∃ S : Set (BelState (Fin 2)), IsRichardsonBody S ∧ ¬ IsUltra S :=
  ⟨segBody, isRichardsonBody_segBody, not_isUltra_segBody⟩

/-- {R, HL} incomparable, this direction (the other is
`Witnesses.hl_not_subset_r`). -/
theorem r_not_subset_hl :
    ∃ S : Set (BelState (Fin 2)), IsRichardsonBody S ∧ ¬ IsHL S :=
  ⟨segBody, isRichardsonBody_segBody, not_isHL_segBody⟩

/-- {R, MVS} incomparable, this direction (the other is
`Witnesses.mvs_not_subset_r`). -/
theorem r_not_subset_mvs :
    ∃ S : Set (BelState (Fin 2)), IsRichardsonBody S ∧ ¬ IsMVS S :=
  ⟨segBody, isRichardsonBody_segBody, not_isMVS_segBody⟩

/-- The convexity edge is strict on the ultracontribution side too:
a convex credal body that is not pointwise-down-closed (with
`Inclusions.IsUltra.isConvexCredalBody` this makes KA ⊊ CV). -/
theorem cv_strict_ka :
    ∃ S : Set (BelState (Fin 2)), IsConvexCredalBody S ∧ ¬ IsUltra S :=
  ⟨segBody, isConvexCredalBody_segBody, not_isUltra_segBody⟩

/-- MVS ⊊ KA: an ultracontribution that is not finitely generated —
the parabola body, whose extreme points are an infinite arc. -/
theorem ka_strict_mvs :
    ∃ S : Set (BelState (Fin 2)), IsUltra S ∧ ¬ IsMVS S :=
  ⟨parabolaBody, isUltra_parabolaBody, not_isMVS_parabolaBody⟩

/-- {HL, MVS} incomparable, this direction (the other is
`Witnesses.mvs_not_subset_hl`). -/
theorem hl_not_subset_mvs :
    ∃ S : Set (BelState (Fin 2)), IsHL S ∧ ¬ IsMVS S :=
  ⟨parabolaBody, isHL_parabolaBody, not_isMVS_parabolaBody⟩

end SuFunctor.Universe.CredalPoset
