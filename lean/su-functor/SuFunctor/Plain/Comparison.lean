import SuFunctor.Plain.Battery
import DoubleCat.Opfibration
import DoubleCat.Virtual.OfPseudo

/-! # The plain total against the virtual route

How the plain construction of `SuFunctor.Plain.SpecFunctor` relates to
the virtual machinery of `DoubleCat.Virtual`:

* **The plain construction subsumes a virtual presentation.**  Every
  pseudo double category has an underlying virtual double category
  (`DoubleCat.Virtual.OfPseudo`), so the total of the spec-class functor
  carries virtual-double-category *data* by restriction — stated below.
  In the other direction, a span-valued lax double functor restricts to
  a span-valued virtual indexing (`DoubleCat.Virtual.GrothendieckRestrict`,
  the Cruttwell–Shulman correspondence), and the two totals agree
  stratum by stratum; that generic bridge is fully proven —
  `restrictVirtual`'s preservation of substitution, once its one open
  coherence leg, is closed in `DoubleCat.Virtual.GrothendieckRestrict`.
  This module still does not consume it: every statement here is made
  directly on the plain side.

* **The projection's variance is the positive half.**  The projection of
  the plain total is a *discrete double opfibration*
  (`specProj_discreteOpfibration` below, an instance of the generic
  `DoubleCat.Opfibration` fact): tight arrows and cells lift uniquely
  along the indexing's own actions — the split opcleavage is the
  canonical-lift data, matching the chapter's reading of the projection.
  The corresponding *cartesian* (negative) half — restriction of spec
  classes against a wiring, right adjoint to the pushforward on the
  inclusion-ordered fibres — is not constructed here; in the class
  fibres the candidate cartesian transport is preimage, and its lifting
  properties are a stated successor, not consumed by anything in this
  package.

* **Where virtuality remains load-bearing.**  Nothing in this package
  removes the virtual presentation of the *rule calculus*
  (`SuFunctor.Virtual`): multi-ary entailment cells have no loose
  composites to ride, by design.  The split this module documents is:
  syntax virtual, semantics plain — the two meet exactly where the
  Cruttwell–Shulman restriction sends the plain indexing into the
  virtual regime.
-/

namespace SuFunctor

namespace Plain

open CategoryTheory

universe u

variable {El : Type u}

/-- The plain total carries virtual-double-category data by restriction:
the underlying virtual double category of a pseudo double category,
instantiated at the spec-class total.  (Data only; the generic
lawfulness of `ofPseudo` for non-thin carriers is the fold-coherence
theorem, which nothing here consumes.) -/
noncomputable example : VirtualDoubleCategoryStruct (SpecTotal El) :=
  VirtualDoubleCategoryStruct.ofPseudo

/-- **The projection of the plain spec-class total is a discrete double
opfibration**: unique tight and cell lifts along the spec-class
indexing's own actions.  This is the machine form of "the variance is
forced, and it is the covariant (positive) half": pushforward of spec
classes along wirings is opcartesian structure. -/
theorem specProj_discreteOpfibration (El : Type u) :
    IsDiscreteDoubleOpfibration (SpanValued.proj (specFunctor El)) :=
  SpanValued.proj_isDiscreteOpfibration (specFunctor El)

end Plain

end SuFunctor
