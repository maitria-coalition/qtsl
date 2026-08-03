import SuFunctorLegacy.Source
import SuFunctorLegacy.Functor
import SuFunctorLegacy.Refute
import SuFunctorLegacy.Squares
import SuFunctorLegacy.Bridge
import SuFunctorLegacy.Threshold
import SuFunctorLegacy.ThresholdRefute
import SuFunctorLegacy.VirtualFunctor
import SuFunctorLegacy.Transpose

/-! # The retired calculus-side semantic tier (archive)

This package archives the first machine-checked semantic tier of the
`su-functor` development: semantic functors from the proof calculus
into the thin double category `Crd` of per-element constraints on
finitely supported subprobability mass functions (`SubPMF`), together
with the results proven against that target.

It is **retired, not deleted**: everything here still builds (against
the live `su-functor` package, whose syntax-side modules —
`SuFunctor.Judgment`, `SuFunctor.Target`, `SuFunctor.Virtual`,
`SuFunctor.VirtualComparison` — it continues to consume), the
regression pins remain checkable, and the refutation countermodels
remain on record.  The tier is superseded as the semantics of record
by the sheaf-fibred construction in the live package: the locally
closed Fell-hyperspace universe (`SuFunctor.Universe`), the plain
spec-class decoration functor (`SuFunctor.Plain.SpecFunctor`), and the
site-dimensional functor (`SuFunctor.Site.SiteFunctor`).

The dependency direction is one-way by design: the live package does
not (and cannot) import this one, so any reference to a retired module
from live code fails the live build — a result that still leans on
this tier is thereby called out for restatement over the successor
carrier.

Module map (retired tier):

* `SuFunctorLegacy.Source` — the thin formal-conjunction presentation
  of the derivation calculus (`BLD`, `JDeriv`).
* `SuFunctorLegacy.Functor` — the semantic double functor
  (`semFunctor`), its pseudo-ness, and the composed soundness
  statement (`semFunctor_sound`).
* `SuFunctorLegacy.Refute` — regression pins for the retired
  kind-table composition.
* `SuFunctorLegacy.Squares` — the per-rule square families at the
  per-element stratum.
* `SuFunctorLegacy.Bridge` — the graded reading, the quantifier
  collapse, and the batch soundness lifts (`gradedAnchor`,
  `gradedSound_ofProof`).
* `SuFunctorLegacy.Threshold` — threshold polarity over `SubPMF`:
  safety walls, liveness tilts, the full-mass slice, mixtures.
* `SuFunctorLegacy.ThresholdRefute` — the polarity pins and the
  three-outcome reach-avoid exhibit.
* `SuFunctorLegacy.VirtualFunctor` — the semantic functor of the
  virtual presentation (`Deriv.sem`).
* `SuFunctorLegacy.Transpose` — the route agreement
  (`transpose_eq_semFunctor`), conservativity
  (`unit_fullyFaithful`), and the calculus dictionary
  (`listDeriv_iff_jderiv`).
-/
