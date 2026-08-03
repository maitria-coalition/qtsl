# su-functor-legacy

The retired calculus-side semantic tier of the `su-functor`
development, kept as a buildable archive.

The modules here construct semantic functors from the proof calculus
into per-element constraints on finitely supported subprobability mass
functions, and prove soundness, threshold polarity, and the
route-agreement theorems against that target. They are superseded as
the semantics of record by the sheaf-fibred construction in
`../su-functor` (the `SuFunctor.Universe`, `SuFunctor.Plain`, and
`SuFunctor.Site` modules).

New results must not import this package. The dependency direction is
one-way: this package imports `su-functor`; the live package cannot
import this one, so a stale reference in live code fails the live
build and calls for restatement over the successor carrier.

Build:

```
cd lean/su-functor-legacy
lake build
```
