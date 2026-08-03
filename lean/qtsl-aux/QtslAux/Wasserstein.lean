import QtslAux.Wasserstein.Coupling
import QtslAux.Wasserstein.Glue
import QtslAux.Wasserstein.Space
import QtslAux.Wasserstein.Complete

/-! # The Wasserstein-2 space

This module gathers the Wasserstein-2 development:

* `QtslAux.Wasserstein.Coupling`: couplings, the quadratic transport cost `cost2`, the
  extended distance `W2edist`, second moments, and identity of indiscernibles;
* `QtslAux.Wasserstein.Glue`: the gluing construction and the triangle inequality for
  `W2edist`;
* `QtslAux.Wasserstein.Space`: the space `P2 X` of probability measures with finite
  second moment, as a metric space;
* `QtslAux.Wasserstein.Complete`: completeness of `P2 X` and the closed-ball fixed-point
  principle instantiated in it.
-/

