import QtslAux.QtslCompose.Presentation
import QtslAux.QtslCompose.AGCompose
import QtslAux.QtslCompose.AGComposeDiscrete
import QtslAux.QtslCompose.AGComposeMarks
import QtslAux.QtslCompose.AGComposeCarves
import QtslAux.QtslCompose.WireCertDischarge
import QtslAux.QtslCompose.SimTransport
import QtslAux.QtslCompose.SimTransportMeas
import QtslAux.QtslCompose.Flatten
import QtslAux.QtslCompose.FlattenMeas
import QtslAux.QtslCompose.AggReduce
import QtslAux.QtslCompose.LtiSampled
import QtslAux.QtslCompose.Coherence
import QtslAux.QtslCompose.StochCoherence
import QtslAux.QtslCompose.AGComposeGuarded
import QtslAux.QtslCompose.AGComposeMarksTier
import QtslAux.QtslCompose.AGComposeMarksStoch

/-! # QTSL composition cluster

Statements + proofs for the composition cluster of the QTSL rule page
(`metanotation/QTSL-rules.toml`): `QWireCompose` (n-ary acyclic assembly +
the per-profile tier split rendered first-class over the ratified System
presentation), `QWireCertDischarge` (the 𝒦⁰∞ membership-row discharge +
slack algebra), `QSimTransport` (behavioral pullback + the finite-kernel
instance over the QRel chain substrate), `QFlatten` (the product-kernel
flatten witness), `QAggReduce` (the P3 containment-evaluation core + the
bag-observable row warrants, γ-traced).

Module map:
- `QtslCompose/Presentation.lean` — System/profile/tier (the System doc §2
  pin: profile derived from field-family population, never a stored tag);
- `QtslCompose/AGCompose.lean` — the n-ary acyclic (S)-face theorems;
- `QtslCompose/AGComposeDiscrete.lean` — the B-row (discrete-kernel)
  assembly: B1/B2/B3 discharged end-to-end over
  `Kernel.traj` through the battery substrate — the first-failure device
  (K4) + per-component Ville (K1) for the n-ary union bound, the
  `∥ₖ`-linearity row for parallel, the `(1, λ, 1, 1)` cancellation at
  kernel level for discrete small-gain;
- `QtslCompose/WireCertDischarge.lean` — 𝒦⁰∞ class + polynomial discharge;
- `QtslCompose/SimTransport.lean` — CM rule 2, both strata;
- `QtslCompose/Flatten.lean` — structure-not-expressiveness, finite tier;
- `QtslCompose/FlattenMeas.lean` — the same witness pair at the
  measurable-kernel tier: `law_parallelComp` over
  `∥ₖ`/`Measure.prod`, projections consuming exactly the sibling's
  Markov property, addressability composed through `SimTransportMeas`;
- `QtslCompose/AggReduce.lean` — P3 + row warrants (coupling rows are NOT
  probabilistic couplings — the eRHL false-cognate fence, stated there);
- `QtslCompose/LtiSampled.lean` — the LTI × discrete sampled-data
  witness's presentation instance (heterogeneity + admissible tier as
  theorems; the empty instantaneous DAG under Moore wiring).
- `QtslCompose/Coherence.lean` — the coherence checklist:
  interchange (`QWireCompose` × `QSimTransport` middle-four exchange,
  behavioral + finite-kernel strata) and flatten-commutes-with-nesting
  (finite-kernel; presentation-stratum form prose-ledgered pending the
  `NestBind` sorts).
- `QtslCompose/StochCoherence.lean` — the coherence successor: the
  SDE/GSHS semantic faces at the measure/kernel tier (interchange +
  flatten over `ProbabilityTheory.Kernel`/`Measure`, plus one-step
  drift-certificate transport along kernel intertwinings).
-/
