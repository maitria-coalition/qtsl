# circuits checker — circuit-manifest recurrence certificates

`ck_manifest.py` is the standalone checker for hardware-liveness
certificates: piecewise-affine rational ranking functions over a cell
partition of a circuit's branch structure, consumed by the
machine-checked recurrence lemma in
`../../lean/qtsl-aux/QtslAux/StreettDemonic.lean`.

Standalone by construction: it imports no producer code and rebuilds
every obligation from the certificate bytes and the declared step
system, in exact rational arithmetic (`fractions.Fraction`).

## run

```
python3 ck_manifest.py <certificate.cbor>
```

Dependencies: Python ≥ 3.10 and `cbor2` (`pip install cbor2`). Exit 0
on ACCEPT, nonzero on REFUSE; the verdict line names the refusing
check.

Certificates, producers, mutant batteries, and the benchmark suite this
checker was measured against live in the companion
`qtsl-experiments` repository (its `circuits/` suite).
