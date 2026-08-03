# The Lean reflection route

The third public checking path: the same sealed commit bytes the
certified checker consumes, loaded into Lean and accepted by the Lean
kernel as a theorem.

A Lake package (library `Reflection`), depending on the core `qtsl`
package for the wire model, the rule soundness lemmas, and the
admissible-rule seam. Build with `lake build`; the executables below
with `lake build geolog_read geolog_reflect`. The per-certificate
kernel receipt modules (`Reflection.Receipt*`) are outside the library
root on purpose — each one kernel-evaluates a whole acceptance run
(`decide`) and wants hardware sized for it (see `MEASUREMENTS.md`);
build them by name.

## Architecture

```
container bytes
  │  readGeologSealed        total decode, canonical spellings only,
  │                          refusal-shaped errors (Container/Body/
  │                          Cells/Codec — mirrors the reference
  │                          reader; 146-fixture differential)
  ▼
sealed commit ops
  │  certOfRows              object rows → wire-model certificate
  │                          (CertRows; pinned theory vocabulary)
  ▼
wire certificate
  │  elabWCert               the established elevation (well-formed
  │                          complexes, hypernet, proof tree)
  ▼
parsed certificate
  │  elabValid               runtime elaboration of a semantic
  │                          validity proof: each rule's side
  │                          conditions are decided and the
  │                          corresponding soundness lemma applied
  ▼
Accepted ⟨H, seq, goal, PLift (seq.semanticallyValid H)⟩
```

The acceptance theorem (`Accept.lean`):

```lean
theorem acceptBytesSealed_sound (bs : Bytes) (a : Accepted)
    (h : acceptBytesSealed bs = some a) :
    a.seq.semanticallyValid a.H
```

Its proof is one line — the accepted value carries the validity proof
constructed during elaboration, so no decode or reconstruction stage
is trusted: a defect anywhere below the soundness lemmas can lose
completeness, never soundness. Per-certificate kernel receipts
(`Receipt*.lean`, generated) check `acceptBytesSealedB bytes = true`
by `decide`, evaluating the entire route inside the kernel.

`elabPO` (in `Elab.lean`) is the stricter, purely compositional form
of the same idea: it constructs an inhabitant of the dependent
proof-object type. Context-carrying disjunction elimination has no
proof-object payload — validity proofs compose across that admissible
seam (`sound_orECtx`), proof objects cannot — so `elabValid` is the
route's production elaborator and `elabPO` documents the compositional
fragment.

## Executables

- `geolog_reflect` — sealed container files in, staged verdicts and
  timings out; `--against FILE.geolog FILE.bernfmt` compares the
  claims reconstructed by this route and by the binary wire parser
  (they must be identical values).
- `geolog_read` — structural dumps (plain + sealed readings) for the
  cross-implementation differential harness.
- `oracle_accept` — drives the rows-onward pipeline from rendered op
  dumps (test instrument).

## Trust notes

- The decoder and reconstruction stages carry no correctness theorems
  and need none for soundness (they appear in the acceptance theorem
  only through the value they produced). Their fidelity is checked
  differentially: byte-exact render agreement with the reference
  reader across the fixture corpus, and claim-value agreement with
  the binary wire path on real certificates.
- Everything on the kernel-evaluated path is structural or
  explicit-fuel recursion — no `partial`, no well-founded recursion
  (audited; see `scripts/geolog_wf_scan2.lean`).
- Measured behavior, including the deliberate scaling cliff:
  `MEASUREMENTS.md` beside this file.
- The accepted fragment is the first-order pinned-vocabulary rule set
  plus primitive-application **enclosure judgments** (`Cert/rootEnc`:
  the Maclaurin remainder-bound obligation, decided in exact rational
  arithmetic and carried to real-analytic validity by the
  mathlib-backed `QtslAux.Enclosure.encCheck_sound` —
  `Reflection.EncValid` / the `acceptBytesSealedAny` arm in
  `Reflection.Accept`). Other primitive applications remain out of
  fragment. The extended soundness statement is
  `acceptBytesSealedAny_sound`; the legacy proof-arm entry points are
  unchanged and byte-identical on proof-root certificates.
