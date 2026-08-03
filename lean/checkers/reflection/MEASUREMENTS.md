# Reflection route: measured behavior (2026-07-21)

The route exists to demonstrate two things with numbers rather than
assertions: it **works** — real sealed containers, produced by the
production stack, are accepted end-to-end, and the kernel itself will
evaluate the whole pipeline to a theorem — and it **scales terribly**,
which is the third checking path's expected and now measured shape.
A null in the large-instance rows below is a finding, not a gap.

Host: 251 GB / 16-thread x86_64 build box. All certificates are
production `.geolog` sealed containers; "compiled" = the
`geolog_reflect` executable (Lean-compiled native code); "kernel" =
`decide`-receipt modules evaluating `acceptBytesSealedB bytes = true`
inside the Lean kernel.

## Compiled route (staged timings, ms)

| certificate | container bytes | read | rows→wire | elevation | validity | end-to-end | verdict |
|---|---|---|---|---|---|---|---|
| ctmc_sis_gen | 919 | 2.6 | 0.14 | 0.04 | 0.24 | 3.0 | ACCEPT |
| micro2_stable | 2 184 | 25.7 | 0.3 | 0.1 | 1.5 | 27.6 | ACCEPT |
| cartpole_dp_core_decrease | 9 336 | 9 578 | 34 | 4.4 | 424 | 10 041 | ACCEPT |
| dp_composite_syzygy | 17 591 | 95 385 | 417 | 16 | 740 | 97 082 | ACCEPT |
| dp_composite_smallgain | 46 235 | — | — | — | — | **null: >2 400 000** | (timeout) |

The reader dominates everything past the first two rows and grows at
≈3.6 power in container bytes over the measured points (list-append
CBOR decoding plus quadratic seam-assembly in the purely-functional
reader — chosen for kernel evaluability, not speed). At that exponent
dp_composite_smallgain projects to ≈48 min compiled; it was cut off at
40. An index-structured reader would take these to seconds — worth
doing only if this route ever needed to be more than a demonstration,
which is precisely what the trichotomy does not claim.

## Kernel route (`decide`, whole pipeline in the kernel)

| certificate | container bytes | kernel wall | kernel maxrss | verdict |
|---|---|---|---|---|
| ctmc_sis_gen | 919 | **965 s** | **233 GB** | theorem (twice: two independent runs) |
| micro2_stable | 2 184 | null: killed in flight | >projected host RAM | theorem on run 1 (receipt build completed); timing unmeasured |

The one fully-measured kernel point is the headline: a certificate the
compiled route accepts in **3 ms** costs the kernel **16 minutes and
233 GB** — a ≈3×10⁵ slowdown, with memory the binding axis (the
kernel's reduction terms, not the certificate, occupy the space). The
micro2 receipt module was kernel-checked successfully in a first
combined run (~≤20 min alongside ctmc), but its instrumented rerun was
killed deliberately when ctmc's maxrss showed the next size up would
contend for the whole host. Nothing larger was attempted; the curve
speaks.

## Fidelity evidence (the untrusted stages)

- 146-fixture byte-exact render differential against the reference
  reader (positives and refusal corpus), including 10 sealed-specific
  cases.
- Claim-value agreement (`--against`, decidable equality on the
  reconstructed sequent and goal) between this route and the binary
  wire parser on 4 production certificates.
- Structural-recursion audit: `WF-compiled (0): []` across every
  definition on the kernel path (`scripts/geolog_wf_scan2.lean`).

## The enclosure arm (2026-07-29, PEnclosure fragment extension)

Host for this section: the barn (Xeon W-2145, 8c/16t, 256 GB) — a
*different, slower, contended* box than the section above; numbers are
package receipts, not ladder rows.

| certificate | container bytes | compiled end-to-end | kernel wall | kernel maxrss | verdict |
|---|---|---|---|---|---|
| enclosure_v1_golden_cos6 | 603 | 0.44 ms | 7.34 s | 3.2 GB | theorem |

The kernel figure includes the module's whole import-cone load; the
same command on the pre-extension build (where these bytes REFUSED at
scan) took 4.66 s, so the marginal kernel cost of full acceptance is
≈2.7 s. Contrast the proof-cert kernel headline above (919 B: 965 s,
233 GB): the enclosure obligation carries no hypernet, no proof tree,
and only degree-bounded exact-rational arithmetic, so it is the first
certificate class for which the kernel route is genuinely cheap.

Tactic note: enclosure receipts decide with `decide +kernel`. Plain
`decide`'s elaborator-side reduction sticks on mathlib-irreducible
instances reached by the enclosure arithmetic (the same reason every
`QtslAux.Enclosure` example is kernel-decided); the committed
proof-cert receipt modules (core-only arithmetic) keep plain `decide`
unchanged.

Mutant battery (route-level, both vehicles — sealed-container byte
mutants and rendered-op-dump rows mutants through `oracle_accept`):
cap tightened one integer below the exact tail bound (1/4410 → 1/4411)
REFUSES at the validity stage on both vehicles; func=3 refuses at
reconstruction (`enc_func_roster`); r = n+2 and a degree lie refuse at
the validity stage; a coherently *looser* true cap (1/4409) ACCEPTS —
the claim-swap reach boundary, same as the fast-path lane documents;
a certificate carrying both `root` and `rootEnc` refuses (P-ROOT).
