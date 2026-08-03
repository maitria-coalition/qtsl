# HOL4 developments

Two HOL4 developments back the QTSL certification story: the certificate-checker
soundness chain (`checker/`), and a measure-theoretic development of stopping
times, optional stopping, and martingale convergence (`martingales/`).

## checker/ — the certificate-checker soundness chain

The end-to-end certified checker is a demonstrated route, assembling now: a
predecessor checker's full chain — from a HOL4 acceptance predicate, through
CakeML compilation, down to a machine-code theorem against the ASL-derived
(official Arm specification) ARM8 model — is proven and re-runs cheaply, and
the theories here carry the current checker along the same route.

The development, bottom up:

- **Numeric foundations** — `qtsl_dyadicScript` (dyadic floats, exact extended
  rationals), `qtsl_qarithScript` (exact-rational polynomials and
  Bernstein coefficients), `qtsl_catalogueScript` (the rule-catalogue check
  functions), `qtsl_enclosureScript` (the remainder-bound rule, including its
  meaning theorem against the distribution's transcendental functions). These
  are side-by-side ports of the Lean development's corresponding modules.
- **The flat chain** — `qtsl_certScript` defines the first-order certificate
  datatype, the binary (v0) wire parser, and the reference checker
  (`checkPf`) that re-checks every rule side condition. The staged CakeML
  program chain (`qtslCertProgScript` → `qtslCertFullProgScript` →
  `qtslCertWPSpecScript` → `qtslCertWholeProgScript`) carries it to a
  whole-program semantics theorem; `qtslToyProgScript` is the shared
  translated foundation with a receipt-table main.
- **The performance chain** — `qtsl_certPerfScript` proves replacement
  representations (flat string input, offset-indexed tables, a fused fold)
  EQUAL to the spec functions, so the downstream theorem statements are
  unchanged; `qtslCertPerf*Script` re-run the program chain on the fused
  implementation. `qtsl_certShardScript` adds interval-sharded checking whose
  accepted shards compose to the whole-corpus run.
- **The relational (succinct) chain** — over the succinct certificate
  container: `qtsl_colsScript` (column relations and the frozen accessor
  kit), `qtsl_wfScript` (well-formedness and the per-node refinement
  relation), `qtsl_decodeSpecScript` (the functional spec of the encoded
  bytes) with `qtsl_decodeOracleScript` (byte-exact oracle runs against the
  untrusted reference decoder), `qtsl_rcScript` (the range-coder decode
  kernel), `qtsl_colreadScript` (the wire reader and verdict), six per-family
  check theories (`qtsl_fam_*Script`), and `qtsl_joinsScript` — the
  composition theorem `checkJoins_eq_checkPf` connecting the relational
  checker to the reference walk. `qtslCertRel*Script` carry this checker
  through the program chain.
- **The geolog tier** — the checker's input is a geolog container natively:
  `geolog/` holds BLAKE3 in HOL (`blake3Script`), the container reader
  (`geolog_readScript`), the hash-chain binding layer (`geolog_bindScript`),
  and a proven decode-totality statement (`geolog_o2Script`); at the root,
  `geolog_certScript` transcodes sealed proof-artefact rows to the relational
  checker's columns, and `geolog_verdictScript` composes the whole pipeline
  into a four-way verdict with its soundness theorem. Demo instances and
  mutant batteries (`geolog_certDemoScript`, `geolog_verdictDemoScript`,
  `qtsl_wfScript`'s demo section) witness acceptance and named refusals at
  value level; `geolog/fixtures/` plus the differential drivers and
  `run-differential*.sh` scripts check the reader byte-for-byte against
  committed oracle outputs from the reference implementation.
- **Compilation** — `compilation/` holds the in-logic ARM8 compile theories
  and the emitted `.S` artefacts; `compilation/proofsARM8/` composes program
  semantics, compiler correctness, and the compile theorems into end-to-end
  machine-code theorems (`machine_code_sound`, and verdict theorems binding
  the printed string to the checker's acceptance).
- **Side developments** — `imprec/` (imprecise-certificate soundness at
  finite state and horizon, plus staged goals type-checked against the
  measure-theory vocabulary), `temporal/` (LTL rewrite rules proved as
  denotation equalities over omega-words).

Two theories are deliberately UNVERIFIED diagnostics, never part of the
assurance chain: `qtslCertDiagScript` (per-stage parse diagnosis) and
`qtsl_decodeOracleScript` (byte-exact decoder oracle).

### Building

Requires HOL4 (Trindemossen-2) and, for the root `qtsl_*` theories (which
ancestor CakeML's `mlstring`) and the translation/CF/compile targets, a
CakeML checkout with `CAKEMLDIR` set. The `geolog/`, `imprec/` and
`temporal/` subdirectories build against a plain HOL4 install (`Holmake` in
each); `holshim/misc` supplies a core-heap `preamble` stand-in for selective
no-CakeML builds. The full program/compile chain is
resource-intensive (tens of GB of RAM for the translator and whole-program
evaluation stages; the staged script layout exists exactly so each expensive
stage banks its theory to disk).

## martingales/ — stopping times and martingale convergence

A development over HOL4's `martingaleTheory` (set-integral formulation),
which carries filtrations and martingales but no stopping-time vocabulary:

- `qtsl_stopScript` — stopping times, stopped processes, finite-horizon
  optional stopping, and bounded optional stopping at an everywhere-finite
  stopping time.
- `qtsl_upxScript` — capped hitting times, the crossing-time ladder,
  upcrossing counts, two-time optional sampling for submartingales, Doob's
  upcrossing inequality, and almost-sure martingale convergence.

Builds against a plain HOL4 install: `Holmake` in `martingales/`.
