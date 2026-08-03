# qtsl

**QTSL** — the **Quantitative Temporal Specification Logic**: a
specification language for stating quantitative safety and liveness
properties of dynamical and hybrid systems, whose proof obligations
compile down to certificate-checkable verification conditions
(Streett-automaton and tower-of-invariants conditions over polynomial
inequalities).

The design premise: a specification logic earns trust not by the
sophistication of its prover but by the smallness of its checker. QTSL
proofs are **certificates** — explicit data artefacts, carried as
ordinary object rows of a geolog theory rather than as a bespoke wire
format — and the checking surface is deliberately tiny: decision
procedures for ground relations (exact rational arithmetic, polynomial
canonical forms, certified positivity via Bernstein-basis bounds), with
soundness results machine-checked in Lean.

Three consumers check the same certificate rows: the **geolog engine**
(the production fast path, engineering-grade assurance), **`qtslab`** —
the QTSL assurance binary (read: *qtsl-lab*) — the certified end-to-end
checker (demonstrated route, assembling now), and the **Lean
reflection** route, which feeds the same bytes to Lean's kernel to
measure where kernel-grade checking meets machine scale.

**BL** — Bernstein Logic, the proof calculus for certified polynomial
bounds via the Bernstein basis — survives here as the **BL fragment of
QTSL**: the workhorse layer that discharges polynomial positivity and
inclusion obligations inside larger temporal arguments.

That fragment is also, today, exactly what the soundness results bind
to. A certificate's machine-checked core encodes the Bernstein Logic
part of its proof tree — sequents over the hypernet the certificate
itself declares, whose acceptance the machine-checked results tie to
validity under every admissible valuation of that hypernet. The theory
set under `theories/` encodes the rest of the QTSL vocabulary as
well — Systems, Specs, and the judgments connecting them, as a
machine-checked schema with a drift-alarmed battery — and selected
producer surfaces have shipped against that schema: the companion
`mtk` toolkit's catalogue APIs (TypeScript and Rust, one
implementation underneath) construct and emit `QSat` satisfaction
frames — a System paired with a Spec — quoted verbatim from the
toolkit's conformance corpus in the book's Specification Language
chapter, and the ground-provider crate here reads those rows when it
recomputes certificate side conditions. What has not caught up is the
mechanized assurance for the general judgment: the machine-checked
soundness results still bind the BL fragment, so no consumer yet
accepts a certificate concluding that a System satisfies a Spec on
mechanized-soundness grounds, and a certificate reaching beyond the
soundness-bound fragment is refused outright rather than silently
accepted — a completeness boundary, not a soundness gap, and it
closes by growing the mechanized coverage toward the emission that
now exists.

## What this repository will hold

This is the theory-as-data and checker-format half of the system (its
database substrate lives in the companion `geolog-alpha` repository —
QTSL's rules are object-level rows with respect to geolog's meta-schema,
not engine code):

- **the compile/project bridge** between certificate models and
  meta-schema object rows (untrusted producer tooling — a wrong bridge
  yields a certificate that fails checking, never a false verdict);
- **theory sources and listings** — the QTSL and BL-fragment theories
  as data;
- **the literate rule catalogue** (below) — the reference manual's
  source of truth;
- **the Lean soundness packages** — the machine-checked results that
  make the checker's smallness meaningful.

## What is here now

- `theories/` — the QTSL theory set as data: `Qtsl.geolog`, the
  omnibus certificate theory (subject and specification vocabulary,
  system formers, flavored cells, and the certificate sections and
  shape), extending `BernsteinLogic.geolog`, the Bernstein Logic
  proof tower — exactly the fragment the certified checker consumes —
  with the conditional-table sibling `CondWire.geolog`, registries
  classifying every side-condition relation, and `check.sh`, the
  drift-alarmed battery of committed goldens, chase fixtures, and
  schema mutants; see `theories/README.md`.
- `checkers/circuits`, `checkers/supermartingales` — the standalone
  Python checkers (exact arithmetic, zero producer imports) for the
  hardware-liveness and published-table campaigns.
- `book/` — the MAITRIA book source. `book/build.sh` produces the PDF
  and the flattened single-file TeX artefact; the experiments chapter
  reads generated tables from a sibling clone of `qtsl-experiments`.
- `lean/` — the Lean soundness packages: `qtsl` (the
  reference `Qtsl` package), `qtsl-aux`
  (`QtslAux`: the consuming lemmas behind the checkers
  above, sorry-free throughout), `optional-sampling`, and
  `double-cat`. Each package pins its own toolchain and mathlib
  revision; see `lean/README.md`.
- `hol/` — the HOL4 development: `checker` (the certified-checker
  chain) and `martingales` (the measure-theory / optional-stopping
  development); see `hol/README.md`.
- `catalogue/` — the rule catalogue's source of truth
  (`QTSL-rules.toml` + sibling rule files) and
  `catalogue/metanotation`, the typesetting tool (`qtsl-rules`,
  `qtsl-book`).
- `tools/lean-cone` (wrapper: `./lean-cone` at the repository root) —
  audit-surface emitter for the Lean packages: given target constants,
  prints their transitive signature cone, topologically sorted, as a
  single checkable file of theorem statements and definition content
  with proof content elided; see `tools/lean-cone/README.md`.
- `crates/qtsl-geolog-provider` — QTSL's value at geolog-alpha's
  ground-provider plugin seam: the exact-rational evaluators for the
  certificate side-condition relations (linear-combination replay, PSD
  certificate checks, syntactic form checks, certificate-kit
  recomputes), one `GroundProvider` the engine's binder adjudicates —
  untrusted producer-side tooling, never a trusted computing base.

Reproduction artefacts for the experiment tables (producers, fixtures,
receipts, and the tables themselves) live in the companion
`qtsl-experiments` repository.

Building: `cargo build --release` builds the catalogue typesetting
tool (`qtsl-rules`, `qtsl-book`); `cargo test --release` runs its
battery. The Lean and HOL4 developments build with their own
toolchains (see `lean/README.md`, `hol/README.md`).

A note on provenance: this system is being re-authored into public
form from a private workshop lineage. Where a source comments on a
design document that lives outside this repository (the upstream
correspondence spec, upstream model ledgers), the citation names its
object self-containedly; the companion `qtsl-experiments` repository
carries the producers, certificates, and receipts behind the
experiment tables.

## Status

The mechanized boundary, exactly:

- **Machine-checked now** — the Lean soundness packages bind the BL
  fragment: acceptance of a certificate's Bernstein-Logic sequent core
  implies validity under every admissible valuation of its declared
  hypernet. The `theories/` schema for the full certificate vocabulary
  (Systems, Specs, and the satisfaction judgments) is itself
  machine-checked data, chase-tested and mutant-fenced by the battery
  beside it.
- **Shipped, not yet soundness-bound** — the `mtk` catalogue surfaces
  emit `QSat` System/Spec satisfaction frames against that schema, and
  the provider crate here recomputes over those rows; a certificate
  whose conclusion reaches beyond the BL fragment is refused by the
  checking surface, never silently accepted.
- **Not yet** — mechanized soundness for the general
  System-models-Spec judgment; that closes only by new machine-checked
  results growing toward the vocabulary the schema and the producers
  already carry.

Formats inside the soundness-bound fragment are the settled ones; the
boundary itself moves only by new mechanized coverage.
