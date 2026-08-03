# MAITRIA: The Book

Source of `https://maitria.org/book.pdf` and its sibling artefact
`https://maitria.org/book.tex` (the flattened single-file LaTeX source).
For agent consumption, the PDF has been constructed such that `pdftotext`
on it returns the original LaTeX source: bare `pdftotext book.pdf -`
yields the body text followed by the complete source, a byte-exact
page-range recipe is printed on the PDF's own source-appendix page, and
the same bytes ride as a PDF attachment (`pdfdetach -saveall book.pdf`).
The `book.tex` URL continues to resolve; the PDF simply no longer needs
a sidecar to be read whole.

The book is the manual for the MAITRIA bundle — **Geolog** (the modelling
substrate), **QTSL** (the Quantitative Temporal Specification Logic), and
**MTK** (the producer stack) — written for readers who know the Safeguarded
AI programme's decks and know category theory, CRDTs, or verification at
research depth.

## State: preview scaffold

Every chapter in the assembly is drafted; the table of contents is
normative. The maturity roster, by durable category (the per-chapter
statement the build keeps current is the preview notice in
`chapters.tex`, printed in the book's front matter):

- **Generated surfaces** — re-derived from the toolkit's own sources,
  never hand-written: the QTSL rule catalogue chapter
  (`chapters/qtsl-rule-catalogue.tex` and its companion preamble are
  emitted artefacts — provenance header inside; regenerate with the
  emitting tool, never hand-edit); the Lean-cone appendix (regenerated
  from the `lean/` trees at every build, strict mode); the Quick Start
  and tutorial transcripts (real runs the build itself regenerates);
  the Experiments chapter's tables (re-derived from receipt files in
  [`maitria-coalition/qtsl-experiments`](https://github.com/maitria-coalition/qtsl-experiments));
  and the Specification Language chapter's API sections (quoted
  verbatim from the toolkit's conformance corpus).
- **Working drafts** — content present, still moving with its measured
  sources: the Executive Summary (a first draft) and the Experiments
  and Markov-kernels chapters (tables and coverage dashboard re-derive
  from receipts and a measured census at each preview).
- **Full drafts** — everything else: the whole Geolog part (quick
  start, tutorial, reference manual, diagrams-as-data); the QTSL
  part's quick start, MTK production tutorial (listings run as
  printed), and prose chapters (semantic universe, hypernets,
  model-type catalogue, composition patterns, specification language,
  partial-completeness); and the MTK part (the fabrication-line worked
  example, whose construction listing runs as printed; the
  implementation pearls; the agents' cookbook).

## Layout

- `chapters.tex` — the assembly template (documentclass `book`); chapters
  ride `\input`. Edit here (and in `chapters/`), never in the built
  `book.tex`.
- `chapters/*.tex` — one file per chapter of the ToC; the two
  `qtsl-rule-catalogue*` files are generated (see above).
- `transcripts/*.toml`, `tools/transcripts.py`, `generated/transcripts/` —
  every command transcript and executable listing printed in the Quick
  Starts and the MTK tutorial is a **generated fragment**: the build runs
  the printed commands in sandboxes against the sibling tool checkouts
  and the chapters `\input` the results, so a transcript cannot silently
  go stale. Regeneration is cached, content-addressed on the spec plus
  its declared inputs (tool source trees, corpus artefacts, the committed
  listings under `listings/`); when nothing changed, nothing runs, and
  when a tool moved, the re-run's diff to the committed fragment is the
  review surface. Specs also re-verify the chapters' *unprinted* receipt
  claims (byte-identity against the published corpus, refusal exit codes,
  control runs) and fail the build when a load-bearing output no longer
  matches the prose (`prose-assert`). Absent tool trees are a warning,
  not an error — a lone clone of this repository still builds from the
  committed fragments. Force a re-run with
  `./build.sh --refresh-transcripts`.
- `generated/experiments-pin.txt` — provenance of the Experiments chapter
  content the committed artefacts were built from: the sibling
  `qtsl-experiments` checkout's commit and the *content hash* of its
  `chapter/` tree (a history rewrite that preserves content preserves the
  hash). The build refreshes it and warns when the content moved.
- `book.pdf`, `book.tex` — **built artefacts, committed** so they resolve
  at
  [`raw.githubusercontent.com/maitria-coalition/qtsl/refs/heads/main/book/book.pdf`](https://raw.githubusercontent.com/maitria-coalition/qtsl/refs/heads/main/book/book.pdf)
  and
  [`…/book/book.tex`](https://raw.githubusercontent.com/maitria-coalition/qtsl/refs/heads/main/book/book.tex).
  `book.tex` is the assembled single-file source (`latexpand` inlines the
  chapter `\input`s and the bibliography). Regenerate with `build.sh`;
  never hand-edit.
- `srclayer.tex`, `tools/srclayer-split.py`, `tools/srclayer-gate.py` —
  the source-carrying mechanism: `book.pdf` carries the assembled
  `book.tex` as an invisible fixed-pitch text layer on appended pages
  (extraction recipes printed on the PDF's source-appendix page) and as
  a PDF attachment. The splitter normalizes and chunks the payload and
  stages the layer's private fonts; the gate verifies, on every full
  build, that the printed recipe reproduces `book.tex` byte-exactly,
  that the attachment detaches byte-identically, and that bare
  `pdftotext` carries the source. `srclayer.tex`'s header comment is
  the design story.
- `build.sh` — the one verb, with two more behind it:
  - `./build.sh` builds. Transcripts regenerate first (cached, see
    above); intermediate state lives in `build/` (gitignored);
    `book.pdf` + `book.tex` install beside the sources and commit iff
    content changed (a no-change rebuild commits nothing). Requires a
    TeX Live with `latexmk` (LuaLaTeX — the catalogue's quoted sources
    carry mathematical Unicode), `latexpand`, Python ≥ 3.11, and
    `poppler-utils` (the source-layer gate; it skips with a note where
    poppler is absent). A "Missing character" glyph gate fails the
    build on dropped glyphs; the source-layer gate fails it when the
    PDF's embedded source stops matching `book.tex` byte-for-byte.
    Builds are byte-reproducible (`SOURCE_DATE_EPOCH`; verified by
    double build).
  - `./build.sh transcripts [--force] [--only SPEC]` runs just the
    transcript generator.
  - `./build.sh experiments <target>` re-derives an Experiments-chapter
    section's numbers through the reproduction spine's own make targets
    (`gymnasium`, `circuits`, `semicon`, `supermartingales`, `chapter`,
    and their subtargets) in the sibling `qtsl-experiments` checkout.
    Deliberately **not** part of the book build — re-running an
    experiment is a per-section choice, and the chapter's tables
    re-derive from the committed receipt files either way.
  - Build requirement: the Experiments chapter `\input`s its sections
    from a sibling checkout of
    [`maitria-coalition/qtsl-experiments`](https://github.com/maitria-coalition/qtsl-experiments)
    (cloned beside this repository; from a git worktree the build finds
    the primary checkout's sibling automatically, and
    `BOOK_TOOL_QTSL_EXPERIMENTS` overrides). The transcript generator
    resolves the other tool checkouts — `geolog-alpha`, `mtk` — the
    same way (`transcripts/tools.toml`).

## License

The book — this source and the built PDF — is licensed
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
(attribution: David "davidad" Dalrymple and the maitria coalition
contributors; see `LICENSE`). The MAITRIA **code** repositories are
licensed separately, under Apache-2.0 OR MIT.
