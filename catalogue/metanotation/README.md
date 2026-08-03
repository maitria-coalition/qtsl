# metanotation — the rules diff-typesetter + the literate rule book

Two tools share this crate and the same hand-authored rules source:
`qtsl-rules` (the two-column diff pages, below) and `qtsl-book` (the literate
rule catalogue — see "the book" at the end).

Typesets the Bernstein Logic derivation rules two ways side by side —
David "davidad" Dalrymple's original (the April 2026 paper, TeX
verbatim) in the left column,
the Lean-realized amendment (rendered back into the same Steele-style
metanotation) in the right — with token-level diff colouring and soundness
marks in the outer page margin.

## one verb

```
cargo run --release            # reads BL-rules.toml, emits + compiles out/BL-rules-diff.pdf
cargo run --release -- --no-compile   # emit .tex only
```

Idempotent: `../BL-rules.toml` is the single source of truth. When a rule evolves
(a PROPOSED-B* ruling lands, a v1 lemma closes), edit its entry and re-run.

## how it works

- **tokenize** both TeX snippets (control words, alphanumeric runs, single
  chars; comments stripped, whitespace normalized),
- **LCS diff** over the token streams — invariants proptested: shared∪left
  reconstructs the left stream, shared∪right the right,
- **colorize**: maximal changed runs wrapped in `\dfl` (red, left-only) /
  `\dfr` (blue, right-only). Structural tokens (braces, brackets, scripts,
  alignment, row breaks), argument-taking macro heads, dimension literals,
  environment names, and `\inferrule*`'s keyval argument are never wrapped
  (their *content* still carries colour, so no diff information is lost —
  the macro glyph itself just stays black). Script arguments get braced
  (`_{\dfl{1}}`).
- **assemble** rows into `template.tex` (longtable, centre vertical rule,
  `marginnote` marks — outer edge under twoside) and compile with
  `latexmk -lualatex`.

## provenance & marks discipline

- Left cells are paper-provenance content: **verbatim, never
  normalized**.
- Every margin mark traces to a named witness: ✓ → a Lean lemma whose axiom
  closure was verified `[propext, Classical.choice, Quot.sound]` (no
  sorryAx) on 2026-07-16, with `leanchecker` replay + a
  `safe_verify` screen; ✗ → a named counterexample (Soundness.lean header /
  §S9). SafeVerify's module-level scan of Soundness.olean flags exactly the
  three declarations carrying the inventoried v1-frontier sorries
  (`ProofObject.sound`, `._unary`, `check_sound`) — disjoint from every
  cited lemma; SoundnessDemo.olean passes wholesale.
- Rules with no mark are open — absence is honest.

## known cosmetic limits

- Re-rendered TeX is token-normalized: spacing inside `\text{…}` can gain a
  space around braces (invisible in math, occasionally visible in text).
- Under-colouring by design at structural tokens and macro heads (see above);
  never mis-colouring.

## files

- `../BL-rules.toml` — the rules source (36 entries: 14 core, sp[Cell],
  admissible/alias rows, ReLU-Split, and the five composition rules —
  Promise, Syzygy, SmallGain, SmallGainN, ProductLattice — folded in
  from the former AG-rules.toml, 2026-08-02). Every rule row carries `tier`
  per the three-tier taxonomy (ratified 2026-07-18): 1 = core
  rule (semantic soundness), 2 = admissible rule (verified unpacking
  into core rules), 3 = alias rule (verified unpacking into a single
  admissible-or-core rule); the ratified words render in the cellheads.
- `template.tex` — document shell (macros are the paper's own subset).
- `src/main.rs` — tokenizer, LCS, colorizer, assembler (+ proptests in
  `tests/`).
- `out/BL-rules-diff.pdf` — the compiled artefact (committed; aux files
  ignored).
- `out/BL-rules-diff-print.pdf` — portrait-re-imposed variant for
  printers that refuse landscape-dimension pages. Print with
  short-edge (tumble) duplex — it keeps rotated-landscape
  backs upright, and LaTeX twoside outer-margin marks land on the free
  edges.

## the book (the literate rule catalogue)

```
cargo run --release --bin qtsl-book                     # out/BL-rule-book.pdf
cargo run --release --bin qtsl-book -- render --rule Syzygy   # one-rule excerpt
cargo run --release --bin qtsl-book -- check            # validations, no TeX
cargo run --release --bin qtsl-book -- bind --from-receipts   # re-anchor hashes
```

One subsection per catalogue rule: the Steele cell (JOINED from the
catalogue rule pages, `BL-rules.toml`/`QTSL-rules.toml` — never
duplicated) with substantial book-side
commentary, the Lean statements and — where a side condition's meaning
must be visible — full checker definitions (extracted from source by decl
name at every render; a rule may bind several modules), the Lean verifier
receipts (cited from the receipt store (`$LEAN_RECEIPT_STORE`),
signature-verified at render against the trust-roots file — resolution
in `book_main.rs` — staleness badged
against `book/bindings.toml`, signers shown by key fingerprint), the HOL4
statement or its loud reasoned absence, documentary HOL receipts, and a
hand-authored proof (`book/proofs/<id>.tex`; genre by tier — alias proofs
carry a filled-in application of the target rule). Front matter renders
the coverage dashboard (incl. an Isabelle column, uniformly absent) over
every rules-page row. **The book's reader is a cold external researcher**:
rendered text carries no internal work-tracking references, private
paths, host names, or
internal ruling citations — see `book/DESIGN.md` ("reader model") for the
posture, the data model, and staleness semantics. Badge doctrine: amber =
stale/absent; red only for outright verification failure. The compile
step gates on `Missing character` in the LuaLaTeX log (the glyph
discipline, ported — lualatex alone exits 0 on dropped glyphs). The book
is portrait A4, printable as-is; the
tool itself never prints.

Sharded for parallel authorship (the authoring fan): `book.toml` carries
`[meta]` only — every `[[rule]]`/`[[coverage]]` entry is its own file
under `book/book.toml.d/` (stem = rule id / sanitized row), statement
bindings shard per entry under `book/bindings.toml.d/`, and per-batch
literature rides `book/refs.d/*.tex` (spliced into the bibliography,
duplicate keys loud). Section order is roster order, computed — never
negotiated in a shared file. `bind` keeps unmoved modules' rows verbatim
(plain `qtsl-book bind` is legal when nothing moved; `--keep-moved`
additionally leaves moved modules un-re-anchored so their amber
survives).
