# The literate rule catalogue: design note

Goal: every catalogue rule
gets a beautifully typeset subsection — the rule in Steele's Computer
Science Metanotation, the Lean statement, Lean verifier receipts, the HOL
statement, HOL verifier receipts, and a typeset proof (core rules at
Putnam-exam-solution detail; admissible/alias rules as proof-tree-rewriting
templates/recipes). Isabelle is an open question — rendered as an honestly
empty column with a note, never silently omitted.

This note fixes the data model, the receipt-binding/staleness semantics,
the proof-authoring convention, and the build verb. The first exemplars
(Syzygy, PConstExact, SmallGain — one per tier) ship in the same leg.

## reader model (the 2026-07-19 revision — a 13-point editorial)

The book's reader is a **cold external researcher** with no house
context; the artefact carries export-sanitization posture throughout.
Consequences, binding on
every string that renders:

- no internal work-tracking references, ruling timestamps, private
  section citations, host/box names, or private paths in rendered
  text; receipts render as content-addressed
  attestations (signer ed25519 key fingerprint + artefact SHA-256).
- the internal rules pages' `note` and `stratum` fields are **never
  rendered** by the book; `book.toml` carries its own per-rule
  `commentary` (substantial: what the rule does, when a producer uses
  it, what the checker recomputes, what would break without each
  hypothesis) and `note`.
- Steele-cell honesty: the sourcenote says the metanotation statement is
  typeset by hand for notational quality, that its mechanized ground
  truth is the extracted-and-hash-bound Lean beside it, and that the
  rule *roster* is machine-checked while the statement *text* is
  editorial (the a8836 finding, stated honestly instead of as a
  "no-auto-scan discipline" mantra).
- badge colours: **amber = stale or absent** (stale receipts, statement
  drift, absence boxes); **red is reserved for outright verification
  failure** (a checker or signature rejecting).
- Isabelle: a dashboard column (uniformly `—`) plus one caption
  sentence; no front-matter block, no per-rule line.
- alias rules name their target in the section header ("alias for
  <target>", target coloured) and their proof carries a filled-in
  display-style application of the target rule.
- known residue: two Lean doc comments quoted verbatim into the book
  (`SyzygyStep`, `holds_of_syzygyConclusionForm`) carry internal design
  vocabulary and one ratification attribution — they are hash-bound
  source text, so scrubbing them is a Lean-tree edit + rebuild +
  receipt re-mint, i.e. part of the tree's own pre-publication
  sanitization pass, not a book edit.

## where each ingredient lives (single sources of truth, joined at build)

The design principle is the one the diff-typesetter already established
(commit 2337a96e2: rule rows are hand-authored; the generator scans the
Lean tree only for the round-trip check and live marks): **each ingredient
stays in its existing home; the book generator joins them at build time
and never duplicates content it can resolve.**

| ingredient | home | resolution |
|---|---|---|
| Steele rule cell | `BL-rules.toml` / `QTSL-rules.toml` rows (hand-authored, the pages' single source; the former `AG-rules.toml` rows folded into `BL-rules.toml` 2026-08-02) | joined by `(source file, row name)`; the book renders the `amended` column (the realized rule) in plain black — the book is not a diff page |
| tier + stratum | same rows (`tier`, the ratified taxonomy of 2026-07-18) | same join |
| Lean statement | the Lean sources themselves | **decl-name pointers resolved at build**: each `[[rule.lean]]` block (a rule may have several — Syzygy also binds `Core.Catalogue` for its checker definitions) names `module` + `decls` (signature-only extraction) + `full_decls` (whole-body extraction, for definitions whose meaning the book binds by display) + optional `intro` prose — quoted text cannot drift from the tree silently, because it is re-read every render and hashed against the binding (below) |
| Lean verifier receipts | the ed25519 receipt store: `$LEAN_RECEIPT_STORE`, default `~/.local/share/lean-receipts` (resolution in `book_main.rs`) | resolved at render by module name over the whole store; **cited, never re-run** — the render never invokes Lean (receipts are the attestation surface) |
| HOL statement | the HOL development (`hol/checker/*Script.sml`) | decl-name pointers (`Definition`/`Theorem` blocks extracted by name), same drift-hashing; `status = "absent"`/`"out-of-scope"` rows carry a hand-written reason rendered LOUDLY in the cell |
| HOL verifier receipts | documentary: the HOL development's build census (hol-strict runs) + landing evidence | hand-cited TeX in `book.toml`; there is **no signed HOL receipt store yet** — the book says so in the receipt cell itself (named future work, kin of the Lean store) |
| Isabelle | nothing in-house | dashboard column, uniformly `—`, plus one caption sentence ("there is no in-house Isabelle development to date, so every rule's Isabelle cell reads —"); no front-matter block, no per-rule boilerplate |
| proof | `book/proofs/<id>.tex`, hand-authored | included verbatim; these are scholarly artefacts a mind writes — genre by tier (below) |
| bindings (hashes) | `book/bindings.toml`, machine-maintained | the staleness ground truth; see next section |

`book/book.toml` is the hand-authored `[meta]` spine; every `[[rule]]`
and `[[coverage]]` entry lives in its own fragment file (next section).
`book/bindings.toml` + `book/bindings.toml.d/` are machine-maintained
(the `bind` verb) and hold hashes only. Hand-prose and machine-state
never share a file, so a diff touching bindings is always mechanical and
a diff touching `book.toml`/`book.toml.d/` is always editorial.

## the fan seam: one fragment file per catalogue row (2026-07-20)

The full fill-in is embarrassingly parallel only if no two authors edit
one file. The sharding, essential for the authoring fan:

- **`book/book.toml.d/<name>.toml`** — exactly one `[[rule]]` xor one
  `[[coverage]]` entry per fragment, byte-for-byte the schema those
  entries have always had. A rule fragment's file stem must equal its
  `id` (ids are filename-safe by fiat: `[A-Za-z0-9_-]`); a coverage
  fragment's stem is the sanitized row name (non-safe chars map to `_`).
  Graduating a coverage entry to a full section = rewriting that row's
  own file — never an edit to a shared one.
- **load = book.toml ∪ fragments** (fragments sorted by filename for
  deterministic parse order), then union checks, loud: duplicate rule
  ids, a (source, row) claimed by two entries of either kind, stem/id
  mismatch, a fragment carrying two entries.
- **section order is the roster order** — (page index in `meta.pages`,
  row index in the page), a pure function of the curated catalogue,
  never encounter order across fragment files and never data parallel
  authors negotiate. (This is why the exemplar edition's section order
  changed at migration: PConstExact (BL-rules.toml) now precedes Syzygy
  (then on AG-rules.toml; folded into BL-rules.toml 2026-08-02).)
- **`book/bindings.toml.d/<entry>.toml`** — per-entry `[[statement]]`
  shards, machine-written by `bind`; the monolith keeps only
  `[[module]]` + `[[hol_file]]` rows. Two entries citing one decl is
  legitimate (exact-duplicate rows collapse at load); one (module, decl)
  with two different hashes is a loud error everywhere.
- **`bind` is incremental over modules**: a module whose source git blob
  is unchanged since the last bind keeps its row *verbatim* (olean,
  provenance and all), so a parallel author's bind is a pure addition —
  untouched modules never churn, and plain `qtsl-book bind` (no mode
  flag) is legal whenever no bound module moved. A new-or-moved module
  demands `--lean-build` or `--from-receipts` exactly as before. Stale
  statement shards (entry deleted) are removed by `bind`.
- **`book/refs.d/<batch>.tex`** — per-batch literature additions,
  spliced before `refs.tex`'s `\end{thebibliography}` at assembly
  (fragments sorted by filename); a duplicate `\bibitem` key anywhere in
  the union is a loud error. The shared `refs.tex` stays the curated
  base; folding fragments into it is anneal material, not fan work.
- **empty Steele cells fail the render**: a `[[rule]]` entry joining a
  roster row whose `amended` cell is empty errors loudly — the Steele
  statement is authored in the rules page first; the book joins, never
  duplicates.

## receipt binding and staleness (the loud-badge semantics)

A receipt attests `(module, olean_sha256, env_sha256,
toolchain, layers, node, ts)`, ed25519-signed. The book must cite receipts
**for the statements it prints**, and staleness must be VISIBLE — a receipt
for an older statement renders with a loud stale badge, never silently.

`bindings.toml` records, per bound Lean module:

- `package` — which Lean package the module lives in (`main` = the
  Qtsl calculus package; `qtsl-aux` = the QtslAux
  auxiliary measure-theory library). Sources resolve through the
  crate-relative `src` path either way; the field is provenance plus the
  routing key for future per-package build steps (2026-07-19,
  the multi-package plumbing leg — before it, only main-package modules
  had ever been bound, and the Q-family's qtsl-aux mechanization was
  invisible to the dashboard);
- `olean_sha256` — the module build the book is bound to (the attested
  artefact the receipts are judged against) — or EMPTY for a module bound
  source-only (see `--allow-unbuilt` below);
- `olean_provenance` — where that hash came from (a receipt id, or a local
  `.lake/build` hash at `bind` time) — documentation, printed in the
  colophon;
- `source_git_blob` — the `.lean` file's git blob sha at bind time;
- per-decl `statement_sha256` — sha256 of the extracted statement text.

At render, three independent comparisons produce the badges:

1. **statement drift (AMBER, loud)** — the re-extracted statement's sha
   differs from the binding: the printed proof and every cited receipt
   predate the statement. Badge on the Lean cell AND on the proof block
   (the proof was written against the old statement; it is now testimony,
   not warrant). (Amber, not red: drift is staleness; red is reserved for
   outright verification failure — a checker or signature rejecting.)
2. **module drift (AMBER)** — statements re-extract identically but the
   file's git blob moved: the module changed around the statement; receipts
   for the bound olean still attest the bound build, and the binding needs
   a re-`bind` from a rebuilt tree to re-anchor.
3. **receipt match (per receipt)** — every store receipt for the module is
   listed. `receipt.olean_sha256 == binding.olean_sha256` ⇒ **current**
   (green, layers credited); mismatch ⇒ **STALE** (amber badge, mint
   date shown, layers NOT credited). The per-layer coverage line under the
   table states, for each of the four gate layers (`build`, `replay` =
   leanchecker, `hardened` = safe_verify, `decorrelated` = lean4export +
   nanoda), whether a CURRENT receipt covers it — so "the last
   replay+hardened coverage predates the current build" is a fact the page
   itself displays. The comparator harness (P1/P2/P3, `comparator/README`)
   is cited per-rule only where a fixture exercises the rule; otherwise its
   line reads "no comparator fixture exercises this rule" — absence loud.
4. **signature** — every cited receipt file is verified at render by
   shelling to `lean-receipt verify` with `LEAN_RECEIPT_ROOTS` =
   the trust-roots file (see `book_main.rs`); signer names come from the root store. A
   missing `lean-receipt` tool fails the render (fail closed — the book
   never prints receipt claims it could not check), unless `--no-receipts`
   explicitly requests a render whose every receipt cell says
   "store not consulted this render".

Why bind to an olean rather than only to source: the receipt's subject IS
the olean (+ env hash); source-level hashes alone cannot say "this receipt
attests this build". Why also bind to source: the render host may hold
no Lean build (Lean runs ride a remote builder), so source
drift is the always-available freshness signal between `bind`s. The two
together give the honest matrix; neither alone does.

`qtsl-book bind` refreshes bindings: statement shas + git blobs always
(no Lean needed); `--lean-build <dir>` additionally re-hashes oleans from
a built tree (run it on the remote build host, or accept a fresh
receipt's attested hash with `--from-receipts`, which records the receipt
id as provenance). Seeding note for this first leg: bindings were seeded
`--from-receipts`-style from the 2026-07-18T13:21Z build receipts,
which postdate the last commit touching the Lean package (11:55Z) — the
provenance fields say exactly this.

## correspondence certification (the reviewer-grade ratchet, 2026-07-20)

A `[[rule]]` fragment may carry a `correspondence` field: TeX prose
stating HOW the bound Lean statements interpret the Steele display —
display metavariable $\mapsto$ Lean binder, each display hypothesis
$\mapsto$ the premise or side condition carrying it, the display
conclusion $\mapsto$ the goal, and **any deliberate width difference
named outright** (each of the first three dictionaries surfaced one:
PConstExact's lemma is proven for all `BowTie` comparators including the
display-excluded $\neq$ — an admission-layer exclusion that used to be
commentary lore and is now certified statement; QBasin's E1 annotation
is enforced by type, not hypothesis; SmallGain's payload structure is
narrower than its display on idx/wire side conditions).

`bind` records, in the entry's own bindings shard, a
`[[correspondence]]` certification triple: `steele_sha256` (the roster
row's `amended` cell), `statements_sha256` (digest over the entry's
sorted statement rows), `prose_sha256` (the dictionary text itself — an
edited dictionary must re-certify; text and pair travel together).
Pass-marker semantics, deliberately: an existing triple is kept
VERBATIM across binds — a bind run for any other reason (receipt
refresh, new modules) must never silently launder an unreviewed change
into "certified" — and is re-stamped only on the first bind of a new
dictionary or under an explicit `bind --recertify <rule-id|all>`.

At render the recorded triple is compared against the three live
hashes: full match $\Rightarrow$ green "reviewer-certified against the displayed
texts"; any mismatch $\Rightarrow$ amber naming exactly which side(s) moved; prose
without a recorded triple $\Rightarrow$ amber "uncertified"; no prose $\Rightarrow$ a loud
absence box on every Lean-citing rule (absence is the point, as with
every other column). The dashboard carries a `corr` column with the
same semantics. A correspondence field on a rule with no Lean bindings
is a loud error — a dictionary needs both of its sides.

The correspondence claim itself stays editorial: reviewer-grade, not
machine-checked. Its machine-checked successor types each rule's
soundness statement against the rule as a structured object
(rule-as-data), and supersedes this block per rule as those statements
land; the dictionary prose is kept as the human-readable gloss it
always was. Nothing built for the ratchet is discarded by the upgrade.

## proof authoring (the scholarly artefacts)

`book/proofs/<id>.tex`, one file per rule id, hand-written, genre by tier:

- **core (tier 1)** — an ordinary mathematical proof at Putnam-exam-solution
  detail: numbered lemma chain, every hypothesis of the rule used and
  *remarked on* (a Putnam solution explains why each hypothesis is needed,
  ideally with the counterexample that removing it admits), literature
  citations to the theorems actually drawn on (`book/refs.bib`, biblatex),
  and a formal-anchor table mapping each proof step to the Lean decl that
  carries it.
- **admissible (tier 2)** — a proof-tree-rewriting recipe: the general
  admissible template (one node ⇒ a derivation fragment over core +
  previously-justified rules), then the rule's instance as a before/after
  tree rewrite. Where a rule is admissible by *reduction to verified
  machinery* rather than by catalogue derivation (PConstExact is the
  ratified example — its TIER NOTE is explicit that no catalogue derivation
  exists, which is the rule's point), the recipe says so and shows the
  degenerate rewrite: the node discharges against a named verified theorem,
  not against catalogue nodes.
- **alias (tier 3)** — a respelling template: the verified 1→1 unpack
  function, the payload-transport table (field ↦ field), the two-line
  algebraic identity that makes the respelling exact, and the soundness
  corollary through the target rule's lemma.

Each proof file's header comment names the decls and the statement shas it
was written against; the render cross-checks those shas against the live
extraction, so a proof written against a superseded statement badges RED
automatically (comparison 1 above covers this — the proof inherits the
Lean cell's statement-drift badge).

## dashboard-only coverage entries (`[[coverage]]`)

Between "all-absent row" and "full literate section" there is an honest
intermediate state: the rule's soundness theorems EXIST in the Lean
development, but its commentary, proof, and HOL treatment are not yet
authored. A `[[coverage]]` entry in `book.toml` wires exactly that
state: it names the rules-page row and one or more `[[coverage.lean]]`
blocks (same shape as a rule's, package field included), and the
generator runs the same extraction + hash-binding + receipt-credit
machinery over them — but renders NO body section. On the dashboard the
row then shows its Lean statement glyph and receipt layers honestly,
while proof and HOL stay absent dashes. A `conditional = true` flag
renders the hyp-flavoured check (`\dcond`): statements bound and fresh,
but the cited theorems warrant the rule *conditionally* — named
hypothesis gaps (QMorseDischarge's G3–G6, QBlockInv's G1) or a proven
fragment/profile (batteries at the discrete-kernel profile, the Streett
K5 cluster, the AG C1/C2/C3a cells) — with the specifics living in the
rule's row on its own catalogue page. A row may not carry both a
coverage entry and a full `[[rule]]` entry (graduating to a full section
deletes the coverage entry). First application (2026-07-19): seven QTSL
rows — QBasin (unconditional), QMorseDischarge, QBlockInv,
QSafetyBattery, QDeadlineBattery, QStreettBundle, QAGCompose — 20
statements across 8 modules of both packages, every declaration
grep-verified at wiring time.

## the coverage dashboard

The book's front matter renders one table over the UNION of all rule rows
from every registered page source (today: `BL-rules.toml`, composition
rows included, + `QTSL-rules.toml`): rule, tier, and per-ingredient status glyphs —
Lean statement bound, receipts per layer (current / stale-only / none),
HOL statement (ported / absent / out-of-scope), HOL receipt, proof text.
Rules with no book entry render as all-absent rows, loudly: **the
dashboard is the point** — the book states what the assurance edifice does
NOT yet cover, per rule, at a glance. QTSL's 34 catalogued rules
(the QTSL rule catalogue note (upstream)) join the dashboard when they get their
rules-TOML page; the registry of page sources is one list in `book.toml`.

## API sections (the producer surface, per entry — 2026-07-21)

Every catalogue entry carries an **API** block immediately after its
metanotation block: the entry's producer surface in **TypeScript**
(the `@maitria/mtk` arranged namespaces) and **Rust** (the
`crates/mtk-catalogue` builders) — for each language the declaration's
signature and a construction snippet. The design principle is the same
join-don't-duplicate law as the Lean cells: nothing is quoted by hand.
At every render the extractor (`src/api.rs`) re-reads the toolkit
sources — signatures by declaration name (`fn NAME`, `interface NAME`;
line-anchored, so call sites never match), snippets from the toolkit's
conformance corpus by fixture-function body (`fn-body:NAME`), marker
pair (`marker:KEY`, reading `// book: api begin KEY` … `// book: api
end KEY` comments placed in the corpus), or golden-vector name
(`conform:VECTOR`, the construction argument of the corpus's
`conform("VECTOR", …)` byte-identity call). A missing declaration,
marker, or vector fails the render loudly, so quoted code cannot
drift silently — and because the snippet sources ARE the corpus whose
emitted bytes are byte-verified against the committed golden vectors,
the book's examples are receipted code, not documentation prose.

Data model, fan-seam sharded like everything else: `book/api.toml`
carries `[meta]` alone (`toolkit_root`, crate-relative; default the
sibling `mtk` repository checkout, the experiments chapter's
sibling-clone convention); `book/api.toml.d/<entry>.toml` carries one
`[api]` table per book entry — stem = id, `[api.ts]` + `[api.rust]`
each with `handle`, `sig_file`, `sig` (list of decl specs),
`snippet_file`, `snippet`, optional per-language `note`; entry-level
`note` for family remarks (parameterized alias builders, variant
selectors); a language may instead be absent with a stated
`ts_absent`/`rust_absent` reason (never silently). Fragment paths use
the public mtk repository layout (`crates/mtk-catalogue/...`,
`ts/...`); the resolver also accepts the workshop layout (the same
paths without the `crates/` prefix), so fragments never carry a
private path. Every `[[rule]]` entry must have an api fragment (a
missing one fails the render, like an empty Steele cell); an api
fragment citing no rule is a loud stale-fragment error. `--api-src
DIR` overrides the toolkit root at invocation — the regeneration
knob until the toolkit package migration into the mtk repository
completes.

**Standalone groups (the Primitive Catalogue seam, 2026-07-21).** A
catalogue that lives as a hand-authored chapter (the hypernet
chapter's 13 H-rows first) registers its entries in `api.toml` as a
`[[standalone]]` group: `dir` (repository-root-relative output
directory), `sourcenote` (the group states its own corpus and
receipts — the rule default speaks certificate-corpus language),
`ids`. `qtsl-book api-blocks` renders each id's API block to
`<dir>/<id>.tex`, committed like the emitted rule-catalogue chapter,
for the chapter to `\input` at its per-entry anchor; `check` and
`render` re-extract every standalone entry exactly like rule blocks,
so quoted code cannot drift silently on any path. The union checks
extend across the seam: a fragment citing neither a `[[rule]]` entry
nor a standalone group is stale; a standalone id without a fragment,
or doubling as a rule id, is a loud error.

## build verb

    qtsl-book [render] [--rule ID] [--no-compile] [--no-receipts]
              [--api-src DIR]
    qtsl-book check
    qtsl-book bind [--lean-build DIR | --from-receipts] [--allow-unbuilt]
                 [--keep-moved] [--recertify RULE-ID|all]

Plain `qtsl-book bind` (no mode flag) refreshes statement shards and
verifies module anchors, keeping every unmoved module's row verbatim —
the common case for a fan leg citing new decls of already-bound modules;
it fails loudly the moment a module is new or its source moved.

`bind --allow-unbuilt` (from-receipts mode): a module with no trusted
receipt in the store binds SOURCE-ONLY — empty `olean_sha256`, loud
stderr, provenance saying so — instead of failing the whole bind.
Statements stay hash-bound to source; the render shows an amber
no-attested-build note for the module and no receipt can be judged
current. The honest use: wiring a freshly mechanized module ahead of its
first gate run; re-bind after the gate mints its receipt.

`render` regenerates `out/BL-rule-book.tex` + PDF (latexmk, LuaLaTeX,
portrait A4 — the print pipeline accepts the PDF as-is;
nothing is printed by the tool itself). `--rule ID` renders a single
rule's subsection to `out/BL-rule-book-<id>.pdf` for fast iteration.
`check` runs every validation (joins, extractions, hashes, receipt
signatures) and emits nothing. The compile step greps the LuaLaTeX log for
`Missing character` and fails loudly — the print organ's glyph gate
(ported to this .tex pipeline), since lualatex itself exits 0 on
missing glyphs.

## explicitly out of scope (this leg)

- A signed HOL receipt store (the Lean store's twin). Named, not built:
  when the HOL development's landing evidence outgrows documentary citation, receipts
  should ride the same trust-root store per the unification ruling.
- Auto-generation of proof text. The proofs are authored, reviewed
  artefacts; the generator only includes, hashes, and badges them.
- ~~QTSL rows (await their rules-TOML page; the dashboard registry is ready).~~
  LANDED 2026-07-19: `QTSL-rules.toml` (34 tiered rows + judgement-kinds row,
  catalogued|staged) is registered in `meta.pages`; the dashboard shows
  every Q-rule with honest all-absent coverage glyphs. ~~Q-rule book entries
  (proofs, Lean/HOL pointers) remain the rollout leg's work.~~ UPDATE, same
  day (the multi-package plumbing leg): seven Q-rows now carry dashboard-only
  `[[coverage]]` Lean bindings (see that section); the full literate sections
  — commentary, proofs, HOL treatment — remain the rollout leg's work.
- Re-running any verifier at render time (receipts are citations by
  design; the gate machinery mints them where verification actually runs).
