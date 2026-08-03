# refs.d/

Bibliography data staged for the book.

- `zettels.bib` — biblatex entries (468) for the reading-notes corpus
  behind the book's citations. Generated; regenerate upstream rather
  than hand-editing.

Status: consumed by the build — `chapters.tex` loads all three `.bib`
files via biblatex `\addbibresource`, and `build.sh` runs biber and
inlines the resulting `.bbl` into the assembled `book.tex`. (The
generated rule-catalogue chapter additionally carries its own manual
`thebibliography`, self-contained by its conventions.) Titles must be
glyph-gate-clean: LaTeX math macros, never literal Unicode math
glyphs — the upstream zettels generator still emits Unicode `ω`-class
characters in a few titles, hand-repaired here; fix at regeneration.
