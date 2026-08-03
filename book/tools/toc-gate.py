#!/usr/bin/env python3
"""toc-gate.py — fail the build when the front matter loses its links.

Regression class (observed 2026-07): a tagging/hyperlink package
interaction produced a book whose table of contents rendered perfectly
but carried ZERO link annotations — and a dead-link checker is
structurally blind to links that are absent rather than broken. This
gate counts Link annotations over the front page range (where the ToC
lives) and requires the structure-tree root (tagged-PDF machinery) to
survive, failing the build loudly like the glyph gate.

Usage:  tools/toc-gate.py BOOK.pdf
Env:    BOOK_TOC_PAGES       front page range to scan (default 15)
        BOOK_TOC_MIN_ANNOTS  minimum Link annotations (default 250)
        BOOK_SKIP_TOC_GATE   set to skip entirely (minimal environments)
        BOOK_TOC_EXPECT_UNTAGGED  skip the structure-tree check only:
            an untagged health build (BOOK_UNTAGGED=1) has no
            /StructTreeRoot BY DESIGN, but its ToC links are still
            real — the links half of this gate stays live for it
            (composition fix, 2026-07-29: the untagged toggle and this
            gate were born on parallel branches; without this flag
            every health build would fail the tagged check)

Baseline at adoption: 298 Link annotations on ToC pages 3-9 of the
~1000pp book (2713 document-wide). The 250 threshold leaves reflow
margin while catching the all-links-vanished class outright; a partial
regression that halves the ToC's links also trips it.
"""

import os
import sys

try:
    import pikepdf
except ImportError:
    print(
        "toc-gate: pikepdf is not installed — install it (e.g. apt install "
        "python3-pikepdf / pip install pikepdf) or set BOOK_SKIP_TOC_GATE=1 "
        "to skip this gate",
        file=sys.stderr,
    )
    sys.exit(1)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: toc-gate.py BOOK.pdf", file=sys.stderr)
        return 2
    pages_to_scan = int(os.environ.get("BOOK_TOC_PAGES", "15"))
    min_annots = int(os.environ.get("BOOK_TOC_MIN_ANNOTS", "250"))

    with pikepdf.open(sys.argv[1]) as pdf:
        n = min(pages_to_scan, len(pdf.pages))
        links = 0
        for page in pdf.pages[:n]:
            for annot in page.get("/Annots", []):
                if annot.get("/Subtype") == pikepdf.Name("/Link"):
                    links += 1
        tagged = "/StructTreeRoot" in pdf.Root

    expect_untagged = bool(os.environ.get("BOOK_TOC_EXPECT_UNTAGGED"))
    ok = True
    if links < min_annots:
        print(
            f"toc-gate: FAIL — {links} Link annotations on the first {n} "
            f"pages (< {min_annots}); the table of contents has lost its "
            "hyperlinks (vanished-links class — check the hyperref/tagging "
            "package interactions noted in chapters.tex)",
            file=sys.stderr,
        )
        ok = False
    if not tagged and not expect_untagged:
        print(
            "toc-gate: FAIL — /StructTreeRoot missing from the document "
            "catalog; PDF tagging was lost",
            file=sys.stderr,
        )
        ok = False
    if ok:
        tag_note = (
            "structure-tree check skipped (BOOK_TOC_EXPECT_UNTAGGED)"
            if expect_untagged
            else "structure tree present"
        )
        print(f"toc-gate: ok — {links} front-matter link annotations "
              f"(>= {min_annots}), {tag_note}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
