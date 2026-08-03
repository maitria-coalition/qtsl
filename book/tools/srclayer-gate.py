#!/usr/bin/env python3
"""srclayer-gate.py — verify the built PDF's source-carrying channels.

Usage: srclayer-gate.py BOOK_PDF BOOK_TEX MANIFEST

Verifies, against the assembled single-file source (BOOK_TEX):

1. INVISIBLE LAYER, byte-exact: the recipe printed on the colophon page
   — pdftotext -layout -fixed 3.125 -f <first source page>, form feeds
   deleted — reproduces BOOK_TEX exactly. The first source page is
   re-derived here from the page count and the manifest's chunk count,
   independently of the colophon's own arithmetic.
2. COLOPHON HONESTY: the colophon page (the page before the chunks)
   states the same -f page number and the same -fixed cell this gate
   just used — the printed recipe and the verified recipe cannot drift
   apart.
3. ATTACHMENT, byte-identical: pdfdetach recovers book.tex.
4. FLAGLESS CHANNEL: bare pdftotext output contains sentinel source
   lines (first, middle, last non-blank) — the uninstructed reflex
   yields the source readably.

Skips (exit 0, loud note): BOOK_SKIP_SRCLAYER_GATE=1, or poppler tools
absent (lone-clone environments; the committed artefacts are built where
the tools exist).
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

FIXED = "3.125"  # the grid cell in PDF points; srclayer.tex's twin


def fail(msg: str) -> None:
    print(f"srclayer gate: FAIL - {msg}", file=sys.stderr)
    sys.exit(1)


def main() -> None:
    if len(sys.argv) != 4:
        fail(f"usage: {sys.argv[0]} BOOK_PDF BOOK_TEX MANIFEST")
    pdf, tex, manifest = map(Path, sys.argv[1:4])

    if os.environ.get("BOOK_SKIP_SRCLAYER_GATE"):
        print("srclayer gate: skipped (BOOK_SKIP_SRCLAYER_GATE)")
        return
    for tool in ("pdftotext", "pdfdetach", "pdfinfo"):
        if not shutil.which(tool):
            print(f"srclayer gate: skipped ({tool} not installed - "
                  f"install poppler-utils to verify the source layer)")
            return

    m = re.search(r"\\def\\srclChunkCount\{(\d+)\}",
                  manifest.read_text(encoding="utf-8"))
    if not m:
        fail(f"{manifest} carries no \\srclChunkCount")
    chunks = int(m.group(1))
    expected = tex.read_bytes()

    info = subprocess.run(["pdfinfo", str(pdf)],
                          capture_output=True, text=True, check=True)
    pages = int(re.search(r"^Pages:\s+(\d+)", info.stdout, re.M).group(1))
    first = pages - chunks + 1

    # 1. the invisible layer, byte-exact under the printed recipe.
    got = subprocess.run(
        ["pdftotext", "-layout", "-fixed", FIXED, "-f", str(first),
         str(pdf), "-"],
        capture_output=True, check=True).stdout.replace(b"\x0c", b"")
    if got != expected:
        gl, el = got.split(b"\n"), expected.split(b"\n")
        for i, (a, b) in enumerate(zip(gl, el)):
            if a != b:
                fail(f"layer extraction diverges from {tex} at line "
                     f"{i + 1}:\n  extracted: {a[:120]!r}\n"
                     f"  source:    {b[:120]!r}")
        fail(f"layer extraction length differs: {len(gl)} extracted "
             f"lines vs {len(el)} source lines")

    # 2. the colophon page states the recipe this gate just verified.
    colophon = subprocess.run(
        ["pdftotext", "-f", str(first - 1), "-l", str(first - 1),
         str(pdf), "-"],
        capture_output=True, text=True, check=True).stdout
    for needle in (f"-f {first}", f"-fixed {FIXED}", "pdfdetach"):
        if needle not in colophon:
            fail(f"colophon page {first - 1} does not state {needle!r} "
                 f"- its printed recipe drifted from the layer")

    # 3. the attachment.
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(["pdfdetach", "-saveall", str(pdf.resolve())],
                       cwd=td, capture_output=True, check=True)
        detached = Path(td) / "book.tex"
        if not detached.exists():
            fail("no book.tex attachment in the PDF")
        if detached.read_bytes() != expected:
            fail("attachment book.tex differs from the assembled source")

    # 4. the flagless channel, by sentinels.
    bare = subprocess.run(["pdftotext", str(pdf), "-"],
                          capture_output=True, check=True).stdout
    lines = [ln for ln in expected.split(b"\n") if ln.strip()]
    for which, ln in (("first", lines[0]),
                      ("middle", lines[len(lines) // 2]),
                      ("last", lines[-1])):
        if ln.strip() not in bare:
            fail(f"bare pdftotext lacks the source's {which} line "
                 f"{ln[:80]!r}")

    print(f"srclayer gate: ok - layer byte-exact ({chunks} pages from "
          f"page {first}), colophon recipe verified, attachment "
          f"byte-identical, flagless channel carries the source")


if __name__ == "__main__":
    main()
