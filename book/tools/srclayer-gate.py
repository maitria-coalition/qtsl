#!/usr/bin/env python3
"""srclayer-gate.py — verify the built PDF's source-carrying channels.

Usage: srclayer-gate.py BOOK_PDF BOOK_TEX MANIFEST

The MODE comes from the manifest (the same file that configured
srclayer.tex, so gate and artefact cannot disagree):

ATTACHMENT-ONLY MODE (\\srclAttachmentOnly in the manifest — the
current mode; the invisible text layer is off since it crashed iOS
Safari's renderer, see srclayer.tex STATUS):

A. ATTACHMENT, byte-identical: `pdfdetach -list` names book.tex as
   attachment 1 and `pdfdetach -save 1` — the exact incantation the
   book prints — recovers BOOK_TEX byte-exactly.
B. COLOPHON HONESTY: the final page prints that same pdfdetach recipe.
C. HEAD NOTE: page 1 (the title page's white-on-white note for agents
   that read only the PDF's head) prints the recipe too.

FULL-LAYER MODE (no \\srclAttachmentOnly; re-arms automatically when
build.sh drops --attachment-only), verified against the assembled
single-file source (BOOK_TEX):

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


def page_text(pdf: Path, page: int) -> str:
    """One page's extracted text, whitespace-collapsed (a printed recipe
    may wrap; needles are matched against the flattened form)."""
    out = subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), str(pdf), "-"],
        capture_output=True, text=True, check=True).stdout
    return " ".join(out.split())


def verify_attachment_only(pdf: Path, expected: bytes, pages: int) -> None:
    """Attachment-only mode: the layer is off; the attachment and both
    printed recipes (colophon + title-page head note) are the contract."""
    # A. the attachment, under the exact printed incantation.
    listing = subprocess.run(["pdfdetach", "-list", str(pdf)],
                             capture_output=True, text=True,
                             check=True).stdout
    if not re.search(r"^\s*1:\s*book\.tex\s*$", listing, re.M):
        fail(f"pdfdetach -list does not name book.tex as attachment 1:\n"
             f"{listing.strip()}")
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(["pdfdetach", "-save", "1", str(pdf.resolve())],
                       cwd=td, capture_output=True, check=True)
        detached = Path(td) / "book.tex"
        if not detached.exists():
            fail("pdfdetach -save 1 produced no book.tex")
        if detached.read_bytes() != expected:
            fail("attachment book.tex differs from the assembled source")

    # B. colophon honesty: the final page prints the recipe.
    colophon = page_text(pdf, pages)
    for needle in ("pdfdetach -list", "pdfdetach -save 1", "book.tex"):
        if needle not in colophon:
            fail(f"final page (the source-attachment colophon) does not "
                 f"state {needle!r} - its printed recipe drifted")

    # C. the head note: page 1 prints the recipe for agents that read
    #    only the start of the PDF (white-on-white on the title page).
    head = page_text(pdf, 1)
    for needle in ("pdfdetach -list", "pdfdetach -save 1"):
        if needle not in head:
            fail(f"page 1 lacks the head note's {needle!r} - the title "
                 f"page's agent-facing recipe is missing or drifted")

    print(f"srclayer gate: ok - ATTACHMENT-ONLY mode (text layer off): "
          f"attachment 1 byte-identical under 'pdfdetach -save 1', "
          f"colophon (page {pages}) + title-page head note both print "
          f"the recipe")


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

    manifest_text = manifest.read_text(encoding="utf-8")
    expected = tex.read_bytes()

    info = subprocess.run(["pdfinfo", str(pdf)],
                          capture_output=True, text=True, check=True)
    pages = int(re.search(r"^Pages:\s+(\d+)", info.stdout, re.M).group(1))

    if re.search(r"\\def\\srclAttachmentOnly\{1\}", manifest_text):
        verify_attachment_only(pdf, expected, pages)
        return

    m = re.search(r"\\def\\srclChunkCount\{(\d+)\}", manifest_text)
    if not m:
        fail(f"{manifest} carries no \\srclChunkCount")
    chunks = int(m.group(1))
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
