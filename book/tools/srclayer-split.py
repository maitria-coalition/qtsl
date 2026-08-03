#!/usr/bin/env python3
"""srclayer-split.py — prepare the assembled book source for the invisible
source layer (srclayer.tex): normalize, split into page-sized chunks, and
write the TeX manifest that activates the layer.

Usage:
    srclayer-split.py [--attachment-only] SOURCE CHUNKDIR MANIFEST FONTDIR

- NORMALIZES SOURCE in place: strips trailing blanks ([ \\t\\r]+ before
  each newline) and asserts a trailing final newline. This is
  token-identical input by TeX's own line-reading rules (the reader
  deletes trailing spaces before tokenizing), and it is REQUIRED for the
  layer's byte-exactness: extractors reconstruct spaces from inter-glyph
  gaps, and there is no gap after a line's last glyph — trailing
  whitespace cannot ride any text layer. The normalized file is the one
  installed/served as book.tex, so the served bytes are recoverable ones.
- REFUSES (exit 1, with line numbers) on: mid-line tabs (verbatim
  typesetting would widen them — silent byte drift), control characters,
  non-UTF-8, or a line beyond MAX_LINE_CHARS (the appendix page-width
  ceiling; PDF pages max out near 16383pt).
- SPLITS at ~TARGET_LINES per chunk, nudging each boundary to fall
  between two non-empty lines: a blank line at a page edge has no
  neighbouring baseline on its own page, so no extractor could
  reconstruct it (measured). Asserts the chunks
  re-concatenate to the source byte-exactly before writing the manifest.

--attachment-only (the srclayer off-switch, 2026-08-03; see
  srclayer.tex STATUS — the invisible text layer crashed iOS Safari):
  normalize + UTF-8 check only, then write a manifest defining
  \\srclAttachmentOnly, which makes srclayer.tex emit the book.tex
  attachment and its colophon page but NO text-layer pages. Fonts are
  not staged, chunks are not cut, and the layer-only refusals (tabs,
  line length, blank runs — all extraction-fidelity concerns) are
  skipped: they must not fail builds for a dormant channel.
"""
import shutil
import subprocess
import sys
from pathlib import Path

TARGET_LINES = 2800     # ~15500pt at the 5.52pt leading; ceiling ~16300pt
BOUNDARY_SLACK = 400    # how far a boundary may slide to find text
MAX_LINE_CHARS = 4800   # ~15500pt at the layer's page-width formula
MAX_BLANK_RUN = 4       # poppler clamps blank-line synthesis at 5 EOLs

# the layer's private font copies (srclayer.tex loads these BY PATH so
# body-text font instances are never shared with — or width-patched
# like — the layer's; see srclayer.tex's grid commentary). kpsewhich
# resolves every face from the same TeX Live the build typesets with.
FONTS = [
    "DejaVuSansMono.ttf",
    "FreeMono.otf",
    "DejaVuSans.ttf",
    "FreeSerif.ttf",
    "STIX-Regular.otf",
    "Asana-Math.otf",
]


def fail(msg: str) -> None:
    print(f"srclayer-split: {msg}", file=sys.stderr)
    sys.exit(1)


def stage_fonts(fontdir: Path) -> None:
    """Copy the layer's fonts to private names under fontdir."""
    fontdir.mkdir(parents=True, exist_ok=True)
    for name in FONTS:
        found = subprocess.run(["kpsewhich", name],
                               capture_output=True, text=True)
        path = found.stdout.strip()
        if found.returncode != 0 or not path:
            fail(f"kpsewhich cannot resolve font {name} (the book build "
                 f"already depends on this face — check the TeX Live "
                 f"installation)")
        dest = fontdir / f"srcl-{name}"
        if not dest.exists() or dest.stat().st_size != Path(path).stat().st_size:
            shutil.copyfile(path, dest)


def main() -> None:
    args = sys.argv[1:]
    attachment_only = "--attachment-only" in args
    args = [a for a in args if a != "--attachment-only"]
    if len(args) != 4:
        fail(f"usage: {sys.argv[0]} [--attachment-only] "
             f"SOURCE CHUNKDIR MANIFEST FONTDIR")
    src, chunkdir, manifest, fontdir = map(Path, args)
    if not attachment_only:
        stage_fonts(fontdir)

    raw = src.read_bytes()
    try:
        raw.decode("utf-8")
    except UnicodeDecodeError as e:
        fail(f"{src} is not clean UTF-8: {e}")
    if not raw.endswith(b"\n"):
        raw += b"\n"

    # normalize: strip trailing blanks per line (see module docstring).
    lines = [ln.rstrip(b" \t\r") for ln in raw.split(b"\n")]
    # raw ends with \n, so split() leaves one trailing empty element that
    # represents end-of-file, not a final blank line — drop it here and
    # re-add the final newline at join time.
    assert lines[-1] == b""
    lines = lines[:-1]

    # layer-only refusals: extraction-fidelity concerns, checked only
    # when the text layer will actually carry the bytes (they must not
    # fail builds for a dormant channel; the attachment is byte-exact
    # by construction regardless).
    if not attachment_only:
        bad = [(i + 1, ln) for i, ln in enumerate(lines)
               if b"\t" in ln or any(b < 0x20 for b in ln)]
        if bad:
            where = ", ".join(str(n) for n, _ in bad[:10])
            fail(f"{src} has mid-line tabs/control chars at line(s) {where} — "
                 f"fix the originating chapter source (verbatim typesetting "
                 f"cannot carry them byte-exactly)")
        over = [(i + 1, len(ln)) for i, ln in enumerate(lines)
                if len(ln.decode("utf-8")) > MAX_LINE_CHARS]
        if over:
            n, ln = over[0]
            fail(f"{src} line {n} is {ln} chars (> {MAX_LINE_CHARS}) — beyond "
                 f"the source-appendix page-width ceiling")

        # blank runs: poppler's physical-layout renderer synthesizes at
        # most 5 line feeds between two baselines, so a run of >= 5 blank
        # lines cannot ride the text layer. The repair is always at the
        # source: shorten the run to <= 4 lines in the originating
        # chapter/listing (whitespace-only change).
        run_start, run_len = None, 0
        for i, ln in enumerate(lines):
            if ln == b"":
                if run_len == 0:
                    run_start = i + 1
                run_len += 1
                if run_len > MAX_BLANK_RUN:
                    fail(f"{src} has a run of >{MAX_BLANK_RUN} blank lines "
                         f"starting at line {run_start} — poppler clamps "
                         f"blank-line synthesis, so the text layer cannot "
                         f"carry it; shorten the run in the originating "
                         f"source to <= {MAX_BLANK_RUN} lines")
            else:
                run_len = 0

    normalized = b"\n".join(lines) + b"\n"
    if normalized != raw:
        src.write_bytes(normalized)
        print(f"srclayer-split: normalized {src} "
              f"({sum(1 for a, b in zip(raw.split(b'\n'), lines) if a != b)}"
              f" line(s) had trailing blanks)")

    if attachment_only:
        manifest.write_text(
            "% generated by tools/srclayer-split.py - source-attachment "
            "manifest\n"
            "% (read by srclayer.tex via \\@@input; never committed).\n"
            "% attachment-only mode: the invisible text layer is OFF\n"
            "% (srclayer.tex STATUS has the story and the re-enable).\n"
            "\\def\\srclAttachmentOnly{1}\n"
            f"\\def\\srclPayloadFile{{{src}}}\n",
            encoding="utf-8")
        print(f"srclayer-split: attachment-only manifest {manifest} "
              f"(text layer off; payload {src})")
        return

    # boundary-aware split: each cut lands between two non-empty lines.
    n = len(lines)
    cuts = [0]
    while cuts[-1] + TARGET_LINES < n:
        want = cuts[-1] + TARGET_LINES
        cut = None
        for delta in range(BOUNDARY_SLACK):
            for cand in (want + delta, want - delta):
                if not (cuts[-1] < cand < n):
                    continue
                if lines[cand - 1] and lines[cand]:
                    cut = cand
                    break
            if cut is not None:
                break
        if cut is None:
            fail(f"no text-adjacent chunk boundary within "
                 f"{BOUNDARY_SLACK} lines of line {want}")
        cuts.append(cut)
    cuts.append(n)

    chunkdir.mkdir(parents=True, exist_ok=True)
    for old in chunkdir.glob("chunk-*.txt"):
        old.unlink()
    names = []
    for k, (a, b) in enumerate(zip(cuts, cuts[1:])):
        path = chunkdir / f"chunk-{k:03d}.txt"
        path.write_bytes(b"\n".join(lines[a:b]) + b"\n")
        names.append(str(path))

    glued = b"".join((chunkdir / f"chunk-{k:03d}.txt").read_bytes()
                     for k in range(len(names)))
    if glued != normalized:
        fail("chunks do not re-concatenate to the source (splitter bug)")

    maxchars = max((len(ln.decode("utf-8")) for ln in lines), default=0)
    manifest.write_text(
        "% generated by tools/srclayer-split.py - source-layer manifest\n"
        "% (read by srclayer.tex via \\@@input; never committed).\n"
        f"\\def\\srclPayloadFile{{{src}}}\n"
        f"\\def\\srclChunkCount{{{len(names)}}}\n"
        f"\\def\\srclMaxLineChars{{{maxchars}}}\n"
        f"\\def\\srclChunkFiles{{{','.join(names)}}}\n",
        encoding="utf-8")
    print(f"srclayer-split: {len(names)} chunk(s) x <={TARGET_LINES} lines, "
          f"longest line {maxchars} chars, manifest {manifest}")


if __name__ == "__main__":
    main()
