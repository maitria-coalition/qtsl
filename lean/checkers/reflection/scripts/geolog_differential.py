#!/usr/bin/env python3
"""Differential driver for the geolog reader executable.

Usage:
    geolog_differential.py <geolog_read-exe> <fixture-dir> [more dirs...]

For every ``*.geolog`` in each fixture directory, runs the reader and
compares:

* the plain block against ``<stem>.hol.txt`` when present (the
  reference reader's own recorded plain dump, byte-exact), else
  against ``<stem>.oracle.txt`` when the manifest expects OK, else
  against the manifest's expected refusal class (first token);
* the sealed block against ``<stem>.hols.txt`` when present, else
  against the manifest expectation (``OK`` rows must render sealed
  byte-equal to the oracle; ``OK_SEALED_UNSUPPORTED`` rows must refuse
  UNSUPPORTED; refusal rows must refuse in the same class as plain).

Manifest format: TSV with ``# name\tfile\trust_verdict\texpected_hol``
header lines; only ``name`` and ``expected_hol`` are consulted.

Exit status 0 iff every comparison agrees. Prints one TSV row per
check: name, side, expectation source, verdict.
"""

import subprocess
import sys
from pathlib import Path


def load_manifest(d: Path):
    expected = {}
    mf = d / "MANIFEST.tsv"
    if not mf.exists():
        return expected
    for line in mf.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) >= 4:
            expected[parts[0]] = parts[3].strip()
    return expected


def run_reader(exe: Path, files):
    out = subprocess.run(
        [str(exe)] + [str(f) for f in files],
        capture_output=True, text=True, timeout=3600,
    )
    if out.returncode != 0:
        sys.stderr.write(out.stderr)
        raise SystemExit(f"reader exited {out.returncode}")
    blocks = {}
    key = None
    buf = []
    for line in out.stdout.splitlines(keepends=True):
        if line.startswith("### "):
            if key is not None:
                blocks[key] = "".join(buf)
            hdr = line[4:].rstrip("\n")
            path, mode = hdr.rsplit(" ", 1)
            key = (Path(path).stem, mode)
            buf = []
        else:
            buf.append(line)
    if key is not None:
        blocks[key] = "".join(buf)
    return blocks


def klass(text: str) -> str:
    first = text.split("\n", 1)[0]
    return first.split(" ", 1)[0]


def main():
    exe = Path(sys.argv[1])
    rows = []
    ok = True
    for d in map(Path, sys.argv[2:]):
        manifest = load_manifest(d)
        files = sorted(d.glob("*.geolog"))
        blocks = run_reader(exe, files)
        for f in files:
            stem = f.stem
            plain = blocks.get((stem, "plain"), "")
            sealed = blocks.get((stem, "sealed"), "")
            exp = manifest.get(stem)

            # plain side
            hol_txt = d / f"{stem}.hol.txt"
            oracle_txt = d / f"{stem}.oracle.txt"
            if hol_txt.exists():
                good = plain == hol_txt.read_text()
                src = "hol.txt"
            elif exp in ("OK", "OK_SEALED_UNSUPPORTED") and oracle_txt.exists():
                good = plain == oracle_txt.read_text()
                src = "oracle.txt"
            elif exp in ("UNREADABLE", "UNSUPPORTED"):
                good = klass(plain) == exp
                src = f"class:{exp}"
            else:
                # not in the reader manifest and no recorded reader dump:
                # a fixture for a different layer — report, don't judge
                good = None
                src = f"info-only({klass(plain)})"
            rows.append((stem, "plain", src,
                         "match" if good else ("info" if good is None else "MISMATCH")))
            if good is not None:
                ok &= good

            # sealed side
            hols_txt = d / f"{stem}.hols.txt"
            if hols_txt.exists():
                good = sealed == hols_txt.read_text()
                src = "hols.txt"
            elif exp == "OK":
                good = sealed == plain
                src = "sealed=plain"
            elif exp == "OK_SEALED_UNSUPPORTED":
                good = klass(sealed) == "UNSUPPORTED"
                src = "class:UNSUPPORTED"
            elif exp in ("UNREADABLE", "UNSUPPORTED"):
                good = klass(sealed) == exp
                src = f"class:{exp}"
            else:
                good = None
                src = f"info-only({klass(sealed)})"
            rows.append((stem, "sealed", src,
                         "match" if good else ("info" if good is None else "MISMATCH")))
            if good is not None:
                ok &= good

    w = max(len(r[0]) for r in rows)
    for r in rows:
        print(f"{r[0]:<{w}}\t{r[1]}\t{r[2]}\t{r[3]}")
    n_bad = sum(1 for r in rows if r[3] == "MISMATCH")
    print(f"# {len(rows)} checks, {n_bad} mismatches")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
