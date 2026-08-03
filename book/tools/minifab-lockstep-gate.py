#!/usr/bin/env python3
"""Mini-Fab lock-step gate: the SDCPN tables fragment and its chapter
must cite the same certified census.

The fragment (chapters/minifab-sdcpn-tables.tex) is shared with
external reports by semantic fold (its header comment carries the
sync discipline), and the chapter prose cites the same counts in
running text. A re-sync or a campaign delta that moved one surface
but not the other would ship a chapter contradicting its own table
--- the class of defect this gate exists to refuse (specimen: a
112-count chapter around a 150-row table). Checks, all cheap and
source-level:

  1. the fragment's certificate-table header count (``$N$ footprint
     rows'') exists, exactly once;
  2. every ``$N$ footprint sequents'' count in the chapter equals it;
  3. the fragment's certificate table has as many certificate rows as
     the chapter's ``<number-word> plated certificates'' /
     ``<number-word> certificates below'' prose claims.

Exit 0 on agreement; exit 1 with the disagreement named.
"""

import re
import sys

FRAGMENT = "chapters/minifab-sdcpn-tables.tex"
CHAPTER = "chapters/qtsl-minifab-example.tex"

WORDS = {
    "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
    "thirteen": 13, "fourteen": 14, "fifteen": 15, "sixteen": 16,
}


def fail(msg: str) -> None:
    print(f"minifab lock-step gate: FAIL - {msg}", file=sys.stderr)
    sys.exit(1)


frag = open(FRAGMENT, encoding="utf-8").read()
chap = open(CHAPTER, encoding="utf-8").read()

# 1. the fragment's header count.
header_counts = re.findall(r"\$(\d+)\$ footprint\s+rows,\s*species", frag)
if len(header_counts) != 1:
    fail(
        f"expected exactly one '$N$ footprint rows, species' header in "
        f"{FRAGMENT}, found {len(header_counts)}"
    )
frag_count = int(header_counts[0])

# 2. the chapter's running-text counts.
chap_counts = [int(n) for n in re.findall(r"\$(\d+)\$ footprint sequents", chap)]
if not chap_counts:
    fail(f"no '$N$ footprint sequents' citation found in {CHAPTER}")
bad = sorted({n for n in chap_counts if n != frag_count})
if bad:
    fail(
        f"census count mismatch: fragment header says {frag_count}, "
        f"chapter cites {bad} (all chapter citations: {chap_counts}) - "
        f"the two surfaces move in the same commit"
    )

# 3. certificate-roster size: fragment table rows vs chapter prose.
cert_block = re.search(
    r"species\s*\n?\\texttt\{HCert\}.*?\\midrule(.*?)\\bottomrule",
    frag,
    re.S,
)
if not cert_block:
    fail(f"could not locate the certificates table body in {FRAGMENT}")
# a certificate row is a top-level table line: name & family & fold & ...
frag_certs = len(
    re.findall(r"^[a-zA-Z][^&\n]*&", cert_block.group(1), re.M)
)
prose_words = re.findall(
    r"\b(%s)\b(?:\s+plated)?\s+certificates\b" % "|".join(WORDS),
    chap,
)
if not prose_words:
    fail(f"no '<number-word> certificates' prose citation found in {CHAPTER}")
# only citations of THIS roster count: those in the exact-certificates
# section cite the plated roster; the fluid lane's own certificate
# counts are out of scope, so restrict to the section span.
exact_span = chap[
    chap.find(r"\section{The combinatorial certificates}"):
    chap.find(r"\section{The fluid certificates")
]
span_words = re.findall(
    r"\b(%s)\b(?:\s+plated)?\s+certificates\b" % "|".join(WORDS),
    exact_span,
)
bad_words = sorted({w for w in span_words if WORDS[w] != frag_certs})
if bad_words:
    fail(
        f"certificate-roster mismatch: fragment table lists {frag_certs} "
        f"certificates, chapter prose says {bad_words}"
    )

print(
    f"minifab lock-step gate: ok - {frag_count} footprint rows, "
    f"{frag_certs} certificates, fragment and chapter agree"
)
