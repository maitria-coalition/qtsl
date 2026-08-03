#!/usr/bin/env bash
# build.sh — the one verb: build the MAITRIA toolkit book.
#
# Verbs (the bare invocation builds the book):
#   ./build.sh [book] [--refresh-transcripts]
#       build; tool transcripts regenerate first (content-addressed
#       cache — unchanged tools skip; --refresh-transcripts forces).
#   ./build.sh transcripts [args...]
#       just the transcript generator (tools/transcripts.py --help).
#   ./build.sh experiments <target...>
#       delegate to the reproduction spine's make targets in the
#       sibling qtsl-experiments checkout (gymnasium | circuits |
#       semicon | supermartingales | chapter, and their subtargets).
#       Deliberately NOT run by the book build: re-deriving the
#       Experiments chapter's numbers is a choice, per section.
#
# Template: chapters.tex (chapters ride \input). Produces, COMMITTED in this
# directory so the raw public URLs resolve:
#   book.pdf — the typeset book. For agent consumption the PDF carries
#     its own source as an embedded file attachment (srclayer.tex):
#     pdfdetach -list book.pdf; pdfdetach -save 1 book.pdf — the recipe
#     is printed on the title page (white head note) and the final page,
#     and verified by tools/srclayer-gate.py below. (The invisible
#     full-source text layer is switched off — 2026-08-03, iOS Safari
#     crashed on its appended pages; the --attachment-only flag at the
#     splitter call below is the switch.)
#     https://raw.githubusercontent.com/maitria-coalition/qtsl/refs/heads/main/book/book.pdf
#     (also https://maitria.org/book.pdf)
#   book.tex — the ASSEMBLED single-file source (latexpand inlines the
#     chapter \input lines and the bibliography, so the artefact is
#     self-contained; the same bytes the PDF carries)
#     https://raw.githubusercontent.com/maitria-coalition/qtsl/refs/heads/main/book/book.tex
#     (also https://maitria.org/book.tex)
# Intermediate state stays in build/ (gitignored).
#
# By default the build INSTALLS the artefacts beside the sources without
# committing them: source changes land alone, and the repository's rebuild
# automation assembles + commits ("book: rebuild (assembled)") once the
# sources are on the main branch — so parallel edits never serialize
# behind one another's typesetting runs. BOOK_COMMIT=1 opts in to the
# old self-commit (iff content changed; the committed artefacts embed the
# revision they were built FROM, one commit behind the commit carrying
# them). BOOK_SKIP_COMMIT=1 (legacy) forces the skip even with
# BOOK_COMMIT set. With BOOK_COMMIT on a dirty tree the artefact commit
# can land AHEAD of the source edits it was built from — commit sources
# first.
#
# Deterministic: SOURCE_DATE_EPOCH is pinned (env override > last git commit
# touching anything EXCEPT the built artefacts — so artefact commits don't
# perturb the next build — > the fixed scaffold date below) and the preamble
# sets an empty \pdftrailerid — two builds of the same sources are
# byte-identical. Typesetting runs UNTAGGED to the cross-ref fixpoint,
# then emits the TAGGED artefact (the recipe comment at the latexmk
# stage tells the story); every build starts cold (-gg): correctness
# over incrementality at this size, immune to mtime-granularity skips.
set -euo pipefail
cd "$(dirname "$0")"

# stage timestamps: one line per stage boundary on stderr, epoch + elapsed —
# so any log of this build (postmerge runs especially) answers "where did
# the time go" without external instrumentation.
BUILD_T0=$(date +%s)
BUILD_TPREV=$BUILD_T0
bstamp() {
  local now; now=$(date +%s)
  echo "build: [t+$((now - BUILD_T0))s] (stage took $((now - BUILD_TPREV))s) $1" >&2
  BUILD_TPREV=$now
}

# locate a sibling checkout: env override, beside this repository, or
# beside the primary checkout (git worktrees lack the siblings).
sibling() {
  local name="$1" env_key cand
  env_key="BOOK_TOOL_$(echo "$name" | tr '[:lower:]-' '[:upper:]_')"
  if [[ -n "${!env_key:-}" ]]; then echo "${!env_key}"; return; fi
  cand="$(cd .. && pwd)/../$name"
  if [[ -d "$cand" ]]; then echo "$cand"; return; fi
  local common; common=$(git rev-parse --git-common-dir 2>/dev/null) || true
  if [[ -n "$common" ]]; then
    cand="$(dirname "$common")/../$name"
    if [[ -d "$cand" ]]; then echo "$cand"; return; fi
  fi
  return 1
}

REFRESH=""
VERB="book"
if [[ $# -gt 0 ]]; then
  case "$1" in
    book) shift ;;
    transcripts) shift; exec python3 tools/transcripts.py "$@" ;;
    experiments)
      shift
      EXP=$(sibling qtsl-experiments) || {
        echo "experiments: no qtsl-experiments checkout found (clone it beside this repository, or set BOOK_TOOL_QTSL_EXPERIMENTS)" >&2
        exit 1
      }
      exec make -C "$EXP" "$@" ;;
    --refresh-transcripts) ;;  # handled below
    *) echo "usage: build.sh [book|transcripts|experiments] [args]" >&2; exit 2 ;;
  esac
fi
for arg in "$@"; do
  [[ "$arg" == "--refresh-transcripts" ]] && REFRESH="--force"
done

# BOOK_UNTAGGED=1: health-build mode — stop after the untagged
# ref-fixpoint passes, skipping the tagged emission stage entirely (the
# fixpoint passes are ALWAYS untagged; see the typesetting recipe below).
# Tagging multiplies lualatex pass cost ~10x (measured 2026-07-29: 423s
# vs 44s per pass, same content), so this is the cheap "does the tip
# typeset green incl. gates" verb. An untagged artefact must never reach
# the committed/public copies: BOOK_COMMIT is refused alongside it, and
# the install step is skipped too (the artefact stays in build/, never
# overwriting the in-tree tagged copy).
if [[ -n "${BOOK_UNTAGGED:-}" ]]; then
  if [[ -n "${BOOK_COMMIT:-}" && -z "${BOOK_SKIP_COMMIT:-}" ]]; then
    echo "build: BOOK_UNTAGGED=1 refuses BOOK_COMMIT=1 (an untagged artefact must never be committed)" >&2
    exit 2
  fi
  echo "build: BOOK_UNTAGGED — tagged emission skipped (health-build mode; committed artefacts stay tagged)" >&2
fi

# hermetic: stale aux state in build/ can settle on a subtly different
# fixpoint (the historic "stable 2-byte cold/warm PDF diff" — diagnosed
# 2026-07-29 as hyperxmp's self-referential <prism:byteCount>, which
# each pass reads from the PREVIOUS run's pdf on disk) — every build
# starts cold.
OUT=build
rm -rf "$OUT"
mkdir -p "$OUT"

SCAFFOLD_EPOCH=1784505600  # 2026-07-19T16:00:00Z, the scaffold date
if [[ -z "${SOURCE_DATE_EPOCH:-}" ]]; then
  # exclude the committed artefacts (and the build-owned generated/
  # fragments, which land in artefact commits): an artefact commit must
  # not shift the epoch, or every rebuild would differ and re-commit
  # forever.
  SOURCE_DATE_EPOCH=$(git log -1 --format=%ct -- ':(top)' \
    ':(top,exclude)book/book.pdf' ':(top,exclude)book/book.tex' \
    ':(top,exclude)book/generated' \
    2>/dev/null || true)
  [[ -n "$SOURCE_DATE_EPOCH" ]] || SOURCE_DATE_EPOCH=$SCAFFOLD_EPOCH
fi
export SOURCE_DATE_EPOCH

# spelling gate: chapter prose holds the settled spellings (term-of-art
# "judgment"; tagged discretionary "judgement" allowed) — fails fast,
# before any typesetting. See tools/spell-gate.py.
python3 tools/spell-gate.py
bstamp 'spell-gate done'

# Mini-Fab lock-step gate: the SDCPN tables fragment (shared with
# external reports by semantic fold; see its header comment) and the
# chapter prose that cites its census must agree — a re-sync that
# moved one surface but not the other fails here, fast, before any
# typesetting. See tools/minifab-lockstep-gate.py.
python3 tools/minifab-lockstep-gate.py
bstamp 'minifab lock-step gate done'

# transcripts: regenerate before typesetting (cached — see
# tools/transcripts.py; absent tool trees warn and keep the committed
# fragments, so a lone clone of this repository still builds).
# BOOK_SKIP_TRANSCRIPTS=1 skips the step entirely.
if [[ -z "${BOOK_SKIP_TRANSCRIPTS:-}" ]]; then
  python3 tools/transcripts.py $REFRESH
fi
bstamp 'transcripts done'

# lean-cone appendix: re-derive the citation census from the chapters
# and the lean/ trees (strict: a Lean rename landing without a matching
# book edit fails the build here, loudly, instead of silently thinning
# the appendix).
python3 tools/lean-cone.py --strict
bstamp 'lean-cone done'

# the Experiments chapter \inputs its sections from the sibling
# qtsl-experiments checkout; resolve it (worktree-safe) and record the
# provenance pin. The pin's chapter-tree hash is a content hash (a
# history rewrite that preserves content preserves it); a change means
# the book just absorbed new experiments content — visible in the diff.
EXP=$(sibling qtsl-experiments) || {
  echo "build: no qtsl-experiments checkout found — the Experiments chapter needs the sibling (clone it beside this repository, or set BOOK_TOOL_QTSL_EXPERIMENTS)" >&2
  exit 1
}
PIN=generated/experiments-pin.txt
mkdir -p generated
{
  echo "# qtsl-experiments provenance for the committed book artefacts."
  echo "# chapter-tree is git's content hash of chapter/ (survives history rewrites)."
  echo "chapter-tree=$(git -C "$EXP" rev-parse HEAD:chapter)"
  echo "commit=$(git -C "$EXP" log -1 --format='%h %cs')"
  if [[ -n "$(git -C "$EXP" status --porcelain -- chapter 2>/dev/null)" ]]; then
    echo "dirty=chapter/ had uncommitted changes at build time"
  fi
} > "$PIN.new"
if [[ ! -f "$PIN" ]]; then
  echo "build: experiments pin recorded (first build):" >&2
  cat "$PIN.new" >&2
elif ! cmp -s "$PIN" "$PIN.new"; then
  echo "build: experiments pin updated (chapter content moved):" >&2
  diff "$PIN" "$PIN.new" >&2 || true
fi
mv "$PIN.new" "$PIN"
bstamp 'experiments pin done'

# the typesetting recipe (adopted 2026-07-29): tagging is left out
# until the cross-ref fixpoint, then enabled for the emitted artefact.
#
#   1. UNTAGGED ref-fixpoint — latexmk's own rerun logic drives cheap
#      untagged passes (\BOOKUNTAGGED via -usepretex; ~44s/pass vs 423s
#      tagged, measured 2026-07-29) until cross-refs/ToC/bib settle.
#      -gg = full cold rebuild: correctness over incrementality at this
#      size, and immune to mtime-granularity skips.
#   2. TAGGED emission — one forced pass-set (-g) re-typesets with
#      tagging on, reusing the fixpoint bbl/toc; latexmk's own rerun
#      analysis drives the iterations it needs (measured 2026-07-29:
#      the tagged aux takes 3 iterations to settle even from the
#      untagged fixpoint — tagging perturbs aux CONTENT, not just
#      pass cost), then the metadata audit below verifies the result.
#
# history: this replaces a pair of always-TAGGED -gg invocations whose
# second (35-50% of every build) existed only to stabilize hyperxmp's
# self-referential <prism:byteCount> — to a STALE value. Under
# \DocumentMetadata that field is not emitted at all (verified
# 2026-07-29: the tagged XMP carries pageCount + complianceProfile
# only), so the pair's entire rationale is extinct for the artefacts
# this script commits; the audit keeps it honest if it ever returns.
#
# tier note (standing decision, 2026-07-29): even at ~10 minutes the
# book build stays ASYNC (health builds + rebuild automation), never a
# blocking pre-merge gate — by decision, not by cost; a faster build is
# not an invitation to promote it.
#
# lualatex since the rule catalogue shipped: its quoted Lean sources
# carry mathematical Unicode (fontspec + a mono fallback chain, loaded
# by the catalogue's generated preamble).
# -jobname=book keeps the artefact names while the template is chapters.tex.
export TEXINPUTS="$EXP/chapter:${TEXINPUTS:-}"
# max_repeat raised from latexmk's default 5 (landed with the spec
# chapter, 2026-07-29): the book's from-scratch pass requirement crossed
# the default cap — a sixth pass converged byte-stable (content growth,
# not oscillation; latexmk still fail-fasts on genuine flip-flop via its
# changed-back detection). Composed into LMK so the recipe's single -gg
# untagged fixpoint inherits the raise.
LMK=(-lualatex -e '$max_repeat=9' -interaction=nonstopmode -halt-on-error -jobname=book -outdir="$OUT")
latexmk "${LMK[@]}" -gg -usepretex='\def\BOOKUNTAGGED{1}' chapters.tex > "$OUT/latexmk-1.log"
bstamp 'latexmk untagged ref-fixpoint done'

# assemble the single-file source NOW — the fixpoint's bbl exists, and
# nothing later perturbs it. The assembled file is at once the
# installed/served book.tex and the PDF's book.tex attachment: one set
# of bytes, two channels (the mechanism lives in srclayer.tex; a third
# channel — the invisible source layer — is switched off, see the
# splitter call below). latexpand drops comments preceding
# \documentclass, and agents fetching the TeX must see the license
# immediately — so the header is restored mechanically from the
# source's own leading comment block.
latexpand --biber "$OUT/book.bbl" chapters.tex > "$OUT/book.tex.body"
# latexpand --biber inlines the bbl once per \addbibresource (three
# identical filecontents* blocks); keep the first, drop the rest.
python3 - "$OUT/book.tex.body" <<'PYEOF'
import sys, re
p = sys.argv[1]
s = open(p).read()
pat = re.compile(r"\\begin\{filecontents\*\}\{[^}]*book\.bbl\}.*?\\end\{filecontents\*\}\n?", re.S)
blocks = pat.findall(s)
if len(blocks) > 1:
    first = blocks[0]
    s = pat.sub("", s)
    # re-insert the single copy where the first block began
    idx = len(s)  # fallback: append before \begin{document}
    m = re.search(r"\\begin\{document\}", s)
    if m: idx = m.start()
    s = s[:idx] + first + s[idx:]
open(p, "w").write(s)
print(f"bbl blocks: {len(blocks)} -> 1", file=sys.stderr)
PYEOF
sed -n '1,/^\\documentclass/{/^\\documentclass/!p}' chapters.tex > "$OUT/book.tex.head"
cat "$OUT/book.tex.head" "$OUT/book.tex.body" > "$OUT/book.tex"
rm -f "$OUT/book.tex.head" "$OUT/book.tex.body"
bstamp 'book.tex assembled'

if [[ -z "${BOOK_UNTAGGED:-}" ]]; then
  # source-attachment prep (srclayer.tex): normalize the assembled
  # source (trailing blanks — token-identical by TeX's own line-reading
  # rules) and write the manifest that activates the appendix.
  # --attachment-only (2026-08-03) is THE srclayer off-switch: the
  # invisible full-source text layer crashed iOS Safari on
  # maitria.org/book.pdf (its appended source pages are enormous page
  # boxes — rendered as a vast black surface, then the tab dies), so
  # only the book.tex attachment channel ships. Drop the flag to
  # re-enable the layer if PDF renderers improve — splitter,
  # srclayer.tex, and the gate all re-arm from the manifest.
  python3 tools/srclayer-split.py --attachment-only \
    "$OUT/book.tex" "$OUT/srcchunks" \
    "$OUT/srclayer-manifest.tex" "$OUT/srclfonts"
  # the attachment's /Params ModDate reads the payload's mtime — pin it
  # to the build epoch so double builds stay byte-identical.
  touch -d "@$SOURCE_DATE_EPOCH" "$OUT/book.tex"
  # one cheap untagged pass with the appendix present: the appendix
  # moves the physical page total, and body footers read
  # \pageref{LastPage} — settle that aux delta at untagged-pass prices
  # instead of inside the ~10x costlier tagged stage.
  latexmk "${LMK[@]}" -g -usepretex='\def\BOOKUNTAGGED{1}' chapters.tex > "$OUT/latexmk-1b.log"
  bstamp 'srclayer settle pass done'

  latexmk "${LMK[@]}" -g chapters.tex > "$OUT/latexmk-2.log"
  bstamp 'latexmk tagged emission done'
  # metadata audit: a self-referential <prism:byteCount> instance, if
  # one ever reappears, must equal the true file size. It lives in the
  # XMP metadata stream, which the tagged pipeline COMPRESSES — a raw
  # byte-grep cannot see it, so read the real stream. Absent instance
  # (the current tagged regime) passes with a note; a stale value
  # fails loudly — the repair would be one more -g pass-set here.
  python3 - "$OUT/book.pdf" <<'PYEOF'
import os, re, sys
path = sys.argv[1]
try:
    import pikepdf
except ImportError:
    print("byteCount audit: pikepdf unavailable - skipped", file=sys.stderr)
    sys.exit(0)
with pikepdf.open(path) as pdf:
    md = pdf.Root.get("/Metadata")
    xmp = md.read_bytes().decode("utf-8", "replace") if md is not None else ""
m = re.search(r'<prism:byteCount>\s*(\d+)|prism:byteCount="(\d+)"', xmp)
if not m:
    print("byteCount audit: ok - no prism:byteCount instance "
          "(expected under DocumentMetadata)")
    sys.exit(0)
claimed = int(m.group(1) or m.group(2))
actual = os.path.getsize(path)
if claimed != actual:
    print(f"byteCount audit: FAIL - XMP claims {claimed}, file is "
          f"{actual} bytes (stale self-reference; the emission stage "
          "needs a second -g pass-set)", file=sys.stderr)
    sys.exit(1)
print(f"byteCount audit: ok - {claimed} = file size")
PYEOF
fi

# glyph gate: lualatex exits 0 even when a font drops a glyph; a page that
# silently loses characters is worse than a failed build.
if grep -q 'Missing character' "$OUT/book.log"; then
  echo "glyph gate: 'Missing character' in $OUT/book.log — glyphs were dropped:" >&2
  grep 'Missing character' "$OUT/book.log" | sort -u | head -20 >&2
  exit 1
fi

# ToC-link gate: hyperref/tagging interactions can silently VANISH the
# table of contents' link annotations (a dead-link checker cannot see
# links that are absent) — counts Link annots over the front page range
# and requires the structure tree to survive. See tools/toc-gate.py;
# BOOK_SKIP_TOC_GATE=1 skips (minimal environments without pikepdf).
# A BOOK_UNTAGGED health build has no structure tree BY DESIGN — its
# links check stays live, the tagged check is waived for it only.
if [[ -z "${BOOK_SKIP_TOC_GATE:-}" ]]; then
  BOOK_TOC_EXPECT_UNTAGGED="${BOOK_UNTAGGED:-}" python3 tools/toc-gate.py "$OUT/book.pdf"
fi

# srclayer gate: the PDF's source-carrying channel verifies against
# the assembled source — the book.tex attachment detaches
# byte-identically under the exact printed incantation, and the recipe
# appears on both pages that print it (title-page head note + final
# page). The gate reads its mode from the manifest, so the full layer
# checks re-arm automatically if --attachment-only is ever dropped.
# A BOOK_UNTAGGED health build ships no source appendix (no
# manifest), so the gate is full-build-only, like the tagged emission.
if [[ -z "${BOOK_UNTAGGED:-}" ]]; then
  python3 tools/srclayer-gate.py "$OUT/book.pdf" "$OUT/book.tex" \
    "$OUT/srclayer-manifest.tex"
fi
bstamp 'gates done'

# install the artefacts beside the sources and commit iff content changed
# (the batched-commit policy made mechanical: a commit happens exactly when
# public-facing content changes). Deliberately NOT a pre-commit hook — a
# hook building 400+ pages of LaTeX on every commit would be miserable.
# A BOOK_UNTAGGED health build installs nothing: its artefact stays in
# build/, never overwriting the in-tree tagged copy.
if [[ -n "${BOOK_UNTAGGED:-}" ]]; then
  echo "BOOK_UNTAGGED: artefacts left in $OUT/, not installed (health build)"
  echo "built (untagged, uninstalled): $OUT/book.pdf ($(stat -c%s "$OUT/book.pdf")B)  [SOURCE_DATE_EPOCH=$SOURCE_DATE_EPOCH]"
  exit 0
fi
cp "$OUT/book.pdf" book.pdf
cp "$OUT/book.tex" book.tex
# the commit sweeps generated/ too (transcript fragments, stamps, the
# experiments pin): those paths are owned by this build, and a fragment
# regenerated in this run belongs in the same commit as the artefacts
# typeset from it.
COMMIT_PATHS=(book.pdf book.tex generated)
if [[ -n "${BOOK_SKIP_COMMIT:-}" || -z "${BOOK_COMMIT:-}" ]]; then
  echo "artefacts installed, not committed (the default: source changes land"
  echo "  alone and the repository's rebuild automation assembles + commits;"
  echo "  set BOOK_COMMIT=1 to commit in-place)"
elif [[ -n "$(git status --porcelain -- "${COMMIT_PATHS[@]}")" ]]; then
  # pathspec commit: only these paths, regardless of what else is
  # staged (concurrent legs' in-flight work is never swept in). The add is
  # explicit-paths-only; it exists so a first-ever (untracked) book.pdf is
  # visible to the pathspec commit.
  git add -- "${COMMIT_PATHS[@]}"
  git commit -q -m "book: rebuild (assembled)" -- "${COMMIT_PATHS[@]}"
  echo "committed: book.pdf + book.tex + generated/ ($(git log -1 --format=%h))"
else
  echo "artefacts unchanged: nothing to commit"
fi

echo "built: book.pdf ($(stat -c%s book.pdf)B), book.tex ($(stat -c%s book.tex)B)  [SOURCE_DATE_EPOCH=$SOURCE_DATE_EPOCH]"
