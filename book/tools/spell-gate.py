#!/usr/bin/env python3
"""spell-gate: hold the book's chapter prose to its settled spellings.

For each (name, pattern, tag) in LOSERS, any match in chapter PROSE
fails the build. Not gated: verbatim environments (Lean/HOL extracts,
listings, and fvextra Verbatim transcript blocks keep their bytes —
tool output is quoted, never respelled), and lines carrying the
allowlist tag —
written as a TeX comment on the match's own line or the line above:

    ... a judgement call % spell-ok: judgement (discretionary sense)

House ruling behind the first entry: the formal term of art is
"judgment" (judgment forms, formation judgments, emitted judgments);
"judgement" is reserved for the informal, discretionary sense and must
carry the tag. The rule-catalogue chapter is generated (bl-book): if
this gate fires on it after a regeneration, fix the generator sources
and re-emit — do not tag your way around a source-side regression.

Exit 0 clean; exit 1 with a hit list.
"""
import re
import sys
from pathlib import Path

# (human name, compiled pattern, allowlist tag)
LOSERS = [
    ("judgement (formal-sense loser; ruled spelling is 'judgment')",
     re.compile(r"[Jj]udgement"),
     "spell-ok: judgement"),
]

# environments whose bodies keep their bytes (extracts, listings)
VERBATIM_ENVS = ("leansrc", "holsrc", "receipttable", "lstlisting", "verbatim", "Verbatim")
BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(VERBATIM_ENVS) + r")\*?\}")
END_RE = re.compile(r"\\end\{(" + "|".join(VERBATIM_ENVS) + r")\*?\}")


def gate_file(path: Path) -> list[str]:
    hits = []
    in_verbatim = False
    prev_line = ""
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        boundary = BEGIN_RE.search(line) or END_RE.search(line)
        if not in_verbatim and not boundary:
            for name, pat, tag in LOSERS:
                if pat.search(line) and tag not in line and tag not in prev_line:
                    hits.append(f"{path}:{lineno}: {name}\n    {line.strip()}")
        if BEGIN_RE.search(line):
            in_verbatim = True
        if END_RE.search(line):
            in_verbatim = False
        prev_line = line
    return hits


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    hits = []
    for tex in sorted((root / "chapters").glob("*.tex")):
        hits.extend(gate_file(tex))
    if hits:
        print(f"spell-gate: {len(hits)} disallowed spelling(s) in chapter prose:",
              file=sys.stderr)
        for h in hits:
            print(h, file=sys.stderr)
        print("spell-gate: fix the spelling, or tag a genuine discretionary-sense"
              " use with '% spell-ok: judgement'.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
