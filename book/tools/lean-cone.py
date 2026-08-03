#!/usr/bin/env python3
"""lean-cone.py — regenerate the book's Lean-cone appendix.

The appendix (generated/lean-cone.tex, \\input by chapters/lean-cone.tex)
lists, per book chapter, every Lean declaration the chapter cites in
\\texttt{...}, together with the declaration's statement as written in
the repository's lean/ trees. The census re-derives from the sources on
every run, so the appendix cannot drift from the tree it describes.

Usage:  tools/lean-cone.py [--strict]
        (from anywhere; paths resolve relative to this file)

--strict: exit nonzero if any result-shaped citation fails to resolve
against the lean/ trees. The build runs in strict mode so that a rename
landing in lean/ without a matching book edit fails the build loudly
instead of silently thinning the appendix.

What counts as a citation:
  * a \\texttt{...} whose content looks like a Lean declaration name
    (contains "_", ".", or an internal case transition, e.g.
    checkPf_sound_frag, SuFunctor.Plain.CheckerFace, qBasin_sound);
  * dotted CamelCase paths are tried both as module paths (files) and
    as namespaced declarations;
  * names ending in .lean are file citations (existence-checked only);
    .sml citations belong to the HOL4 layer and are out of scope here.

Statements are printed signature-level: a theorem or definition up to
its top-level ":=", a structure/inductive/class header up to its
"where". Surrounding context (open, variable, universe) lives in the
cited file; the appendix names the file and line for every entry.
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

BOOK = Path(__file__).resolve().parent.parent
REPO = BOOK.parent
OUT = BOOK / "generated" / "lean-cone.tex"

# The trees the book's trust story binds to, in resolution-priority
# order; the remaining lean/ directories are indexed too, so that a
# citation resolving only outside the primary trees is reported rather
# than misread as stale.
PRIMARY_TREES = ["su-functor", "qtsl-aux", "qtsl", "pointfree", "checkers"]
SECONDARY_TREES = ["double-cat", "optional-sampling", "su-functor-legacy"]

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive",
    "class", "instance", "opaque", "axiom",
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
    r"([A-Za-z_À-῿][A-Za-z0-9_'.À-῿₀-₟]*)"
)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.À-῿]+)")
END_RE = re.compile(r"^\s*end\b\s*([A-Za-z0-9_.À-῿]*)")
SECTION_RE = re.compile(r"^\s*section\b")

# Suffixes strong enough to mark a non-resolving citation as a stale
# Lean reference (rather than, say, a geolog relation name that merely
# looks Lean-shaped). Deliberately narrower than the resolver itself.
LEAN_SUFFIX_HINTS = (
    "_sound", "_iff", "_complete", "_holds", "_soundness", "soundness",
    "_of_wf", "_admissible",
)


def strip_comments(text):
    """Remove Lean block and line comments, PRESERVING newlines so that
    line numbers in the cleaned text align 1:1 with the raw file."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        ch = text[i]
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            if ch == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def collapse_blank_runs(s, keep=1):
    """Collapse runs of blank lines in an emitted excerpt to at most
    `keep`. strip_comments PRESERVES newlines (line-number alignment),
    so a stripped doc comment leaves a hole of blanks in the excerpt —
    a typographic wart in the printed listing, and runs of five or more
    blank lines cannot ride the book's source layer (srclayer.tex's
    blank-run ceiling; tools/srclayer-split.py refuses them)."""
    out, run = [], 0
    for ln in s.split("\n"):
        if ln.strip() == "":
            run += 1
            if run <= keep:
                out.append("")
        else:
            run = 0
            out.append(ln)
    return "\n".join(out)


class Decl:
    __slots__ = ("bare", "ns", "kind", "file", "line", "primary")

    def __init__(self, bare, ns, kind, file, line, primary):
        self.bare, self.ns, self.kind = bare, ns, kind
        self.file, self.line, self.primary = file, line, primary


def index_lean_trees():
    """Map bare declaration name -> [Decl]."""
    index = defaultdict(list)
    file_lines = {}
    for tree, primary in [(t, True) for t in PRIMARY_TREES] + [
        (t, False) for t in SECONDARY_TREES
    ]:
        root = REPO / "lean" / tree
        if not root.is_dir():
            continue
        for f in sorted(root.rglob("*.lean")):
            raw = f.read_text(encoding="utf-8", errors="replace")
            clean = strip_comments(raw).split("\n")
            file_lines[f] = clean  # aligned 1:1 with the raw lines
            ns_stack = []
            for lineno, line in enumerate(clean, start=1):
                m = NS_RE.match(line)
                if m:
                    ns_stack.extend(m.group(1).split("."))
                    continue
                if SECTION_RE.match(line):
                    ns_stack.append(None)  # anonymous scope marker
                    continue
                m = END_RE.match(line)
                if m:
                    name = m.group(1)
                    if name:
                        for comp in reversed(name.split(".")):
                            if ns_stack and ns_stack[-1] == comp:
                                ns_stack.pop()
                    else:
                        if ns_stack and ns_stack[-1] is None:
                            ns_stack.pop()
                    continue
                m = DECL_RE.match(line)
                if m:
                    kind, name = m.group(1), m.group(2)
                    parts = name.split(".")
                    bare = parts[-1]
                    ns = [c for c in ns_stack if c is not None] + parts[:-1]
                    index[bare].append(
                        Decl(bare, tuple(ns), kind, f, lineno, primary)
                    )
    return index, file_lines


BRACKETS = {"(": 1, "[": 1, "{": 1, "⟨": 1, "⦃": 1, ")": -1, "]": -1,
            "}": -1, "⟩": -1, "⦄": -1}


def extract_statement(lines, start, kind, max_lines=40):
    """Signature-level statement from lines[start-1:]."""
    depth = 0
    collected = []
    for k in range(start - 1, min(len(lines), start - 1 + max_lines)):
        line = lines[k].rstrip()
        i = 0
        while i < len(line):
            ch = line[i]
            if ch in BRACKETS:
                depth += BRACKETS[ch]
            elif depth == 0 and line.startswith(":=", i):
                collected.append(line[:i].rstrip())
                return "\n".join(collected).rstrip(), True
            elif (depth == 0
                  and kind not in ("theorem", "lemma")
                  and re.match(r"\bwhere\b", line[i:])):
                collected.append(line[:i].rstrip() + " where …")
                return "\n".join(collected).rstrip(), True
            i += 1
        collected.append(line.rstrip())
    return "\n".join(collected).rstrip(), False


TEXTTT_RE = re.compile(r"\\texttt\{")


def texttt_contents(text):
    """Yield \\texttt{...} contents, tolerating one brace-nesting level."""
    for m in TEXTTT_RE.finditer(text):
        i = m.end()
        depth = 1
        buf = []
        while i < len(text) and depth > 0:
            ch = text[i]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    break
            if depth > 0:
                buf.append(ch)
            i += 1
        yield "".join(buf)


def deescape(s):
    s = re.sub(r"\\textquotesingle\s*", "'", s)
    s = re.sub(r"\\textbackslash\s*", "\\\\", s)
    for esc, plain in [("\\_", "_"), ("\\&", "&"), ("\\%", "%"),
                       ("\\#", "#"), ("\\$", "$"), ("\\{", "{"),
                       ("\\}", "}")]:
        s = s.replace(esc, plain)
    # a nested \texttt (author typo tolerated in the sweep)
    s = s.replace("\\texttt{", "").replace("}", "") if "\\texttt" in s else s
    return s.strip()


IDENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_'.₀-₟]*$")


def lean_shaped(c):
    return "_" in c or "." in c or re.search(r"[a-z][A-Z]", c)


def module_path_like(c):
    parts = c.split(".")
    return len(parts) > 1 and all(p[:1].isupper() for p in parts)


def chapters_in_order():
    """[(file, title, label)] in book order, nested inputs folded in."""
    main = (BOOK / "chapters.tex").read_text(encoding="utf-8")
    # drop comment lines so the held-out appendix stub is not swept
    main = "\n".join(l for l in main.split("\n") if not l.lstrip().startswith("%"))
    order = []
    for m in re.finditer(r"\\input\{(chapters/[^}]+)\}", main):
        path = BOOK / (m.group(1) + ".tex")
        if not path.exists():
            path = BOOK / m.group(1)
        if not path.exists() or path.name == "lean-cone.tex":
            continue
        text = path.read_text(encoding="utf-8")
        tm = re.search(r"\\chapter(?:\[[^\]]*\])?\{([^}]*)\}", text)
        title = tm.group(1) if tm else path.stem
        lm = re.search(r"\\label\{(ch:[^}]*)\}", text)
        label = lm.group(1) if lm else None
        # fold one level of nested \input into the parent chapter
        for n in re.finditer(r"\\input\{([^}]+)\}", text):
            sub = BOOK / (n.group(1) + ".tex")
            if not sub.exists():
                sub = BOOK / n.group(1)
            if sub.exists() and sub != path:
                text += "\n" + sub.read_text(encoding="utf-8")
        order.append((path, title, label, text))
    return order


def tex_tt(s):
    for ch, rep in [("_", "\\_"), ("#", "\\#"), ("%", "\\%"),
                    ("&", "\\&"), ("$", "\\$"), ("{", "\\{"),
                    ("}", "\\}")]:
        s = s.replace(ch, rep)
    return s


def main():
    strict = "--strict" in sys.argv[1:]
    index, file_lines = index_lean_trees()
    chapters = chapters_in_order()

    listed = {}            # bare-or-qualified name -> chapter label listed under
    sections = []
    unresolved = []        # (chapter, citation)
    outside = []           # (chapter, citation, tree) resolved outside primary
    total_entries = 0

    for path, title, label, text in chapters:
        seen_here = []
        repeats = []
        modules = []
        for raw in texttt_contents(text):
            c = deescape(raw)
            if c.endswith(".lean") or c.endswith("/"):
                continue  # file/tree citations: existence handled below
            if not IDENT_RE.match(c) or not lean_shaped(c):
                continue
            if c in listed:
                if c not in repeats and listed[c] != title:
                    repeats.append(c)
                continue
            if any(c == s[0] for s in seen_here):
                continue
            parts = c.split(".")
            bare, quals = parts[-1], tuple(parts[:-1])
            cands = [d for d in index.get(bare, [])
                     if not quals or d.ns[-len(quals):] == quals]
            if not cands and module_path_like(c):
                hit = None
                for tree in PRIMARY_TREES + SECONDARY_TREES:
                    stem = REPO / "lean" / tree / "/".join(parts)
                    if stem.with_suffix(".lean").exists() or stem.is_dir():
                        hit = stem
                        break
                if hit:
                    modules.append((c, hit))
                    listed[c] = title
                    continue
            if not cands:
                if module_path_like(c) or any(
                        c.endswith(h) for h in LEAN_SUFFIX_HINTS):
                    unresolved.append((title, c))
                continue
            primaries = [d for d in cands if d.primary]
            d = (primaries or cands)[0]
            if not primaries:
                outside.append((title, c, d.file.relative_to(REPO)))
            stmt, ok = extract_statement(file_lines[d.file], d.line, d.kind)
            stmt = collapse_blank_runs(stmt)
            seen_here.append((c, d, stmt, ok, len(cands)))
            listed[c] = title

        if not (seen_here or repeats or modules):
            continue
        body = []
        body.append(f"\\section{{{title}}}")
        if label:
            body.append(f"Citations from Chapter~\\ref{{{label}}}.")
        body.append("")
        for c, d, stmt, ok, ncand in seen_here:
            rel = d.file.relative_to(REPO)
            ns_disp = ".".join(d.ns)
            head = "\\par\\medskip\\noindent{\\small "
            if ns_disp:
                head += f"\\texttt{{{tex_tt(ns_disp)}.}}"
            head += f"\\texttt{{\\bfseries {tex_tt(c.split('.')[-1])}}}"
            head += (f"}}\\hfill{{\\footnotesize \\path{{{rel}}},"
                     f" line {d.line}}}\\par\\nopagebreak")
            body.append(head)
            body.append("\\begin{leansrc}")
            body.append(wrap_stmt(stmt))
            if not ok:
                body.append("  …")
            body.append("\\end{leansrc}")
            total_entries += 1
        if modules:
            mods = ", ".join(f"\\texttt{{{tex_tt(m)}}}" for m, _ in modules)
            body.append(f"\\par\\medskip\\noindent Modules cited: {mods}.")
        if repeats:
            reps = ", ".join(f"\\texttt{{{tex_tt(r)}}}" for r in sorted(repeats))
            body.append("\\par\\medskip\\noindent Also cited in this"
                        f" chapter, listed under an earlier one: {reps}.")
        sections.append("\n".join(body))

    header = (
        "% Auto-generated by tools/lean-cone.py from the book chapters and\n"
        "% the lean/ trees. Do not hand-edit: rerun the tool (the build\n"
        "% does). Statements are extracted signature-level from the sources\n"
        "% at generation time.\n\n"
    )
    OUT.write_text(header + "\n\n".join(sections) + "\n", encoding="utf-8")

    print(f"lean-cone: {total_entries} declarations listed across"
          f" {len(sections)} chapters -> {OUT.relative_to(BOOK)}")
    for title, c, rel in outside:
        print(f"lean-cone: note: {c} (cited in '{title}') resolves only"
              f" outside the primary trees: {rel}")
    # The generated rule catalogue cites its own emission-time layers:
    # rule-source modules (BernsteinLogic.*) and HOL4 results, whose
    # extraction the catalogue performs itself, hash-bound, at emission.
    # Those are reported separately from stale book citations.
    seen_pairs = set()
    stale, emission_layer = [], []
    for title, c in unresolved:
        if (title, c) in seen_pairs:
            continue
        seen_pairs.add((title, c))
        if title == "Rule Catalogue":
            emission_layer.append((title, c))
        else:
            stale.append((title, c))
    if emission_layer:
        print(f"lean-cone: {len(emission_layer)} catalogue emission-layer"
              " citations (rule-source/HOL4; not swept — the catalogue"
              " carries its own hash-bound extraction):")
        for title, c in emission_layer:
            print(f"  {c}")
    if stale:
        print(f"lean-cone: {len(stale)} UNRESOLVED citations"
              " (stale-reference candidates):")
        for title, c in stale:
            print(f"  {c}   (cited in '{title}')")
        if strict:
            sys.exit(1)


def tex_tt_last(c, ns_disp):
    return tex_tt(c.split(".")[-1])


def wrap_stmt(stmt, width=84):
    out = []
    for line in stmt.split("\n"):
        while len(line) > width:
            cut = line.rfind(" ", 0, width)
            if cut <= 0:
                cut = width
            out.append(line[:cut])
            line = "      " + line[cut:].lstrip()
        out.append(line)
    return "\n".join(out)


if __name__ == "__main__":
    main()
