#!/usr/bin/env python3
"""Regenerate the book's tool transcripts from real runs.

Every command transcript printed in a chapter is a generated fragment
(``generated/transcripts/<spec>/<name>.tex``) produced by running the
printed commands against the sibling tool checkouts, or by excerpting a
committed file. Chapters ``\\input`` the fragments; nothing shown to the
reader is hand-transcribed, so transcripts cannot silently go stale.

Regeneration is cached, content-addressed: each spec's stamp
(``generated/stamps/<spec>.stamp``) records a digest over the spec file
and every declared input (tool source trees, corpus files, listings).
When nothing changed, nothing runs; when a tool or an input moved, the
session re-runs and any change to the printed text shows up as an
ordinary diff to the committed fragment.

Specs live in ``transcripts/*.toml`` (``tools.toml`` is the tool-tree
registry). Run via ``../build.sh transcripts`` or directly:

    tools/transcripts.py [--force] [--strict] [--allow-dirty] [--only SPEC]

Exit is nonzero on hard errors (a command exited with an unexpected
status, a prose assertion failed, a fragment would contain
``\\end{Verbatim}``); missing tool trees are a warning by default and an
error under ``--strict``. Requires Python >= 3.11 (tomllib).
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

GENERATOR_VERSION = "1"

BOOK = Path(__file__).resolve().parent.parent
REPO = BOOK.parent
SPECS = BOOK / "transcripts"
GEN = BOOK / "generated" / "transcripts"
STAMPS = BOOK / "generated" / "stamps"

VERB_OPEN = (
    "\\begin{{Verbatim}}[fontsize=\\{fontsize},frame=leftline,"
    "rulecolor=\\color{{accentmid}},framesep=3mm,xleftmargin=3mm]"
)
VERB_CLOSE = "\\end{Verbatim}"

MARK = "__TRANSCRIPT_MARK"


def warn(msg: str) -> None:
    print(f"transcripts: warning: {msg}", file=sys.stderr)


def die(msg: str) -> None:
    print(f"transcripts: error: {msg}", file=sys.stderr)
    sys.exit(1)


# ------------------------------------------------------------ colour hygiene
#
# A captured transcript must be the same bytes whatever terminal the
# capture ran under. An ANSI escape in a fragment is wrong twice over: it
# typesets as garbage inside Verbatim, and one landing between a prose
# assertion's ``^``/``$`` anchors fails the assertion for a reason that has
# nothing to do with the tool's output — while being INVISIBLE in the
# error message, which a terminal renders as colour.
#
# The capture already pipes (``stdout=PIPE``), so a tool checking isatty
# stays plain. What defeats that is colour FORCING in the ambient
# environment: Node's ``shouldColorize`` short-circuits on ``FORCE_COLOR``
# *before* it consults ``isTTY``, so ``console.log("...", n, "bytes")``
# renders the number argument yellow through a pipe. Setting the disabling
# conventions is not enough — Node ignores ``NO_COLOR`` outright when
# ``FORCE_COLOR`` is set, and says so on stderr. The forcing variables have
# to be REMOVED.
#
# Two defences, both at the capture: scrub the environment, then strip
# whatever survives it (with a warning naming the step) — so a tool that
# colourizes for reasons the environment cannot reach still cannot corrupt
# a committed fragment. Note the assertions alone were never sufficient
# cover: they guard the lines they anchor, and a fragment's other lines
# would carry escapes straight into the committed .tex.

COLOR_FORCING_VARS = ("FORCE_COLOR", "CLICOLOR_FORCE", "COLORTERM")
COLOR_DISABLING_ENV = {"NO_COLOR": "1", "CLICOLOR": "0", "TERM": "dumb"}

# CSI (``ESC [ ... final``), OSC (``ESC ] ... BEL|ST``), and the two-byte
# escapes; enough for anything that reaches a captured stdout.
ANSI_RX = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]"
    r"|\][^\x07\x1b]*(?:\x07|\x1b\\)"
    r"|[@-Z\\-_])"
)


def no_color_env(base: dict[str, str] | None = None) -> dict[str, str]:
    """A copy of the environment that cannot force colour on a pipe."""
    env = dict(os.environ if base is None else base)
    for key in COLOR_FORCING_VARS:
        env.pop(key, None)
    env.update(COLOR_DISABLING_ENV)
    return env


def strip_ansi(text: str, where: str) -> str:
    clean = ANSI_RX.sub("", text)
    if clean != text:
        warn(f"{where}: output carried ANSI escapes even under the"
             f" no-colour environment — stripped. The tool ignores"
             f" NO_COLOR; give its step an explicit no-colour flag"
             f" (e.g. --color=never) so the capture is honest.")
    return clean


# --------------------------------------------------------------- tool trees


def main_checkout_root() -> Path | None:
    """Root of the primary checkout (worktrees resolve siblings via it)."""
    try:
        common = subprocess.run(
            ["git", "-C", str(REPO), "rev-parse", "--git-common-dir"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None
    p = Path(common)
    if not p.is_absolute():
        p = (REPO / p).resolve()
    return p.parent


def resolve_tool(name: str, entry: dict) -> Path | None:
    """Locate a tool tree: env override, then the declared relative path
    beside this checkout, then beside the primary checkout (for git
    worktrees, whose parent directory usually lacks the siblings)."""
    env_key = "BOOK_TOOL_" + re.sub(r"[^A-Za-z0-9]", "_", name).upper()
    if env_key in os.environ:
        p = Path(os.environ[env_key]).resolve()
        return p if p.exists() else None
    rel = entry.get("path", f"../{name}")
    cand = (REPO / rel).resolve()
    if cand.exists():
        return cand
    main_root = main_checkout_root()
    if main_root is not None:
        cand = (main_root / rel).resolve()
        if cand.exists():
            return cand
    return None


def load_tools() -> dict[str, dict]:
    with open(SPECS / "tools.toml", "rb") as f:
        return tomllib.load(f)


def tool_head(path: Path) -> tuple[str, str] | None:
    """(short sha, commit date) of the tool tree's HEAD, or None."""
    try:
        out = subprocess.run(
            ["git", "-C", str(path), "log", "-1", "--format=%h %cs"],
            capture_output=True, text=True, check=True,
        ).stdout.split()
        return out[0], out[1]
    except (OSError, subprocess.CalledProcessError, IndexError):
        return None


def paths_dirty(tree: Path, rel: str) -> bool:
    try:
        out = subprocess.run(
            ["git", "-C", str(tree), "status", "--porcelain", "--", rel],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        return bool(out)
    except (OSError, subprocess.CalledProcessError):
        return False  # not a git tree: nothing to compare against


# ------------------------------------------------------------------ hashing


def hash_path(h: "hashlib._Hash", p: Path, label: str) -> None:
    """Feed a file or directory's content (names + bytes) into a digest."""
    h.update(label.encode())
    if p.is_file():
        h.update(p.read_bytes())
        return
    if not p.is_dir():
        raise FileNotFoundError(p)
    for sub in sorted(p.rglob("*")):
        if ".git" in sub.parts or "node_modules" in sub.parts:
            continue
        if sub.is_file() and not sub.is_symlink():
            h.update(str(sub.relative_to(p)).encode())
            h.update(sub.read_bytes())


def split_ref(ref: str) -> tuple[str, str]:
    """'tool:rel/path' -> (tool, rel). Tool 'book' means this book/ dir."""
    tool, _, rel = ref.partition(":")
    if not rel:
        die(f"input reference {ref!r} must be tool:relative/path")
    return tool, rel


# ------------------------------------------------------------ spec sessions


def substitute(text: str, tool_paths: dict[str, Path]) -> str:
    """Expand {toolname} and {ENV:VAR} templates."""

    def repl(m: re.Match) -> str:
        key = m.group(1)
        if key.startswith("ENV:"):
            return os.environ.get(key[4:], "")
        if key in tool_paths:
            return str(tool_paths[key])
        die(f"unknown template key {{{key}}}")
        return ""  # unreachable

    return re.sub(r"\{([A-Za-z0-9_.:-]+)\}", repl, text)


def make_sandbox(spec: dict, tool_paths: dict[str, Path]) -> Path:
    sandbox = Path(tempfile.mkdtemp(prefix="book-transcript-"))
    for m in spec.get("mount", []):
        src = tool_paths[m["tool"]] / m["src"]
        dest = sandbox / m["dest"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        if not src.exists():
            die(f"mount source missing: {src}")
        if m.get("mode", "link") == "copy":
            if src.is_dir():
                shutil.copytree(src, dest)
            else:
                shutil.copy2(src, dest)
        else:
            dest.symlink_to(src)
    return sandbox


def run_session(spec: dict, steps: list[dict], sandbox: Path,
                tool_paths: dict[str, Path]) -> list[tuple[str, int]]:
    """Run all steps in one bash session; return (output, exit) per step.

    One session per spec: the working directory, shell variables, and
    ``$?`` persist across steps exactly as they would for a reader typing
    the printed commands into one terminal.
    """
    env = no_color_env()
    env["TRANSCRIPT_ROOT"] = str(sandbox)
    for k, v in spec.get("session", {}).get("env", {}).items():
        env[k] = substitute(v, tool_paths)
    for cmd in spec.get("session", {}).get("setup", []):
        cmd = substitute(cmd, tool_paths)
        r = subprocess.run(cmd, shell=True, cwd=sandbox, env=env,
                           capture_output=True, text=True,
                           timeout=spec.get("timeout", 600))
        if r.returncode != 0:
            die(f"setup step failed ({cmd!r}):\n{r.stdout}\n{r.stderr}")

    script = ["set +e"]
    for i, step in enumerate(steps):
        script.append(f'echo "{MARK} BEGIN {i}"')
        script.append("(exit ${__rc:-0})")  # restore $? for `echo $?` steps
        script.append(substitute(step["run"], tool_paths))
        script.append("__rc=$?")
        script.append(f'echo "{MARK} END {i} rc=$__rc"')
    sf = sandbox / ".session.sh"
    sf.write_text("\n".join(script) + "\n")
    r = subprocess.run(["bash", str(sf)], cwd=sandbox, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, timeout=spec.get("timeout", 600))
    results: list[tuple[str, int]] = []
    current: list[str] | None = None
    for line in r.stdout.splitlines():
        if line.startswith(MARK):
            m = re.match(rf"{MARK} (BEGIN|END) (\d+)(?: rc=(-?\d+))?", line)
            if not m:
                continue
            if m.group(1) == "BEGIN":
                current = []
            else:
                idx = int(m.group(2))
                text = strip_ansi(
                    "\n".join(current or []),
                    f"step {steps[idx]['run']!r}" if idx < len(steps)
                    else f"step {idx}")
                results.append((text, int(m.group(3))))
                current = None
        elif current is not None:
            current.append(line)
    if len(results) != len(steps):
        die(f"session produced {len(results)} step records for "
            f"{len(steps)} steps — a step swallowed the markers?")
    return results


# ------------------------------------------------------------------ filters


def apply_filters(lines: list[str], filters: list[dict]) -> list[str]:
    for f in filters:
        kind = f["kind"]
        if kind == "collapse":
            # maximal runs of consecutive matching lines -> one marker line
            rx, marker = re.compile(f["match"]), f["marker"]
            out: list[str] = []
            in_run = False
            for ln in lines:
                if rx.search(ln):
                    if not in_run:
                        out.append(marker)
                        in_run = True
                else:
                    out.append(ln)
                    in_run = False
            lines = out
        elif kind == "cut":
            # first `from` match through next `to` match -> one marker line
            fr, to = re.compile(f["from"]), re.compile(f["to"])
            out, state = [], 0  # 0 before, 1 cutting, 2 after
            for ln in lines:
                if state == 0 and fr.search(ln):
                    out.append(f["marker"])
                    state = 1
                    if to.search(ln):
                        state = 2
                elif state == 1:
                    if to.search(ln):
                        state = 2
                else:
                    out.append(ln)
            lines = out
        elif kind == "clip":
            # drop everything after the matching line; append marker if any
            rx = re.compile(f["after"])
            out = []
            for ln in lines:
                out.append(ln)
                if rx.search(ln):
                    if f.get("marker"):
                        out.append(f["marker"])
                    break
            lines = out
        elif kind == "recolumn":
            # re-seat a trailing comment at a fixed column (declared in the
            # chapter's receipt comment as re-flowing to the book's measure)
            rx, at, col = re.compile(f["match"]), f["at"], f["column"]
            gap = f.get("min-gap", 2)
            out = []
            for ln in lines:
                idx = ln.find(at)
                if rx.search(ln) and idx > 0:
                    payload = ln[:idx].rstrip()
                    pad = max(col - len(payload), gap)
                    ln = payload + " " * pad + ln[idx:]
                out.append(ln)
            lines = out
        elif kind == "wrap":
            # break long lines at the last `at` before `width`; continuation
            # lines get `indent`. The chapter declares the wrapping in prose.
            width, at = f["width"], f.get("at", ",")
            indent = f.get("indent", "  ")
            keep_sep = f.get("keep-sep", at != " ")
            only = re.compile(f["match"]) if "match" in f else None
            out = []
            for ln in lines:
                if only and not only.search(ln):
                    out.append(ln)
                    continue
                while len(ln) > width:
                    cut = ln.rfind(at, 0, width + 1)
                    if cut <= 0:
                        break
                    out.append(ln[: cut + len(at)] if keep_sep else ln[:cut])
                    ln = indent + ln[cut + len(at):]
                out.append(ln)
            lines = out
        else:
            die(f"unknown filter kind {kind!r}")
    return lines


# ---------------------------------------------------------------- fragments


def compose_run_fragment(frag: dict, steps: list[dict],
                         results: list[tuple[str, int]],
                         start: int) -> tuple[str, str]:
    """Returns (raw text for assertions, filtered display text)."""
    raw_parts: list[str] = []
    display: list[str] = []
    for j, step in enumerate(steps):
        out, rc = results[start + j]
        expect = step.get("expect-exit", 0)
        if expect >= 0 and rc != expect:
            die(f"step {step['run']!r} exited {rc}, expected {expect}\n"
                f"output:\n{out}")
        raw_parts.append(out)
        if step.get("show-cmd", True):
            display.extend(step.get("display", "$ " + step["run"]).splitlines())
        if step.get("show-out", True) and out:
            display.extend(out.splitlines())
    raw = "\n".join(raw_parts)
    shown = apply_filters(display, frag.get("filters", []))
    return raw, "\n".join(shown)


def compose_file_fragment(frag: dict, tool_paths: dict[str, Path]) -> tuple[str, str]:
    tool, rel = split_ref(frag["source"])
    text = (tool_paths[tool] / rel).read_text()
    lines = text.splitlines()
    if "from" in frag:
        rx = re.compile(frag["from"])
        for i, ln in enumerate(lines):
            if rx.search(ln):
                lines = lines[i:]
                break
        else:
            die(f"fragment {frag['name']}: 'from' anchor not found")
    if "to" in frag:
        rx = re.compile(frag["to"])
        for i, ln in enumerate(lines):
            if rx.search(ln):
                lines = lines[: i + 1]
                break
        else:
            die(f"fragment {frag['name']}: 'to' anchor not found")
    raw = "\n".join(lines)
    shown = frag.get("prepend", []) + apply_filters(lines, frag.get("filters", []))
    return raw, "\n".join(shown)


def fragment_tex(spec_name: str, frag: dict, body: str,
                 provenance: list[str]) -> str:
    if VERB_CLOSE in body:
        die(f"fragment {frag['name']} would contain {VERB_CLOSE!r}")
    header = [
        f"% AUTOGENERATED by tools/transcripts.py from"
        f" transcripts/{spec_name}.toml (fragment {frag['name']!r}).",
        "% Do not hand-edit: edit the spec or its inputs and rerun"
        " ./build.sh (or ./build.sh transcripts --force).",
    ]
    header += [f"% {p}" for p in provenance]
    open_line = VERB_OPEN.format(fontsize=frag.get("fontsize", "small"))
    return "\n".join(header) + "\n" + open_line + "\n" + body + "\n" + VERB_CLOSE + "\n"


def normalize_volatile(text: str, volatile: list[str]) -> str:
    for rx in volatile:
        text = re.sub(rx, "<volatile>", text)
    return text


def strip_header(text: str) -> str:
    """Drop the leading ``%`` comment block (AUTOGENERATED + provenance).

    Regeneration compares displayed content, not the header: a tool-tree
    revision bump alone must never rewrite a committed fragment (each
    rewrite would also re-roll any volatile spans, e.g. wall-clock
    timings, churning the source with digits that are not content).
    Only the leading comment block is stripped — a ``%`` inside the
    Verbatim body is content and still compares.
    """
    lines = text.splitlines(keepends=True)
    for i, ln in enumerate(lines):
        if not ln.startswith("%"):
            return "".join(lines[i:])
    return ""


# --------------------------------------------------------------------- main


def process_spec(path: Path, tools: dict, args) -> bool:
    """Returns True on success (including honest skips)."""
    name = path.stem
    spec = tomllib.loads(path.read_text())
    fragments = spec.get("fragment", [])
    if not fragments:
        warn(f"{name}: no fragments declared")
        return True

    # resolve every tool the spec references
    needed: set[str] = set()
    for ref in spec.get("inputs", []):
        needed.add(split_ref(ref)[0])
    for frag in fragments:
        if frag.get("kind") == "file":
            needed.add(split_ref(frag["source"])[0])
    for m in spec.get("mount", []):
        needed.add(m["tool"])
    tool_paths: dict[str, Path] = {"book": BOOK}
    missing: list[str] = []
    for t in sorted(needed - {"book"}):
        if t not in tools:
            die(f"{name}: tool {t!r} not in tools.toml")
        p = resolve_tool(t, tools[t])
        if p is None:
            missing.append(t)
        else:
            tool_paths[t] = p

    frag_paths = [
        (GEN / name / f"{f['name']}.tex") if f.get("emit", True) else None
        for f in fragments
    ]
    stamp_path = STAMPS / f"{name}.stamp"

    if missing:
        msg = (f"{name}: tool tree(s) absent ({', '.join(missing)}); "
               f"keeping committed fragments")
        if args.strict:
            die(msg)
        warn(msg)
        for fp in frag_paths:
            if fp is not None and not fp.exists():
                die(f"{name}: {fp} missing and its tool tree is absent")
        return True

    # cache key over spec bytes + declared inputs
    h = hashlib.sha256()
    h.update(GENERATOR_VERSION.encode())
    h.update(path.read_bytes())
    for ref in sorted(spec.get("inputs", [])):
        tool, rel = split_ref(ref)
        try:
            hash_path(h, tool_paths[tool] / rel, ref)
        except FileNotFoundError:
            die(f"{name}: declared input missing: {ref}")
    key = h.hexdigest()

    stale = (
        args.force
        or not stamp_path.exists()
        or f"key={key}" not in stamp_path.read_text().splitlines()
        or any(fp is not None and not fp.exists() for fp in frag_paths)
    )
    if not stale:
        print(f"transcripts: {name}: up to date")
        return True

    # external tool trees must be clean where we cite their revision
    provenance: list[str] = []
    for t in sorted(needed - {"book"}):
        tp = tool_paths[t]
        head = tool_head(tp)
        dirty = any(
            paths_dirty(tp, split_ref(ref)[1])
            for ref in spec.get("inputs", [])
            if split_ref(ref)[0] == t
        )
        if dirty and not args.allow_dirty:
            msg = (f"{name}: {t} has uncommitted changes under declared "
                   f"inputs; refusing to cite it (--allow-dirty overrides)")
            if args.strict:
                die(msg)
            warn(msg + "; keeping committed fragments")
            return True
        label = f"{t} @ {head[0]} ({head[1]})" if head else f"{t} (not a git tree)"
        if dirty:
            label += " +uncommitted"
        provenance.append(label)

    # ensure steps (build the tools this spec runs)
    for t in sorted(needed - {"book"}):
        for cmd in tools[t].get("ensure", []):
            r = subprocess.run(cmd, shell=True, cwd=tool_paths[t],
                               env=no_color_env(),
                               capture_output=True, text=True)
            if r.returncode != 0:
                die(f"{name}: ensure step for {t} failed ({cmd!r}):\n"
                    f"{r.stdout[-2000:]}\n{r.stderr[-2000:]}")

    sandbox = make_sandbox(spec, tool_paths)
    try:
        run_steps: list[dict] = []
        frag_step_start: dict[str, int] = {}
        for frag in fragments:
            if frag.get("kind", "run") == "run":
                frag_step_start[frag["name"]] = len(run_steps)
                run_steps.extend(frag.get("step", []))
        results = (
            run_session(spec, run_steps, sandbox, tool_paths)
            if run_steps else []
        )

        changed = 0
        for frag, fp in zip(fragments, frag_paths):
            if frag.get("kind", "run") == "file":
                raw, body = compose_file_fragment(frag, tool_paths)
            else:
                raw, body = compose_run_fragment(
                    frag, frag.get("step", []), results,
                    frag_step_start[frag["name"]])
            for rx in frag.get("prose-assert", []):
                if not re.search(rx, raw, re.M):
                    die(f"{name}/{frag['name']}: prose assertion failed —"
                        f" the chapter's prose may now be stale."
                        f" Missing: {rx!r}\nagainst output:\n{raw}")
            if fp is None:
                continue  # assertion-only fragment: nothing rendered
            tex = fragment_tex(name, frag, body, provenance)
            if fp.exists():
                old, new = fp.read_text(), tex
                vol = frag.get("volatile", [])
                if old == new:
                    continue
                if (normalize_volatile(strip_header(old), vol)
                        == normalize_volatile(strip_header(new), vol)):
                    # displayed content is stable: any difference sits in
                    # the provenance header or in declared volatile spans
                    # (wall-clock timings). Keep the committed bytes whole
                    # — header and timings stay the internally consistent
                    # record of the run that actually produced them — and
                    # let the spec stamp carry the re-certification at the
                    # current revisions.
                    print(f"transcripts: {name}/{frag['name']}: stable"
                          f" (header/volatile-only differences kept)")
                    continue
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_text(tex)
            changed += 1
            print(f"transcripts: {name}/{frag['name']}: REGENERATED"
                  f" (review the diff)")
        stamp_path.parent.mkdir(parents=True, exist_ok=True)
        stamp_path.write_text(
            f"key={key}\n" + "".join(f"# {p}\n" for p in provenance))
        if changed == 0:
            print(f"transcripts: {name}: refreshed, all fragments stable")
        return True
    finally:
        shutil.rmtree(sandbox, ignore_errors=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--force", action="store_true",
                    help="re-run every session regardless of stamps")
    ap.add_argument("--strict", action="store_true",
                    help="absent/dirty tool trees are errors, not warnings")
    ap.add_argument("--allow-dirty", action="store_true",
                    help="regenerate from tool trees with uncommitted "
                         "changes (provenance is marked)")
    ap.add_argument("--only", action="append", default=[],
                    help="process only the named spec(s)")
    args = ap.parse_args()

    tools = load_tools()
    specs = sorted(p for p in SPECS.glob("*.toml") if p.name != "tools.toml")
    if args.only:
        specs = [p for p in specs if p.stem in args.only]
        if not specs:
            die(f"no specs match {args.only}")
    ok = True
    for spec in specs:
        ok = process_spec(spec, tools, args) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
