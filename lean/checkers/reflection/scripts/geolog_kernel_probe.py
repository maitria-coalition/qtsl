#!/usr/bin/env python3
"""Generate a kernel-reduction probe for the geolog reader.

Usage:
    geolog_kernel_probe.py <out.lean> refuse <fixture> <class> <witness>
    geolog_kernel_probe.py <out.lean> accept <fixture> <nops> <zones> <pc> <ts> <msg|none>
      (repeat the refuse/accept groups; <zones> like "1:3,1:65535" or "-";
       <msg> as hex bytes or "none" or "empty")

Emits `example ... := by decide` probes over the embedded fixture
bytes. `decide` hands the closed Bool to the kernel, so a successful
elaboration proves the exercised decode path reduces there — i.e. is
free of well-founded (kernel-opaque) recursion. The probe file is
generated, not committed: fixture bytes stay out of the tree.

Kernel-facing comparators avoid two toolchain sinkholes on purpose:
string equality does not kernel-reduce under the byte-packed string
model (refusal probes compare class and witness; tags are compared by
the native differential), and deeply nested product `DecidableEq`
instances can fail to synthesize (accept probes compare fields
individually).
"""

import sys
from pathlib import Path

HEADER = """import Reflection.Render

open PPLC.Geolog

/-- Refusal shape: class and witness. -/
def errShape (r : GRes) (c : RClass) (w : Nat) : Bool :=
  match r with
  | .err c' _ w' => c' == c && w' == w
  | .ok _ => false

/-- Accept shape of a single commit, field-wise. -/
def commitIs (c : GCommit) (nops : Nat) (zr : List ZoneRun)
    (pc ts : Nat) (msg : Option Bytes) : Bool :=
  c.cbody.ops.length == nops && c.cbody.zoneRuns == zr &&
  c.cskel.parentCount == pc && c.cskel.tsClaim == ts &&
  c.cskel.message == msg

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
"""


def zones_lit(spec: str) -> str:
    if spec in ("-", ""):
        return "[]"
    runs = ["⟨" + r.replace(":", ", ") + "⟩" for r in spec.split(",")]
    return "[" + ", ".join(runs) + "]"


def msg_lit(spec: str) -> str:
    if spec == "none":
        return "none"
    if spec == "empty":
        return "some []"
    bs = bytes.fromhex(spec)
    return "some " + str(list(bs))


def main():
    out = Path(sys.argv[1])
    args = sys.argv[2:]
    defs, examples = [], []
    i = n = 0
    while i < len(args):
        kind = args[i]
        n += 1
        name = f"bs{n}"
        data = list(Path(args[i + 1]).read_bytes())
        defs.append(f"def {name} : PPLC.Geolog.Bytes := {data}\n")
        if kind == "refuse":
            cls, wit = args[i + 2], args[i + 3]
            examples.append(
                f"example : errShape (readGeolog {name}) .{cls} {wit} = true := by decide\n")
            i += 4
        elif kind == "accept":
            nops, zones, pc, ts, msg = args[i + 2:i + 7]
            examples.append(
                f"example : (match readGeolog {name} with\n"
                f"           | .ok g => g.commits.length == 1 &&\n"
                f"               (g.commits.all fun c =>\n"
                f"                 commitIs c {nops} {zones_lit(zones)} {pc} {ts} ({msg_lit(msg)}))\n"
                f"           | .err _ _ _ => false) = true := by decide\n")
            i += 7
        else:
            raise SystemExit(f"unknown probe kind {kind!r}")
    out.write_text(HEADER + "".join(defs) + "\n" + "".join(examples))
    print(f"wrote {out} with {len(examples)} probes")


if __name__ == "__main__":
    main()
