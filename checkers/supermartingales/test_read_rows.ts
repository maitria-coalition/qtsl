/**
 * test_read_rows.ts — the malformed-input gate battery for read_rows.ts.
 *
 * Mutant discipline: each case corrupts a pristine rows listing in a way
 * aimed at ONE conformance row of the C2 sect. 4.2 table, runs the
 * reader, and requires (a) a REFUSED exit and (b) the refusal to name
 * the intended check — a mutant whose witness stays green would mean
 * the gate it targets was never a gate. The pristine listing must PASS
 * before and after (the battery restores nothing on disk; mutations are
 * in-memory string edits written to a scratch directory).
 *
 *   node --experimental-strip-types test_read_rows.ts \
 *     --stack BLstack.rows.txt --cert BLCert.rows.txt pristine.rows.txt
 *
 * Exit 0 iff every case behaves; nonzero with a per-case report line
 * otherwise.
 */

import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

type Case = {
  name: string;
  /** aimed conformance row / gate */
  aims: string;
  /** substring the refusal must carry */
  expect: string;
  mutate: (text: string) => string;
};

function lineOf(text: string, re: RegExp): string {
  const m = text.split("\n").find((l) => re.test(l));
  if (!m) throw new Error(`fixture has no line matching ${re}`);
  return m;
}

/** Replace the first line matching `re` via `f`; throws if absent. */
function editLine(text: string, re: RegExp, f: (l: string) => string): string {
  const lines = text.split("\n");
  const i = lines.findIndex((l) => re.test(l));
  if (i < 0) throw new Error(`fixture has no line matching ${re}`);
  lines[i] = f(lines[i]);
  return lines.join("\n");
}

const CASES: Case[] = [
  {
    name: "dup-funval-identical",
    aims: "P-FUN (duplicate FUN_VAL row)",
    expect: "duplicate row",
    // duplicate a Wire/index row verbatim under a fresh op index
    mutate: (t) => {
      const l = lineOf(t, /cert\/Wire\/index/);
      const n = t.split("\n").filter((x) => /^op\[/.test(x)).length;
      return t.replace(/\n$/, "") + "\n" +
        l.replace(/^op\[\s*\d+\]/, `op[${n}]`) + "\n";
    },
  },
  {
    name: "dup-funval-contradicting",
    aims: "P-FUN (contradicting duplicate)",
    expect: "duplicate row",
    mutate: (t) => {
      const l = lineOf(t, /cert\/Wire\/index/);
      const n = t.split("\n").filter((x) => /^op\[/.test(x)).length;
      return t.replace(/\n$/, "") + "\n" +
        l.replace(/^op\[\s*\d+\]/, `op[${n}]`).replace(/value=nat:\d+/, "value=nat:999") + "\n";
    },
  },
  {
    name: "drop-wire-index",
    aims: "P-DENSE (Wire/index family vs Cert/nWires)",
    expect: "P-DENSE",
    // blank the first Wire/index row (keep op numbering intact by
    // replacing it with a duplicate of a harmless neighbor? no — turn it
    // into a comment would break numbering; instead re-point its index
    // past nWires)
    mutate: (t) => editLine(t, /cert\/Wire\/index/, (l) => l.replace(/value=nat:\d+/, "value=nat:900000")),
  },
  {
    name: "nwires-skew",
    aims: "P-DENSE (Cert/nWires authority)",
    expect: "P-DENSE",
    mutate: (t) => editLine(t, /cert\/Cert\/nWires/, (l) => l.replace(/value=nat:(\d+)/, (_, d) => `value=nat:${Number(d) + 1}`)),
  },
  {
    name: "forward-ref",
    aims: "P-REF (refs strictly backward)",
    expect: "not backward",
    mutate: (t) => editLine(t, /stack\/Judgment\/pre/, (l) => l.replace(/value=L\d+/, "value=L999999")),
  },
  {
    name: "orphan-rows",
    aims: "P-ORPHAN (surplus is never silently dropped)",
    expect: "P-ORPHAN",
    mutate: (t) => {
      const n = t.split("\n").filter((x) => /^op\[/.test(x)).length;
      return t.replace(/\n$/, "") + "\n" +
        `op[${n}] elta sort=G<stack/Term>\n` +
        `op[${n + 1}] funa fun=G<stack/TConst> args=[q:7/9] value=L${n}\n`;
    },
  },
  {
    name: "sph-with-argument",
    aims: "P-ARGS (arity against the declaration)",
    expect: "P-ARGS",
    // give a nullary constructor an argument (FSpH if present, else FTrue)
    mutate: (t) => {
      const re = /fun=G<(cert\/FSpH|stack\/FTrue)> args=\[\]/;
      if (!re.test(t)) throw new Error("fixture has no nullary formula constructor");
      return t.replace(re, (m) => m.replace("args=[]", "args=[L0]"));
    },
  },
  {
    name: "payload-row",
    aims: "reader subset (payload-free wires)",
    expect: "payload",
    mutate: (t) => {
      const wire = lineOf(t, /elta sort=G<stack\/Wire>/);
      const wireIdx = Number(wire.match(/^op\[\s*(\d+)\]/)![1]);
      const n = t.split("\n").filter((x) => /^op\[/.test(x)).length;
      return t.replace(/\n$/, "") + "\n" +
        `op[${n}] funa fun=G<cert/Wire/payloadQ> args=[L${wireIdx}] value=q:1/2\n`;
    },
  },
  {
    name: "wrong-sort-ref",
    aims: "P-REF (sort agreement at use)",
    expect: "P-REF",
    // point Wire/type at op 0 (whatever sort it is, it is not TensorType
    // in any compiled listing, whose op 0 is a Wire or Term element)
    mutate: (t) => editLine(t, /stack\/Wire\/type/, (l) => l.replace(/value=L\d+/, "value=L0")),
  },
  {
    name: "noncanonical-rational",
    aims: "canonical-literal gate (Q reduced)",
    expect: "non-canonical rational",
    mutate: (t) => editLine(t, /q:-?\d+\/\d+/, (l) => l.replace(/q:(-?\d+)\/(\d+)/, (_, a, b) => `q:${Number(a) * 2}/${Number(b) * 2}`)),
  },
  {
    name: "midline-truncation",
    aims: "container grammar (no partial reads)",
    expect: "unparseable",
    mutate: (t) => {
      const cut = Math.floor(t.length * 0.7);
      const nl = t.indexOf("\n", cut);
      return t.slice(0, nl - 12); // rip mid-line
    },
  },
  {
    name: "op-renumbering",
    aims: "container grammar (strict op numbering)",
    expect: "expected",
    mutate: (t) => editLine(t, /^op\[\s*7\]/, (l) => l.replace(/^op\[\s*7\]/, "op[  77]")),
  },
];

function main() {
  const argv = process.argv.slice(2);
  let stack = "", cert = "", pristine = "";
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === "--stack") stack = argv[++i];
    else if (argv[i] === "--cert") cert = argv[++i];
    else pristine = argv[i];
  }
  if (!stack || !cert || !pristine) {
    console.error("usage: test_read_rows.ts --stack S --cert C pristine.rows.txt");
    process.exit(2);
  }
  const reader = path.join(path.dirname(process.argv[1]), "read_rows.ts");
  const work = fs.mkdtempSync(path.join(os.tmpdir(), "read-rows-gate-"));
  const run = (file: string) =>
    spawnSync("node", ["--experimental-strip-types", reader, "--stack", stack, "--cert", cert, file], {
      encoding: "utf8",
      maxBuffer: 1 << 28,
    });

  const text = fs.readFileSync(pristine, "utf8");
  let failures = 0;

  const base = run(pristine);
  if (base.status !== 0) {
    console.error(`FAIL pristine: reader refused the unmutated fixture:\n${base.stdout.slice(0, 400)}`);
    process.exit(1);
  }
  console.log(`ok   pristine passes (${text.split("\n").length} lines)`);

  for (const c of CASES) {
    let mutated: string;
    try {
      mutated = c.mutate(text);
    } catch (e) {
      console.log(`skip ${c.name}: ${(e as Error).message}`);
      continue;
    }
    const f = path.join(work, `${c.name}.rows.txt`);
    fs.writeFileSync(f, mutated);
    const r = run(f);
    if (r.status !== 3) {
      console.error(`FAIL ${c.name} (${c.aims}): expected REFUSED exit 3, got ${r.status}`);
      failures += 1;
      continue;
    }
    if (!r.stdout.includes(c.expect)) {
      console.error(`FAIL ${c.name} (${c.aims}): refusal does not name the gate — got: ${r.stdout.split("\n")[0].slice(0, 200)}`);
      failures += 1;
      continue;
    }
    console.log(`ok   ${c.name} -> ${r.stdout.split("\n")[0].slice(0, 100)}`);
  }

  const again = run(pristine);
  if (again.status !== 0) {
    console.error("FAIL pristine no longer passes after the battery (on-disk mutation leaked)");
    failures += 1;
  }
  fs.rmSync(work, { recursive: true, force: true });
  if (failures) {
    console.error(`${failures} failure(s)`);
    process.exit(1);
  }
  console.log("gate battery green");
}

main();
