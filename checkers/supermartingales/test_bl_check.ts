/**
 * test_bl_check.ts — verdict battery for the TypeScript reference lane
 * (`check_rows.ts` = read_rows.ts + bl_check.ts) over the committed
 * testdata listings.
 *
 * Three certificates from the published-table campaign's wave-1a set
 * (the qtsl-experiments repository carries the full corpus + battery;
 * these are its smallest representatives, committed here so the lane
 * has standalone teeth):
 *   - faulty_rare_bound          pristine        -> ACCEPT
 *   - faulty_rare_M1_false_bound inflated claim  -> REJECT berncone.coeff
 *   - faulty_rare_M2_corrupt_table perturbed kernel -> REJECT berncone.coeff
 *
 * A checker that has never rejected anything is untested machinery; the
 * REJECT rows must land at the ATTACKED check (berncone.coeff — the
 * recomputed Bernstein coefficient grid), not merely refuse.
 *
 *   node --experimental-strip-types test_bl_check.ts
 */

import { spawnSync } from "node:child_process";
import * as path from "node:path";

const HERE = path.dirname(new URL(import.meta.url).pathname);

const CASES: [string, "ACCEPT" | "REJECT", string | null][] = [
  ["faulty_rare_bound.rows.txt", "ACCEPT", null],
  ["faulty_rare_M1_false_bound.rows.txt", "REJECT", "berncone.coeff"],
  ["faulty_rare_M2_corrupt_table.rows.txt", "REJECT", "berncone.coeff"],
];

const r = spawnSync(
  process.execPath,
  [
    "--experimental-strip-types",
    path.join(HERE, "check_rows.ts"),
    "--stack", path.join(HERE, "theories", "BLstack.rows.txt"),
    "--cert", path.join(HERE, "theories", "BLCert.rows.txt"),
    ...CASES.map(([f]) => path.join(HERE, "testdata", f)),
  ],
  { encoding: "utf8" },
);
if (r.error) throw r.error;
const lines = r.stdout.trim().split("\n");
let bad = 0;
for (let i = 0; i < CASES.length; i++) {
  const [file, verdict, id] = CASES[i];
  const line = lines[i] ?? "(missing)";
  const okVerdict = line.startsWith(verdict) && line.includes(file);
  const okId = id === null || line.includes(id);
  if (okVerdict && okId) {
    console.log(`ok   ${file}: ${verdict}${id ? ` at ${id}` : ""}`);
  } else {
    console.log(`FAIL ${file}: wanted ${verdict}${id ? ` at ${id}` : ""}, got: ${line}`);
    bad += 1;
  }
}
process.exit(bad ? 1 : 0);
