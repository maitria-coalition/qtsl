/**
 * check_rows.ts — CLI for the TypeScript reference lane: read a
 * certificate stored as geolog object rows (reference listing notation)
 * with `read_rows.ts`, then check it with `bl_check.ts`.
 *
 *   node --experimental-strip-types check_rows.ts \
 *     --stack theories/BLstack.rows.txt --cert theories/BLCert.rows.txt \
 *     cert.rows.txt [more.rows.txt ...]
 *
 * One line per input, machine-stable:
 *   ACCEPT <path> proof_nodes=<n>
 *   REJECT <path> <check-id>[,<check-id>...]
 *   REFUSED <path> <reader reason>
 * Exit 0 iff every input ACCEPTed (drivers that expect refusals — mutant
 * batteries — parse the lines instead of the exit code).
 */

import * as fs from "node:fs";
import { RowsReader, parseListing, parseTheoryListing } from "./read_rows.ts";
import type { Vocab } from "./read_rows.ts";
import { checkCertificate } from "./bl_check.ts";

function main() {
  const argv = process.argv.slice(2);
  let stackPath = "", certPath = "";
  const inputs: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === "--stack") stackPath = argv[++i];
    else if (argv[i] === "--cert") certPath = argv[++i];
    else inputs.push(argv[i]);
  }
  if (!stackPath || !certPath || inputs.length === 0) {
    console.error(
      "usage: node --experimental-strip-types check_rows.ts --stack BLstack.rows.txt --cert BLCert.rows.txt cert.rows.txt...",
    );
    process.exit(2);
  }
  const vocab: Vocab = { funs: new Map(), sorts: new Set() };
  parseTheoryListing(fs.readFileSync(stackPath, "utf8"), "stack", vocab, stackPath);
  parseTheoryListing(fs.readFileSync(certPath, "utf8"), "cert", vocab, certPath);
  let ok = true;
  for (const input of inputs) {
    let line: string;
    try {
      const ops = parseListing(fs.readFileSync(input, "utf8"), input);
      const reader = new RowsReader(ops, vocab);
      reader.reconstruct();
      const fails = checkCertificate(reader);
      if (fails.length === 0) {
        line = `ACCEPT ${input} proof_nodes=${reader.nProofNodes}`;
      } else {
        ok = false;
        const ids = [...new Set(fails.map((f) => f.id))];
        line = `REJECT ${input} ${ids.join(",")}`;
      }
    } catch (e) {
      ok = false;
      line = `REFUSED ${input} ${(e as Error).message.split("\n")[0]}`;
    }
    process.stdout.write(line + "\n");
  }
  process.exit(ok ? 0 : 1);
}

main();
