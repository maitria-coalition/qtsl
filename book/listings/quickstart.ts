// quickstart.ts — produce the FrozenLake certificate, then break it.
import { writeFileSync } from "node:fs";
import { dp } from "@maitria/mtk";

// The environment: Gymnasium's FrozenLake-4x4, slippery (success rate 1/3).
const model = dp.frozenlake("4x4", true, "1/3");

// The claim: exact finite-horizon dynamic programming to deadline T = 10.
const res = model.exact(10);
console.log("claim:", res.bound);

// Emit the certificate: canonical bytes, encoded by the Rust core.
const meta = {
  envId: "FrozenLake-v1",
  mdpName: "frozenlake-4x4",
  repoSha: dp.gymSha(),
  kwargs: "",
};
const bytes = res.emit(meta);
writeFileSync("exact_T10.cbor", bytes);
console.log("wrote exact_T10.cbor:", bytes.length, "bytes");

// Now break it: raise one interior value-table entry to 1.
// (docMutate refuses unless the unmodified doc round-trips byte-identically.)
const broken = dp.docMutate(bytes, [
  { path: ["table", 1, 0, 0], setHex: "01" },
  { path: ["table", 1, 0, 1], setHex: "01" },
]);
writeFileSync("mutant_table_raised.cbor", broken);
console.log("wrote mutant_table_raised.cbor:", broken.length, "bytes");
