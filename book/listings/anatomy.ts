// anatomy.ts — a certificate is a document; read it before you trust it.
import { readFileSync } from "node:fs";
import { dp } from "@maitria/mtk";

const bytes = readFileSync("exact_T10.cbor");
const doc = dp.docJson(bytes, []) as Record<string, unknown>;
console.log("fields:", Object.keys(doc).join(" "));
console.log("deadline:", dp.docJson(bytes, ["deadline"]),
            " states:", dp.docJson(bytes, ["ns"]),
            " goal:", dp.docJson(bytes, ["goal"]));
console.log("claim:", dp.docJson(bytes, ["claim"]));      // bignum pair, hex
console.log("kernel[0]:", dp.docJson(bytes, ["kernel", 0])); // s a s' p_num p_den
