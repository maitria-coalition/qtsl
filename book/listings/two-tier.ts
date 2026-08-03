// two-tier.ts — the float lane proposes; the exact lane disposes.
import { lp } from "@maitria/mtk";

// minimize x0 + x1  subject to  x0 + 2*x1 = 1,  3*x0 + x1 = 1,  x >= 0
const cols = [{ cost: 1 }, { cost: 1 }];
const rows = [
  { lo: 1, hi: 1, cols: [0, 1], coefs: [1, 2] },
  { lo: 1, hi: 1, cols: [0, 1], coefs: [3, 1] },
];

// tier F: HiGHS, floats — fast, unciteable; duals are routing advice
const f = lp.floatSolve(cols, rows);
console.log("float:", f.status, f.objective, "duals", f.rowDuals);

// tier E: exact Bland simplex over Q — the only tier a certificate cites
const e = lp.simplexMin([1, 1], [[1, 2], [3, 1]], [1, 1]);
if (e.status === "opt") {
  const at = e.x.map(String).join(", ");
  console.log("exact:", e.value.toString(), "at x =", at);
}
