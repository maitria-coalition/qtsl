/**
 * qpoly.ts — exact rational + multivariate polynomial substrate for the
 * TypeScript reference checker (`bl_check.ts`).
 *
 * The TS realization of the arithmetic that `bl_checker.py` obtains from
 * SymPy: expansion of certificate terms into exact-Q polynomials, the
 * canonical primitive-integer term AST (`canon_term`, ported
 * decision-for-decision from `bl_cert.py` — "canonical" in this package
 * means precisely that function's output), barycentric coordinates of a
 * rational n-simplex, and the Bernstein-coefficient machinery of
 * `bl_bernstein.py` (basis change, degree elevation, inward layers q_k,
 * forward differences P_j, the BernCone (j, gamma) grid).
 *
 * Everything is exact; floats never appear. Zero dependencies; node >= 22.
 *
 * Trust posture: part of the reference checker (the trusted component).
 * Differential partner: the python trio over the same certificates'
 * bernfmt bytes (house-side oracle since the rows migration).
 */

import { Q, cmpQ } from "./read_rows.ts";
import type { Term } from "./read_rows.ts";

export class CheckError extends Error {}

function fail(msg: string): never {
  throw new CheckError(msg);
}

// ---------------------------------------------------------------------------
// exact rational arithmetic over read_rows' canonical Q
// ---------------------------------------------------------------------------

function bgcd(a: bigint, b: bigint): bigint {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b) [a, b] = [b, a % b];
  return a;
}

/** Canonicalizing constructor (read_rows' Q refuses non-reduced input). */
export function mkQ(n: bigint, d: bigint): Q {
  if (d === 0n) fail("division by zero");
  if (d < 0n) {
    n = -n;
    d = -d;
  }
  const g = n === 0n ? d : bgcd(n, d);
  return new Q(n / g, d / g);
}

export const Q0 = mkQ(0n, 1n);
export const Q1 = mkQ(1n, 1n);

export const qAdd = (a: Q, b: Q) => mkQ(a.n * b.d + b.n * a.d, a.d * b.d);
export const qSub = (a: Q, b: Q) => mkQ(a.n * b.d - b.n * a.d, a.d * b.d);
export const qMul = (a: Q, b: Q) => mkQ(a.n * b.n, a.d * b.d);
export const qDiv = (a: Q, b: Q) => {
  if (b.n === 0n) fail("division by zero");
  return mkQ(a.n * b.d, a.d * b.n);
};
export const qNeg = (a: Q) => new Q(-a.n, a.d);
export const qIsZero = (a: Q) => a.n === 0n;

export function factorial(k: number): bigint {
  let out = 1n;
  for (let i = 2n; i <= BigInt(k); i++) out *= i;
  return out;
}

export function binomial(n: number, k: number): bigint {
  if (k < 0 || k > n) return 0n;
  return factorial(n) / (factorial(k) * factorial(n - k));
}

/** Multinomial d! / prod(alpha_i!), requiring sum(alpha) == d. */
export function multinom(d: number, alpha: readonly number[]): bigint {
  const s = alpha.reduce((a, b) => a + b, 0);
  if (s !== d) fail(`multinom: |alpha| = ${s} != d = ${d}`);
  let den = 1n;
  for (const a of alpha) den *= factorial(a);
  return factorial(d) / den;
}

// ---------------------------------------------------------------------------
// multivariate polynomials over Q
//
// A monomial is a canonical key "x^2,y^1" (variables sorted by name,
// exponents >= 1 only; "" is the constant monomial). A polynomial is a
// map monomial -> nonzero Q. This is the expanded normal form sympy's
// `expand` produces — equality of maps IS value equality.
// ---------------------------------------------------------------------------

export type Mono = Map<string, number>;
export type Poly = Map<string, Q>;

export function monoKey(m: Mono): string {
  return [...m.entries()]
    .filter(([, e]) => e > 0)
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
    .map(([v, e]) => `${v}^${e}`)
    .join(",");
}

export function monoOfKey(key: string): Mono {
  const m: Mono = new Map();
  if (key === "") return m;
  for (const part of key.split(",")) {
    const i = part.lastIndexOf("^");
    m.set(part.slice(0, i), Number(part.slice(i + 1)));
  }
  return m;
}

export const pZero = (): Poly => new Map();
export const pConst = (q: Q): Poly => (qIsZero(q) ? new Map() : new Map([["", q]]));
export const pVar = (name: string): Poly => new Map([[`${name}^1`, Q1]]);

function pAddTerm(p: Poly, key: string, c: Q) {
  const cur = p.get(key);
  const v = cur === undefined ? c : qAdd(cur, c);
  if (qIsZero(v)) p.delete(key);
  else p.set(key, v);
}

export function pAdd(a: Poly, b: Poly): Poly {
  const out: Poly = new Map(a);
  for (const [k, c] of b) pAddTerm(out, k, c);
  return out;
}

export function pNeg(a: Poly): Poly {
  const out: Poly = new Map();
  for (const [k, c] of a) out.set(k, qNeg(c));
  return out;
}

export const pSub = (a: Poly, b: Poly): Poly => pAdd(a, pNeg(b));

export function pScale(a: Poly, s: Q): Poly {
  if (qIsZero(s)) return new Map();
  const out: Poly = new Map();
  for (const [k, c] of a) out.set(k, qMul(c, s));
  return out;
}

export function pMul(a: Poly, b: Poly): Poly {
  const out: Poly = new Map();
  for (const [ka, ca] of a) {
    const ma = monoOfKey(ka);
    for (const [kb, cb] of b) {
      const m = new Map(ma);
      for (const [v, e] of monoOfKey(kb)) m.set(v, (m.get(v) ?? 0) + e);
      pAddTerm(out, monoKey(m), qMul(ca, cb));
    }
  }
  return out;
}

export function pPow(a: Poly, e: number): Poly {
  let out = pConst(Q1);
  for (let i = 0; i < e; i++) out = pMul(out, a);
  return out;
}

export const pIsZero = (a: Poly) => a.size === 0;

export function pEquals(a: Poly, b: Poly): boolean {
  if (a.size !== b.size) return false;
  for (const [k, c] of a) {
    const o = b.get(k);
    if (o === undefined || !c.eq(o)) return false;
  }
  return true;
}

export function pFreeVars(a: Poly): Set<string> {
  const out = new Set<string>();
  for (const k of a.keys()) for (const [v] of monoOfKey(k)) out.add(v);
  return out;
}

export function pTotalDegree(a: Poly): number {
  let d = 0;
  for (const k of a.keys()) {
    let e = 0;
    for (const [, x] of monoOfKey(k)) e += x;
    if (e > d) d = e;
  }
  return d;
}

/** Substitute variable -> polynomial, expanding. */
export function pSubst(a: Poly, name: string, repl: Poly): Poly {
  let out: Poly = new Map();
  for (const [k, c] of a) {
    const m = monoOfKey(k);
    const e = m.get(name) ?? 0;
    m.delete(name);
    let term: Poly = new Map([[monoKey(m), c]]);
    if (e > 0) term = pMul(term, pPow(repl, e));
    out = pAdd(out, term);
  }
  return out;
}

/** The constant value of a variable-free polynomial. */
export function pConstValue(a: Poly): Q {
  if (a.size === 0) return Q0;
  if (a.size === 1 && a.has("")) return a.get("")!;
  fail(`polynomial is not ground: ${[...a.keys()].join(" | ")}`);
}

// ---------------------------------------------------------------------------
// certificate terms -> polynomials (term_to_sympy + expand, in one step)
// ---------------------------------------------------------------------------

/** The pinned wire-coordinate symbol convention (bl_cert.idx_symbol_name):
 * TIdx(TVar(w), i) <-> the polynomial variable "<w>__<i>". */
export const idxSymbolName = (wire: string, i: number) => `${wire}__${i}`;

/** The predicate-hole symbol (bl_cert.HOLE). read_rows models the hole as
 * `{ k: "var", wire: null }`; the polynomial layer names it like python
 * does so ground-instance evaluation and scope bookkeeping line up. */
export const HOLE = "_hole";

/** Term -> expanded polynomial. `syms` (optional) collects every variable
 * name minted on the way — the port of term_to_sympy's `sym` registry,
 * which wire_of_sym_from later inverts for canonical-AST reconstruction. */
export function termToPoly(t: Term, syms?: Set<string>): Poly {
  switch (t.k) {
    case "const":
      return pConst(t.q);
    case "var": {
      const name = t.wire === null ? HOLE : t.wire;
      syms?.add(name);
      return pVar(name);
    }
    case "idx": {
      if (t.c.k !== "var" || t.c.wire === null)
        fail(`TIdx base must be a wire in v0+G1 emission`);
      const name = idxSymbolName(t.c.wire, t.i);
      syms?.add(name);
      return pVar(name);
    }
    case "add":
      return pAdd(termToPoly(t.l, syms), termToPoly(t.r, syms));
    case "mul":
      return pMul(termToPoly(t.l, syms), termToPoly(t.r, syms));
    case "sub":
      return pSub(termToPoly(t.l, syms), termToPoly(t.r, syms));
    case "neg":
      return pNeg(termToPoly(t.c, syms));
  }
}

// ---------------------------------------------------------------------------
// canonical polynomial term ASTs (bl_cert.canon_sympy / canon_term /
// _term_ast, decision-for-decision)
// ---------------------------------------------------------------------------

/** Primitive-integer form: clear denominators by the positive lcm, divide
 * by the positive gcd of the integer coefficients — SIGN PRESERVED (sign
 * is semantic content in an inequality atom). Sound for (t <= 0) atom
 * bodies only, whose meaning is invariant under positive scaling. */
export function canonPoly(a: Poly): Poly {
  if (a.size === 0) return a;
  const coeffs = [...a.values()];
  let denl = 1n;
  for (const c of coeffs) denl = (denl / bgcd(denl, c.d)) * c.d;
  let g = 0n;
  for (const c of coeffs) {
    const num = (c.n < 0n ? -c.n : c.n) * (denl / c.d);
    g = bgcd(g, num);
  }
  return pScale(a, mkQ(denl, g));
}

/** wire_of_sym_from: invert the symbol registry back to Term leaves.
 * "<base>__<digits>" with base a known wire -> TIdx(TVar(base), i);
 * everything else -> TVar(name). */
export function wireOfSymFrom(syms: Set<string>, wireNames?: Set<string>): Map<string, Term> {
  const out = new Map<string, Term>();
  for (const name of syms) {
    let term: Term | null = null;
    const cut = name.lastIndexOf("__");
    if (cut > 0) {
      const base = name.slice(0, cut);
      const tail = name.slice(cut + 2);
      if (/^\d+$/.test(tail) && (wireNames === undefined || wireNames.has(base)))
        term = { k: "idx", c: { k: "var", wire: base }, i: Number(tail) };
    }
    out.set(name, term ?? { k: "var", wire: name === HOLE ? null : name });
  }
  return out;
}

/** _term_ast: monomials sorted by (-total_degree, variable string); each
 * monomial a left-nested TMul of per-variable repetitions (variables in
 * name order over the WHOLE polynomial's sorted symbol list), coefficient
 * in front; the whole a right-nested TAdd. */
export function polyToTermAst(a: Poly, wireOfSym?: Map<string, Term>): Term {
  const syms = [...pFreeVars(a)].sort();
  if (syms.length === 0) return { k: "const", q: pConstValue(a) };
  type Row = { negDeg: number; varstr: string; exps: number[]; coeff: Q };
  const rows: Row[] = [];
  for (const [k, coeff] of a) {
    const m = monoOfKey(k);
    const exps = syms.map((s) => m.get(s) ?? 0);
    const deg = exps.reduce((x, y) => x + y, 0);
    const varstr = syms
      .map((s, i) => (exps[i] ? `${s}^${exps[i]}` : null))
      .filter((x) => x !== null)
      .join(",");
    rows.push({ negDeg: -deg, varstr, exps, coeff });
  }
  rows.sort((x, y) =>
    x.negDeg !== y.negDeg ? x.negDeg - y.negDeg : x.varstr < y.varstr ? -1 : x.varstr > y.varstr ? 1 : 0,
  );
  const parts: Term[] = [];
  for (const r of rows) {
    let vprod: Term | null = null;
    for (let i = 0; i < syms.length; i++) {
      for (let n = 0; n < r.exps[i]; n++) {
        const leaf: Term =
          wireOfSym?.get(syms[i]) ??
          ({ k: "var", wire: syms[i] === HOLE ? null : syms[i] } as Term);
        vprod = vprod === null ? leaf : { k: "mul", l: vprod, r: leaf };
      }
    }
    parts.push(
      vprod === null
        ? { k: "const", q: r.coeff }
        : { k: "mul", l: { k: "const", q: r.coeff }, r: vprod },
    );
  }
  let out = parts[parts.length - 1];
  for (let i = parts.length - 2; i >= 0; i--) out = { k: "add", l: parts[i], r: out };
  return out;
}

/** canon_term: canonical AST of the primitive-integer form. */
export const canonTerm = (a: Poly, wireOfSym?: Map<string, Term>): Term =>
  polyToTermAst(canonPoly(a), wireOfSym);

// ---------------------------------------------------------------------------
// simplices: barycentric coordinates (bl_bernstein.barycentric_coords)
// ---------------------------------------------------------------------------

/** Exact linear solve (Gaussian elimination over Q); null iff singular. */
function solveQ(A: Q[][], rhs: Poly[]): Poly[] | null {
  const n = A.length;
  const M: Q[][] = A.map((row) => [...row]);
  const b: Poly[] = [...rhs];
  for (let col = 0; col < n; col++) {
    let piv = -1;
    for (let r = col; r < n; r++)
      if (!qIsZero(M[r][col])) {
        piv = r;
        break;
      }
    if (piv < 0) return null;
    [M[col], M[piv]] = [M[piv], M[col]];
    [b[col], b[piv]] = [b[piv], b[col]];
    const inv = qDiv(Q1, M[col][col]);
    for (let c = col; c < n; c++) M[col][c] = qMul(M[col][c], inv);
    b[col] = pScale(b[col], inv);
    for (let r = 0; r < n; r++) {
      if (r === col || qIsZero(M[r][col])) continue;
      const f = M[r][col];
      for (let c = col; c < n; c++) M[r][c] = qSub(M[r][c], qMul(f, M[col][c]));
      b[r] = pSub(b[r], pScale(b[col], f));
    }
  }
  return b;
}

/** Affine barycentric coordinate polynomials lambda_0..lambda_n of a
 * simplex with vertices in Q^n, over ambient variables `xs`. Throws
 * CheckError on a degenerate simplex (a checker-side well-formedness
 * condition — the 'corrupted simplex' mutant class). */
export function barycentricCoords(vertices: Q[][], xs: string[]): Poly[] {
  const n = xs.length;
  if (vertices.length !== n + 1)
    fail(`need ${n + 1} vertices for an ${n}-simplex, got ${vertices.length}`);
  // Solve [V^T; 1..1] lam = [x; 1].
  const A: Q[][] = [];
  for (let i = 0; i < n; i++) A.push(vertices.map((v) => v[i]));
  A.push(vertices.map(() => Q1));
  const rhs: Poly[] = [...xs.map((x) => pVar(x)), pConst(Q1)];
  const lam = solveQ(A, rhs);
  if (lam === null) fail(`degenerate simplex`);
  return lam;
}

// ---------------------------------------------------------------------------
// Bernstein machinery (bl_bernstein.py, ported whole)
// ---------------------------------------------------------------------------

/** All alpha in N^slots with |alpha| = total, in bl_bernstein's order. */
export function multiIndices(slots: number, total: number): number[][] {
  if (slots === 0) return total === 0 ? [[]] : [];
  const out: number[][] = [];
  for (let first = 0; first <= total; first++)
    for (const rest of multiIndices(slots - 1, total - first)) out.push([first, ...rest]);
  return out;
}

export function multiIndicesUpto(slots: number, total: number): number[][] {
  const out: number[][] = [];
  for (let t = 0; t <= total; t++) out.push(...multiIndices(slots, t));
  return out;
}

const alphaKey = (alpha: readonly number[]) => alpha.join(",");

/** Degree-d Bernstein coefficients of `poly` (over ambient variables xs)
 * on the simplex `vertices`: {alphaKey: b_alpha}, exact. Throws if
 * deg > d (the off-by-one-degree mutant class is caught, not truncated). */
export function bernsteinCoeffs(
  poly: Poly,
  xs: string[],
  vertices: Q[][],
  d: number,
): Map<string, Q> {
  const n = xs.length;
  if (pTotalDegree(poly) > d)
    fail(`polynomial degree ${pTotalDegree(poly)} exceeds claimed d=${d}`);
  const lams = Array.from({ length: n + 1 }, (_, j) => `lam${j}`);
  // x_i := sum_j lam_j * (V_j)_i
  let pLam = poly;
  for (let i = 0; i < n; i++) {
    let sub = pZero();
    for (let j = 0; j <= n; j++) sub = pAdd(sub, pScale(pVar(lams[j]), vertices[j][i]));
    pLam = pSubst(pLam, xs[i], sub);
  }
  // homogenize each monomial of lam-degree e by (sum lam)^(d-e)
  let one = pZero();
  for (const l of lams) one = pAdd(one, pVar(l));
  const onePows: Poly[] = [pConst(Q1)];
  for (let e = 1; e <= d; e++) onePows.push(pMul(onePows[e - 1], one));
  let hom = pZero();
  for (const [k, c] of pLam) {
    let e = 0;
    for (const [, x] of monoOfKey(k)) e += x;
    if (e > d) fail(`homogenization: monomial degree ${e} > d=${d}`);
    hom = pAdd(hom, pMul(new Map([[k, c]]), onePows[d - e]));
  }
  const out = new Map<string, Q>();
  for (const alpha of multiIndices(n + 1, d)) {
    const m: Mono = new Map();
    for (let i = 0; i <= n; i++) if (alpha[i]) m.set(lams[i], alpha[i]);
    const c = hom.get(monoKey(m)) ?? Q0;
    out.set(alphaKey(alpha), qDiv(c, mkQ(multinom(d, alpha), 1n)));
  }
  return out;
}

/** One degree-elevation step: c'_beta = sum_i (beta_i/(e+1)) c_{beta-e_i}. */
export function elevateOnce(coeffs: Map<string, Q>, e: number): Map<string, Q> {
  const slots = coeffs.keys().next().value!.split(",").length;
  const out = new Map<string, Q>();
  for (const beta of multiIndices(slots, e + 1)) {
    let acc = Q0;
    for (let i = 0; i < slots; i++) {
      if (beta[i] > 0) {
        const lower = [...beta];
        lower[i] -= 1;
        acc = qAdd(acc, qMul(mkQ(BigInt(beta[i]), BigInt(e + 1)), coeffs.get(alphaKey(lower))!));
      }
    }
    out.set(alphaKey(beta), acc);
  }
  return out;
}

export function elevateTo(coeffs: Map<string, Q>, e: number, target: number): Map<string, Q> {
  let cur = coeffs;
  for (let ce = e; ce < target; ce++) cur = elevateOnce(cur, ce);
  return cur;
}

/** q_k on F_S (degree d - |k|) from the full family b over N^{n+1}. */
export function inwardLayerQk(
  b: Map<string, Q>,
  d: number,
  S: number[],
  k: number[],
): Map<string, Q> {
  const npl1 = b.keys().next().value!.split(",").length;
  const Sset = new Set(S);
  const Sbar: number[] = [];
  for (let i = 0; i < npl1; i++) if (!Sset.has(i)) Sbar.push(i);
  const kTotal = k.reduce((a, x) => a + x, 0);
  const out = new Map<string, Q>();
  const Ssorted = [...S].sort((a, x) => a - x);
  for (const beta of multiIndices(Sbar.length, d - kTotal)) {
    const alpha = new Array(npl1).fill(0);
    Ssorted.forEach((i, pos) => (alpha[i] = k[pos]));
    Sbar.forEach((i, pos) => (alpha[i] = beta[pos]));
    out.set(alphaKey(beta), b.get(alphaKey(alpha))!);
  }
  return out;
}

/** Degree-d coefficients (on F_S) of the forward-difference P_j. */
export function forwardDiffPj(
  b: Map<string, Q>,
  d: number,
  S: number[],
  j: number[],
): Map<string, Q> {
  const npl1 = b.keys().next().value!.split(",").length;
  const Sset = new Set(S);
  const Sbar: number[] = [];
  for (let i = 0; i < npl1; i++) if (!Sset.has(i)) Sbar.push(i);
  const acc = new Map<string, Q>();
  for (const gamma of multiIndices(Sbar.length, d)) acc.set(alphaKey(gamma), Q0);
  // k ranges over the box prod [0..j_i]
  const ks: number[][] = [[]];
  for (const ji of j) {
    const next: number[][] = [];
    for (const prefix of ks) for (let v = 0; v <= ji; v++) next.push([...prefix, v]);
    ks.length = 0;
    ks.push(...next);
  }
  for (const k of ks) {
    const kTotal = k.reduce((a, x) => a + x, 0);
    const sign = kTotal % 2 === 0 ? 1n : -1n;
    let w = 1n;
    for (let pos = 0; pos < j.length; pos++) w *= binomial(j[pos], k[pos]);
    const qk = inwardLayerQk(b, d, S, k);
    const qkD = elevateTo(qk, d - kTotal, d);
    for (const [gk, cur] of acc) acc.set(gk, qAdd(cur, qMul(mkQ(sign * w, 1n), qkD.get(gk)!)));
  }
  return acc;
}

/** The full BernCone (j, gamma) grid: Map jKey -> Map gammaKey -> Q. */
export function bernconeGrid(
  b: Map<string, Q>,
  d: number,
  S: number[],
): Map<string, Map<string, Q>> {
  const Ssorted = [...S].sort((a, x) => a - x);
  const out = new Map<string, Map<string, Q>>();
  for (const j of multiIndicesUpto(Ssorted.length, d))
    out.set(alphaKey(j), forwardDiffPj(b, d, Ssorted, j));
  return out;
}

export const qCmp = cmpQ;
