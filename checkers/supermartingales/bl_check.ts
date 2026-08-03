/**
 * bl_check.ts — the TypeScript reference checker for Bernstein Logic
 * certificates stored as geolog object rows.
 *
 * The rows-lane sibling of `bl_checker.py`, ported check-for-check over
 * the model `read_rows.ts` reconstructs: for every proof node, verify the
 * applicability side-conditions the geolog contract states, plus hypernet
 * well-formedness and the root-sequent identity (the sp conjunction is
 * synthesized and VERIFIED, never trusted). Every failure carries the
 * SAME stable check-id string as the python checker; the mutant batteries
 * and the migration differential assert on these.
 *
 * SCOPE (exactly the rows reader's subset): app-free hypernets,
 * payload-free wires, the proof rules {Ax, Cut, AndI, AndE, OrE, EqElim,
 * ConvIntro, ConvElim, BernCone, Farkas, Promise, Syzygy} and the two
 * judgment-kind roots (productLattice, enclosure). The python checker's
 * clauses for diagram-citing rules (ReLU/LiRPA family, jet-v1) have no
 * reachable inputs through this reader — `read_rows.ts` refuses those
 * certificates before checking begins — and are deliberately not ported.
 *
 * Model notes (wire-shape inversions the reader already performed):
 *   - Farkas is leaf-form: the reader verified each entry is a literal
 *     `(e <= 0)` conjunct of the node's own pre (the python reader
 *     synthesizes the equivalent PAx+PAndE extraction chains, whose
 *     checks are true by construction); this checker consumes the
 *     entries directly.
 *   - EqElim carries no `flipped` bit on the stored form; either
 *     orientation of the equality premise is accepted (the python
 *     checker pins the orientation its reader recorded).
 *
 * Trust posture: this file + `read_rows.ts` + `qpoly.ts` are the trusted
 * reference component for rows-stored certificates. Differential partner:
 * `bl_checker.py` over the same certificates' bernfmt bytes (the
 * house-side oracle since the rows migration).
 */

import { Q, RowsReader, sameTerm, sameFormula, cmpQ } from "./read_rows.ts";
import type { Term, Formula, Judgment, Proof, Simplex, BlockLatticeM } from "./read_rows.ts";
import type { Poly } from "./qpoly.ts";
import {
  CheckError,
  HOLE,
  Q0,
  Q1,
  barycentricCoords,
  bernconeGrid,
  bernsteinCoeffs,
  canonTerm,
  factorial,
  idxSymbolName,
  mkQ,
  pConst,
  pEquals,
  pFreeVars,
  pIsZero,
  pSub,
  pScale,
  pAdd,
  qAdd,
  qDiv,
  qMul,
  qSub,
  termToPoly,
  wireOfSymFrom,
} from "./qpoly.ts";

export type Failure = { id: string; where: string; detail: string };

export class Failures extends Array<Failure> {
  add(id: string, where: string, detail: string) {
    this.push({ id, where, detail });
  }
}

const CONST0: Term = { k: "const", q: Q0 };

// ---------------------------------------------------------------------------
// formula/term utilities (bl_cert.py ports over the reader's model)
// ---------------------------------------------------------------------------

export function termFreeWires(t: Term, into = new Set<string>()): Set<string> {
  switch (t.k) {
    case "const":
      return into;
    case "var":
      if (t.wire !== null) into.add(t.wire);
      return into;
    case "idx":
      return termFreeWires(t.c, into); // geolog ax/FreeInTerm_idx
    case "neg":
      return termFreeWires(t.c, into);
    default:
      termFreeWires(t.l, into);
      return termFreeWires(t.r, into);
  }
}

export function formulaFreeWires(f: Formula, into = new Set<string>()): Set<string> {
  switch (f.k) {
    case "tt":
    case "ff":
      return into;
    case "atom":
      termFreeWires(f.l, into);
      return termFreeWires(f.r, into);
    case "inreg":
      return termFreeWires(f.t, into);
    default:
      formulaFreeWires(f.l, into);
      return formulaFreeWires(f.r, into);
  }
}

/** Substitute a wire (or the predicate hole, wire === null) by a term. */
function termSubst(t: Term, wire: string | null, repl: Term): Term {
  switch (t.k) {
    case "const":
      return t;
    case "var":
      return t.wire === wire ? repl : t;
    case "idx":
      return { k: "idx", c: termSubst(t.c, wire, repl), i: t.i };
    case "neg":
      return { k: "neg", c: termSubst(t.c, wire, repl) };
    default:
      return { k: t.k, l: termSubst(t.l, wire, repl), r: termSubst(t.r, wire, repl) };
  }
}

export function formulaSubst(f: Formula, wire: string | null, repl: Term): Formula {
  switch (f.k) {
    case "tt":
    case "ff":
      return f;
    case "atom":
      return { k: "atom", op: f.op, l: termSubst(f.l, wire, repl), r: termSubst(f.r, wire, repl) };
    case "inreg":
      return { k: "inreg", t: termSubst(f.t, wire, repl), s: f.s, S: f.S };
    default:
      return { k: f.k, l: formulaSubst(f.l, wire, repl), r: formulaSubst(f.r, wire, repl) };
  }
}

/** geolog applyPredicateToTerm: substitute the placeholder hole. */
const applyPredicate = (predicate: Formula, arg: Term): Formula =>
  formulaSubst(predicate, null, arg);

function conjGet(f: Formula, path: readonly ("l" | "r")[]): Formula {
  for (const step of path) {
    if (f.k !== "and") throw new CheckError(`path step ${step} into non-conjunction ${f.k}`);
    f = step === "l" ? f.l : f.r;
  }
  return f;
}

function conjReplace(f: Formula, path: readonly ("l" | "r")[], nf: Formula): Formula {
  if (path.length === 0) return nf;
  if (f.k !== "and") throw new CheckError("path into non-conjunction");
  return path[0] === "l"
    ? { k: "and", l: conjReplace(f.l, path.slice(1), nf), r: f.r }
    : { k: "and", l: f.l, r: conjReplace(f.r, path.slice(1), nf) };
}

function conjunctList(f: Formula): Formula[] {
  return f.k === "and" ? [...conjunctList(f.l), ...conjunctList(f.r)] : [f];
}

/** Conjunct-wise premise containment (Lean `premiseContains`). */
function premiseContains(pre: Formula, sub: Formula): boolean {
  const preCs = conjunctList(pre);
  return conjunctList(sub).every((a) => preCs.some((b) => sameFormula(a, b)));
}

/** Exact evaluation of a wire-free formula (predicate instances). */
function evalGroundFormula(f: Formula): boolean {
  switch (f.k) {
    case "tt":
      return true;
    case "ff":
      return false;
    case "and":
      return evalGroundFormula(f.l) && evalGroundFormula(f.r);
    case "or":
      return evalGroundFormula(f.l) || evalGroundFormula(f.r);
    case "atom": {
      const syms = new Set<string>();
      const l = termToPoly(f.l, syms);
      const r = termToPoly(f.r, syms);
      if (syms.size) throw new CheckError("eval_ground_formula on non-ground atom");
      const c = cmpQ(groundValue(l), groundValue(r));
      switch (f.op) {
        case "<=": return c <= 0;
        case "<": return c < 0;
        case "=": return c === 0;
        case ">=": return c >= 0;
        case ">": return c > 0;
      }
    }
    default:
      throw new CheckError(`eval_ground_formula on ${f.k}`);
  }
}

function groundValue(p: Poly): Q {
  if (p.size === 0) return Q0;
  const c = p.get("");
  if (c === undefined || p.size !== 1) throw new CheckError("non-ground polynomial");
  return c;
}

// ---- predicate shape classifiers (BUILD-PLAN D1 closed enumeration) -------

function predAtoms(pred: Formula): Formula[] {
  return pred.k === "and" ? [...predAtoms(pred.l), ...predAtoms(pred.r)] : [pred];
}

function atomHoleConst(a: Formula): { op: string; c: Q } | null {
  if (a.k !== "atom") return null;
  if (a.l.k === "var" && a.l.wire === null && a.r.k === "const") return { op: a.op, c: a.r.q };
  if (a.r.k === "var" && a.r.wire === null && a.l.k === "const") return { op: a.op, c: a.l.q };
  return null;
}

function isConvexPredicate(pred: Formula): boolean {
  return predAtoms(pred).every((a) => {
    const m = atomHoleConst(a);
    return m !== null && ["<=", ">=", "="].includes(m.op);
  });
}

function isConicPredicate(pred: Formula): boolean {
  return predAtoms(pred).every((a) => {
    const m = atomHoleConst(a);
    return m !== null && ["<=", ">=", "="].includes(m.op) && m.c.n === 0n;
  });
}

/** Lean `syzygyConclusionForm`, field-for-field: the three interchangeable
 * readings of the value-exact bound (conclusion <= 0). */
function syzygyConclusionForm(conclusion: Term, post: Formula): boolean {
  if (sameFormula(post, { k: "atom", op: "<=", l: conclusion, r: CONST0 })) return true;
  if (
    conclusion.k === "neg" &&
    sameFormula(post, { k: "atom", op: ">=", l: conclusion.c, r: CONST0 })
  )
    return true;
  if (
    conclusion.k === "sub" &&
    sameFormula(post, { k: "atom", op: "<=", l: conclusion.l, r: conclusion.r })
  )
    return true;
  return false;
}

// ---------------------------------------------------------------------------
// barycentric halfspace canonical form (ConvIntro/ConvElim's shared spec)
// ---------------------------------------------------------------------------

function simplexVertices(s: Simplex): Q[][] {
  return s.coords;
}

function barycentricHalfspaceForm(term: Term, s: Simplex, S: readonly number[]): Formula {
  if (s.verts.length !== 2) throw new CheckError("v0 toy: 1D regions only");
  const x = "_x_";
  const lams = barycentricCoords(simplexVertices(s), [x]);
  const tPoly = termToPoly(term);
  const Sset = new Set(S);
  const atoms: Formula[] = [];
  for (let i = 0; i < lams.length; i++) {
    const body = Sset.has(i) ? lams[i] : pScale(lams[i], mkQ(-1n, 1n));
    // substitute x := t
    let expr: Poly = pConst(Q0);
    for (const [k, c] of body) {
      if (k === "") expr = pAdd(expr, pConst(c));
      else if (k === `${x}^1`) expr = pAdd(expr, pScale(tPoly, c));
      else throw new CheckError("barycentric coordinate is not affine");
    }
    atoms.push({ k: "atom", op: "<=", l: canonTerm(expr), r: CONST0 });
  }
  let out = atoms[atoms.length - 1];
  for (let i = atoms.length - 2; i >= 0; i--) out = { k: "and", l: atoms[i], r: out };
  return out;
}

// ---------------------------------------------------------------------------
// hypernet well-formedness (the reader subset: app-free, wires only)
// ---------------------------------------------------------------------------

function checkHypernet(r: RowsReader, fails: Failures) {
  // The rows reader enforces app-freeness (Cert/nApps == 0) and dense
  // wire indices at parse; prim-level clauses (linearity, acyclicity,
  // dtype schemas) are vacuous over an empty prim list. The name-space
  // gates remain meaningful and are kept.
  const seen = new Set<string>();
  for (const w of r.wires) {
    if (seen.has(w.name)) fails.add("wf.wire-dup", "hypernet", "duplicate wire names");
    seen.add(w.name);
    if (/^.*__\d+$/.test(w.name))
      fails.add(
        "wf.reserved-name",
        `wire ${w.name}`,
        "wire names of the form <base>__<digits> are reserved for the TIdx coordinate symbol namespace",
      );
    if (w.name === HOLE)
      fails.add("wf.hole-wire", `wire ${w.name}`, "the predicate hole cannot be declared as a wire");
  }
}

/** Lean `Hypernet.spConjunction` over an app-free hypernet: the bare tt
 * terminator (foldr (and . spFact) tt over no prims). */
const spH = (): Formula => ({ k: "tt" });

// ---------------------------------------------------------------------------
// proof checking
// ---------------------------------------------------------------------------

const proofJudgment = (p: Proof): Judgment | null =>
  p.k === "pprod" || p.k === "penc" ? null : (p as { j: Judgment }).j;

export function checkProof(node: Proof, wireNames: Set<string>, fails: Failures, where = "root") {
  if (node.k === "pprod") {
    checkProductLattice(node, fails, where);
    return;
  }
  if (node.k === "penc") {
    checkEnclosure(node, fails, where);
    return;
  }
  const c = node.j;
  for (const [side, f] of [
    ["pre", c.pre],
    ["post", c.post],
  ] as const) {
    const extra = [...formulaFreeWires(f)].filter((w) => !wireNames.has(w));
    if (extra.length)
      fails.add("wf.formula-scope", `${where}.${side}`, `unknown wires ${JSON.stringify(extra.sort())}`);
  }

  switch (node.k) {
    case "ax": {
      if (!sameFormula(c.pre, c.post)) fails.add("ax.pre-post", where, "PAx requires pre == post");
      return;
    }

    case "ande": {
      checkProof(node.prem, wireNames, fails, where + ".premise");
      const pj = proofJudgment(node.prem);
      if (!pj) {
        fails.add("ande.not-and", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(pj.pre, c.pre)) fails.add("ande.pre", where, "premise pre != conclusion pre");
      if (pj.post.k !== "and") fails.add("ande.not-and", where, "premise post is not a conjunction");
      else {
        const want = node.which === "l" ? pj.post.l : pj.post.r;
        if (!sameFormula(c.post, want))
          fails.add("ande.post", where, "conclusion is not the selected conjunct");
      }
      return;
    }

    case "andi": {
      checkProof(node.l, wireNames, fails, where + ".l");
      checkProof(node.r, wireNames, fails, where + ".r");
      const lj = proofJudgment(node.l), rj = proofJudgment(node.r);
      if (!lj || !rj) {
        fails.add("andi.pre", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(lj.pre, c.pre) || !sameFormula(rj.pre, c.pre))
        fails.add("andi.pre", where, "premise pre mismatch");
      if (!sameFormula(c.post, { k: "and", l: lj.post, r: rj.post }))
        fails.add("andi.post", where, "post != And(l.post, r.post)");
      return;
    }

    case "orectx": {
      checkProof(node.l, wireNames, fails, where + ".left");
      checkProof(node.r, wireNames, fails, where + ".right");
      const lj = proofJudgment(node.l), rj = proofJudgment(node.r);
      if (!lj || !rj) {
        fails.add("orectx.path", where, "branch concludes a non-sequent judgment");
        return;
      }
      let disj: Formula;
      try {
        disj = conjGet(c.pre, node.path);
      } catch (e) {
        fails.add("orectx.path", where, (e as Error).message);
        return;
      }
      if (disj.k !== "or") {
        fails.add("orectx.path-not-or", where, `conjunct at path is ${disj.k}, not FOr`);
        return;
      }
      if (!sameFormula(lj.pre, conjReplace(c.pre, node.path, disj.l)))
        fails.add("orectx.left-pre", where, "left pre != pre[path := left disjunct]");
      if (!sameFormula(rj.pre, conjReplace(c.pre, node.path, disj.r)))
        fails.add("orectx.right-pre", where, "right pre != pre[path := right disjunct]");
      if (!sameFormula(lj.post, c.post) || !sameFormula(rj.post, c.post))
        fails.add("orectx.post", where, "branch posts must equal conclusion post");
      return;
    }

    case "cut": {
      checkProof(node.l, wireNames, fails, where + ".left");
      checkProof(node.r, wireNames, fails, where + ".right");
      const lj = proofJudgment(node.l), rj = proofJudgment(node.r);
      if (!lj || !rj) {
        fails.add("cut.pre", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(lj.pre, c.pre)) fails.add("cut.pre", where, "left premise pre != conclusion pre");
      if (!sameFormula(lj.post, node.cf)) fails.add("cut.left-post", where, "left post != cut formula");
      if (!sameFormula(rj.pre, { k: "and", l: lj.pre, r: node.cf }))
        fails.add("cut.right-pre", where, "right pre != And(left pre, cut formula)");
      if (!sameFormula(rj.post, c.post)) fails.add("cut.post", where, "right post != conclusion post");
      return;
    }

    case "eqelim": {
      checkProof(node.eq, wireNames, fails, where + ".eq");
      checkProof(node.body, wireNames, fails, where + ".body");
      const ej = proofJudgment(node.eq), bj = proofJudgment(node.body);
      if (!ej || !bj) {
        fails.add("eqelim.pre", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(ej.pre, c.pre) || !sameFormula(bj.pre, c.pre))
        fails.add("eqelim.pre", where, "premise pre mismatch");
      // The stored form carries no orientation bit; accept (t = u) or (u = t).
      const tu: Formula = { k: "atom", op: "=", l: node.tT, r: node.tU };
      const ut: Formula = { k: "atom", op: "=", l: node.tU, r: node.tT };
      if (!sameFormula(ej.post, tu) && !sameFormula(ej.post, ut))
        fails.add("eqelim.eq-form", where, "eq premise post != (t = u) in either orientation");
      if (!sameFormula(bj.post, formulaSubst(node.bf, node.wire, node.tT)))
        fails.add("eqelim.body-sub", where, "body post != bodyForm[wire := termT]");
      if (!sameFormula(c.post, formulaSubst(node.bf, node.wire, node.tU)))
        fails.add("eqelim.concl-sub", where, "conclusion post != bodyForm[wire := termU]");
      return;
    }

    case "convintro":
    case "convelim": {
      checkProof(node.prem, wireNames, fails, where + ".premise");
      const pj = proofJudgment(node.prem);
      if (!pj) {
        fails.add("conv.pre", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(pj.pre, c.pre)) fails.add("conv.pre", where, "premise pre mismatch");
      const n = node.s.verts.length - 1;
      if (!(node.S.length < n + 1 && node.S.every((i) => i >= 0 && i <= n))) {
        fails.add("conv.S-improper", where, "S must be a PROPER subset");
        return;
      }
      let hs: Formula;
      try {
        hs = barycentricHalfspaceForm(node.t, node.s, node.S);
      } catch (e) {
        fails.add("conv.simplex-degenerate", where, (e as Error).message);
        return;
      }
      const region: Formula = { k: "inreg", t: node.t, s: node.s, S: [...node.S] };
      if (node.k === "convintro") {
        if (!sameFormula(pj.post, hs))
          fails.add("convintro.halfspace", where, "premise post != canonical barycentric halfspace form");
        if (!sameFormula(c.post, region)) fails.add("convintro.post", where, "post != region atom");
      } else {
        if (!sameFormula(pj.post, region))
          fails.add("convelim.premise", where, "premise post != region atom");
        if (!sameFormula(c.post, hs))
          fails.add("convelim.post", where, "post != canonical barycentric halfspace form");
      }
      return;
    }

    case "berncone": {
      checkProof(node.rp, wireNames, fails, where + ".region");
      const rj = proofJudgment(node.rp);
      if (!rj) {
        fails.add("berncone.pre", where, "region premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(rj.pre, c.pre)) fails.add("berncone.pre", where, "region premise pre mismatch");
      if (!sameFormula(rj.post, { k: "inreg", t: node.tx, s: node.s, S: [...node.S] }))
        fails.add("berncone.region-post", where, "region premise post != FInRegion(termX, simplex, S)");
      const ndim = node.s.verts.length - 1;
      if (!(node.S.length < ndim + 1 && node.S.every((i) => i >= 0 && i <= ndim))) {
        fails.add("berncone.S-improper", where, "S must be a PROPER subset");
        return;
      }
      if (node.S.length) {
        if (!isConicPredicate(node.pred)) {
          fails.add("berncone.predicate-conic", where, "S nonempty requires a conic predicate");
          return;
        }
      } else if (!isConvexPredicate(node.pred)) {
        fails.add("berncone.predicate-convex", where, "S empty requires a convex predicate");
        return;
      }
      if (node.tx.k !== "var" || node.tx.wire === null) {
        fails.add("berncone.termX", where, "region argument must be a wire");
        return;
      }
      const regionWire = node.tx.wire;
      const pw = termFreeWires(node.poly);
      pw.delete(regionWire);
      if (pw.size) {
        fails.add(
          "berncone.poly-scope",
          where,
          `polynomial mentions wires ${JSON.stringify([...pw].sort())} other than the region argument`,
        );
        return;
      }
      // G1 idx discipline
      const profile = termIdxProfile(node.poly);
      if (profile === null) {
        fails.add("berncone.idx-form", where, "TIdx base must be a wire");
        return;
      }
      const { bare, idxd } = profile;
      const syms = new Set<string>();
      const pexpr = termToPoly(node.poly, syms);
      let xs: string[];
      if (ndim === 1) {
        if (idxd.size) {
          fails.add("berncone.idx-on-1d", where, "TIdx coordinates over a 1-dim region (use the wire)");
          return;
        }
        xs = [regionWire];
      } else {
        if (bare.size) {
          fails.add(
            "berncone.bare-wire-ndim",
            where,
            `bare wire occurrence(s) ${JSON.stringify([...bare].sort())} over an ${ndim}-dim region (G1: coordinates via TIdx only)`,
          );
          return;
        }
        for (const key of idxd)
          if (Number(key.split(" ")[1]) >= ndim || Number(key.split(" ")[1]) < 0) {
            fails.add("berncone.idx-range", where, `TIdx index out of range for ambient dim ${ndim}`);
            return;
          }
        xs = Array.from({ length: ndim }, (_, i) => idxSymbolName(regionWire, i));
      }
      let grid: Map<string, Map<string, Q>>;
      try {
        const b = bernsteinCoeffs(pexpr, xs, simplexVertices(node.s), node.deg);
        grid = bernconeGrid(b, node.deg, [...node.S]);
      } catch (e) {
        const msg = (e as Error).message;
        fails.add(msg.includes("exceeds") ? "berncone.degree" : "berncone.compute", where, msg);
        return;
      }
      for (const [j, fam] of grid)
        for (const [gamma, val] of fam) {
          const inst = applyPredicate(node.pred, { k: "const", q: val });
          if (!evalGroundFormula(inst))
            fails.add("berncone.coeff", where, `coefficient P_${j}[${gamma}] = ${val} violates predicate`);
        }
      // (no stored grid rides the rows form; the recompute is normative)
      if (!sameFormula(c.post, applyPredicate(node.pred, node.poly)))
        fails.add("berncone.post", where, "post != predicate applied to the polynomial term");
      return;
    }

    case "farkas": {
      // Leaf-form: the reader verified each entry is a literal (e <= 0)
      // conjunct of this node's own pre (the synthesized extraction
      // chains of the bernfmt lane are true by construction).
      let combo: Poly = new Map();
      const syms = new Set<string>();
      for (let i = 0; i < node.entries.length; i++) {
        const lam = node.lambdas[i];
        if (lam.n < 0n) fails.add("farkas.lambda-negative", where, `lambda[${i}] = ${lam} < 0`);
        combo = pAdd(combo, pScale(termToPoly(node.entries[i], syms), lam));
      }
      const want = canonTerm(combo, wireOfSymFrom(syms, wireNames));
      if (!sameTerm(node.concl, want)) {
        const cdiff = pSub(termToPoly(node.concl, syms), combo);
        if (!pIsZero(cdiff))
          fails.add(
            "farkas.combination",
            where,
            "conclusion is neither the canon AST nor value-exact against the combination",
          );
      }
      if (!sameFormula(c.post, { k: "atom", op: "<=", l: node.concl, r: CONST0 }))
        fails.add("farkas.post", where, "post != (conclusion <= 0)");
      return;
    }

    case "promise": {
      checkProof(node.sup, wireNames, fails, where + ".supplier");
      checkProof(node.con, wireNames, fails, where + ".consumer");
      const sj = proofJudgment(node.sup), kj = proofJudgment(node.con);
      if (!sj || !kj) {
        fails.add("promise.supplier-post", where, "premise concludes a non-sequent judgment");
        return;
      }
      if (!sameFormula(sj.post, node.contract))
        fails.add("promise.supplier-post", where, "supplier post != contract");
      let got: Formula;
      try {
        got = conjGet(kj.pre, node.path);
      } catch (e) {
        fails.add("promise.path", where, (e as Error).message);
        return;
      }
      if (!sameFormula(got, node.contract))
        fails.add("promise.path-reads", where, "consumer pre at path != contract");
      if (!sameFormula(c.pre, conjReplace(kj.pre, node.path, sj.pre)))
        fails.add("promise.pre-plumb", where, "conclusion pre != consumer pre[path := supplier pre]");
      if (!sameFormula(c.post, kj.post)) fails.add("promise.post", where, "conclusion post != consumer post");
      const iface = new Set(node.iface);
      const contractWires = formulaFreeWires(node.contract);
      const outside = [...contractWires].filter((w) => !iface.has(w));
      if (outside.length)
        fails.add(
          "promise.contract-confined",
          where,
          `contract wires ${JSON.stringify(outside.sort())} outside the declared interface`,
        );
      const ctx = conjReplace(kj.pre, node.path, { k: "tt" });
      const ctxWires = formulaFreeWires(ctx);
      formulaFreeWires(c.post, ctxWires);
      const shared = [...formulaFreeWires(sj.pre)].filter((w) => ctxWires.has(w) && !iface.has(w));
      if (shared.length)
        fails.add(
          "promise.separation",
          where,
          `supplier-pre wires ${JSON.stringify(shared.sort())} shared with the context or conclusion outside the interface`,
        );
      return;
    }

    case "syzygy": {
      // Components are real sub-proofs; lambdas carry the signed weight
      // the reader recovered from entry polarity (dialect D's wiring).
      let combo: Poly = new Map();
      const syms = new Set<string>();
      for (let i = 0; i < node.comps.length; i++) {
        const comp = node.comps[i];
        checkProof(comp, wireNames, fails, `${where}.component[${i}]`);
        const cj = proofJudgment(comp);
        if (!cj) {
          fails.add("syzygy.component-shape", where, `component[${i}] concludes a non-sequent judgment`);
          continue;
        }
        if (!premiseContains(c.pre, cj.pre))
          fails.add(
            "syzygy.premise-contains",
            where,
            `component[${i}] pre is not a sub-conjunction of the composite pre`,
          );
        const pj = cj.post;
        const lam = node.lambdas[i];
        if (pj.k === "atom" && pj.op === "=") {
          // free-sign wiring entry: lam * (l - r), any sign
          combo = pAdd(combo, pScale(pSub(termToPoly(pj.l, syms), termToPoly(pj.r, syms)), lam));
          continue;
        }
        if (pj.k !== "atom") {
          fails.add("syzygy.component-shape", where, `component[${i}] post is not an atom`);
          continue;
        }
        let poly: Poly;
        if (pj.op === "<=" || pj.op === "<")
          poly = pSub(termToPoly(pj.l, syms), termToPoly(pj.r, syms));
        else if (pj.op === ">=" || pj.op === ">")
          poly = pSub(termToPoly(pj.r, syms), termToPoly(pj.l, syms));
        else {
          fails.add(
            "syzygy.component-shape",
            where,
            `component[${i}] post has op ${JSON.stringify(pj.op)} — not a combination-bearing atom`,
          );
          continue;
        }
        if (lam.n < 0n)
          fails.add("syzygy.lambda-negative", where, `lambda[${i}] = ${lam} < 0 on a non-equality entry`);
        combo = pAdd(combo, pScale(poly, lam));
      }
      const want = canonTerm(combo, wireOfSymFrom(syms, wireNames));
      if (!sameTerm(node.concl, want)) {
        const cdiff = pSub(termToPoly(node.concl, syms), combo);
        if (!pIsZero(cdiff))
          fails.add(
            "syzygy.combination",
            where,
            "conclusion is neither the canon AST nor value-exact against the combination",
          );
      }
      if (!syzygyConclusionForm(node.concl, c.post))
        fails.add(
          "syzygy.post",
          where,
          "post is none of the syzygyConclusionForm readings (zero-form / ge-flip / literal) of the conclusion",
        );
      if (node.theta !== null) {
        const th = node.theta;
        if (!(cmpQ(th, Q0) > 0 && cmpQ(th, Q1) < 0))
          fails.add(
            "syzygy.theta-range",
            where,
            `theta = ${th} outside (0, 1) — the small-gain guard modulus range`,
          );
      }
      return;
    }
  }
}

/** (bare wires, indexed (wire, i) pairs) — null on a non-wire TIdx base. */
function termIdxProfile(
  t: Term,
): { bare: Set<string>; idxd: Set<string> } | null {
  const bare = new Set<string>();
  const idxd = new Set<string>(); // "wire i"
  const walk = (u: Term): boolean => {
    switch (u.k) {
      case "const":
        return true;
      case "var":
        if (u.wire !== null) bare.add(u.wire);
        return true;
      case "idx":
        if (u.c.k !== "var" || u.c.wire === null) return false;
        idxd.add(`${u.c.wire} ${u.i}`);
        return true;
      case "neg":
        return walk(u.c);
      default:
        return walk(u.l) && walk(u.r);
    }
  };
  return walk(t) ? { bare, idxd } : null;
}

// ---------------------------------------------------------------------------
// family-v1: blocklattice / productLattice ([F1]-[F5])
// ---------------------------------------------------------------------------

const cellsPerAxis = (L: BlockLatticeM) => L.axes.map((a) => a.grid.length - 1);
const nCells = (L: BlockLatticeM) => cellsPerAxis(L).reduce((a, b) => a * b, 1);

function cellCoords(cs: number[], idx: number): number[] {
  const out = new Array(cs.length).fill(0);
  for (let i = cs.length - 1; i >= 0; i--) {
    out[i] = idx % cs[i];
    idx = Math.floor(idx / cs[i]);
  }
  return out;
}

function cellIndex(cs: number[], co: number[]): number {
  let idx = 0;
  for (let i = 0; i < cs.length; i++) idx = idx * cs[i] + co[i];
  return idx;
}

type Facet = { idx: number; axis: number; d: -1 | 1 };

/** Canonical boundary facet list: (cell asc, axis asc, - before +);
 * grid-boundary facets excluded. */
function boundaryFacets(cells: Set<number>, cs: number[]): Facet[] {
  const out: Facet[] = [];
  for (const idx of [...cells].sort((a, b) => a - b)) {
    const co = cellCoords(cs, idx);
    for (let axis = 0; axis < cs.length; axis++) {
      for (const d of [-1, 1] as const) {
        const nb = [...co];
        nb[axis] += d;
        if (nb[axis] < 0 || nb[axis] >= cs[axis]) continue;
        if (!cells.has(cellIndex(cs, nb))) out.push({ idx, axis, d });
      }
    }
  }
  return out;
}

/** Pure tree substitution TVar(wire) -> TConst(v) (the [F2] rule-2 form). */
function substTree(t: Term, wire: string, v: Q): Term {
  switch (t.k) {
    case "var":
      return t.wire === wire ? { k: "const", q: v } : t;
    case "const":
      return t;
    case "neg":
      return { k: "neg", c: substTree(t.c, wire, v) };
    case "idx":
      return { k: "idx", c: substTree(t.c, wire, v), i: t.i };
    default:
      return { k: t.k, l: substTree(t.l, wire, v), r: substTree(t.r, wire, v) };
  }
}

function f2ExtractAtoms(
  f: Formula,
  fails: Failures,
  where: string,
): Map<string, [Q, Q]> | null {
  const out = new Map<string, [Q, Q]>();
  const walk = (g: Formula): boolean => {
    if (g.k === "and") return walk(g.l) && walk(g.r);
    if (g.k === "inreg") {
      if (g.t.k !== "var" || g.t.wire === null) {
        fails.add("fam.f2.pre-atom", where, `pre atom region argument must be a real wire`);
        return false;
      }
      if (g.S.length) {
        fails.add("fam.f2.pre-atom", where, "pre atom extension set must be empty");
        return false;
      }
      const vs = g.s.coords;
      if (vs.length !== 2 || vs[0].length !== 1 || vs[1].length !== 1) {
        fails.add("fam.f2.pre-atom", where, `pre atom region must be a 1-simplex`);
        return false;
      }
      const lo = vs[0][0], hi = vs[1][0];
      if (!(cmpQ(lo, hi) < 0)) {
        fails.add("fam.f2.pre-atom", where, `pre atom interval degenerate: [${lo}, ${hi}]`);
        return false;
      }
      const w = g.t.wire;
      if (out.has(w)) {
        fails.add("fam.f2.pre-atom", where, `two pre atoms over one wire ${w}`);
        return false;
      }
      out.set(w, [lo, hi]);
      return true;
    }
    fails.add("fam.f2.pre-shape", where, `pre must be an AND-tree of inRegion atoms; found ${g.k}`);
    return false;
  };
  return walk(f) ? out : null;
}

function f2CheckFacet(
  L: BlockLatticeM,
  k: number,
  facet: Facet,
  proof: Proof,
  fails: Failures,
  where: string,
) {
  const cs = cellsPerAxis(L);
  const co = cellCoords(cs, facet.idx);
  const g = L.axes[facet.axis].grid;
  const v = facet.d === -1 ? g[co[facet.axis]] : g[co[facet.axis] + 1];
  const wires = L.axes.map((a) => a.wire);
  const wPinned = wires[facet.axis];
  const drift = L.axes[facet.axis].drift;
  const cj = proofJudgment(proof);
  if (!cj) {
    fails.add("fam.f2.concludes", where, `facet ${k} proof concludes a non-sequent judgment`);
    return;
  }
  const post = cj.post;
  if (!(post.k === "atom" && post.r.k === "const" && (post.op === ">=" || post.op === "<="))) {
    fails.add("fam.f2.post", where, `facet ${k}: post must be FAtom(>=|<=, P, const)`);
    return;
  }
  const m = post.r.q;
  if (facet.d === -1 && !(post.op === ">=" && cmpQ(m, Q0) > 0))
    fails.add(
      "fam.f2.orientation",
      where,
      `facet ${k}: lower face (block on + side) needs >= with positive margin, got ${post.op} ${m}`,
    );
  if (facet.d === 1 && !(post.op === "<=" && cmpQ(m, Q0) < 0))
    fails.add(
      "fam.f2.orientation",
      where,
      `facet ${k}: upper face (block on - side) needs <= with negative margin, got ${post.op} ${m}`,
    );
  const wantPoly = substTree(drift, wPinned, v);
  if (!sameTerm(post.l, wantPoly))
    fails.add(
      "fam.f2.polynomial",
      where,
      `facet ${k}: polynomial != drift[${wPinned} := ${v}] (pure tree substitution)`,
    );
  const atoms = f2ExtractAtoms(cj.pre, fails, `${where}.facet${k}`);
  if (atoms === null) return;
  for (const [w, [lo, hi]] of atoms) {
    const j = wires.indexOf(w);
    if (j < 0) {
      fails.add("fam.f2.scope", where, `facet ${k}: pre atom over foreign wire ${w}`);
      continue;
    }
    if (j !== facet.axis) {
      const want: [Q, Q] = [L.axes[j].grid[co[j]], L.axes[j].grid[co[j] + 1]];
      if (!(lo.eq(want[0]) && hi.eq(want[1])))
        fails.add(
          "fam.f2.free-interval",
          where,
          `facet ${k}: free-axis atom [${lo},${hi}] != cell interval [${want[0]},${want[1]}]`,
        );
    } else {
      const ga = L.axes[j].grid;
      if (!(lo.eq(ga[0]) && hi.eq(ga[ga.length - 1])))
        fails.add(
          "fam.f2.idle-interval",
          where,
          `facet ${k}: non-free-axis atom [${lo},${hi}] != full arena [${ga[0]},${ga[ga.length - 1]}]`,
        );
    }
  }
  const used = formulaFreeWires(cj.pre);
  formulaFreeWires(cj.post, used);
  const extra = [...used].filter((w) => !wires.includes(w));
  if (extra.length)
    fails.add("fam.f2.scope", where, `facet ${k}: conclusion mentions foreign wires ${JSON.stringify(extra.sort())}`);
}

const scalarTreeFragment = (t: Term): boolean => {
  switch (t.k) {
    case "var":
      return t.wire !== null;
    case "const":
      return true;
    case "add":
    case "mul":
    case "sub":
      return scalarTreeFragment(t.l) && scalarTreeFragment(t.r);
    default:
      return false;
  }
};

function checkBlocklattice(L: BlockLatticeM, fails: Failures, where = "lattice", checkNodes = true) {
  const wires = L.axes.map((a) => a.wire);
  if (!(L.axes.length >= 1 && L.axes.length <= 2)) {
    fails.add("fam.f1.amb-dim", where, `amb_dim ${L.axes.length} outside the family-v1 gate`);
    return;
  }
  if (new Set(wires).size !== wires.length) {
    fails.add("fam.f1.axis-wires", where, "duplicate axis wires");
    return;
  }
  for (let i = 0; i < L.axes.length; i++) {
    const { drift, grid } = L.axes[i];
    if (grid.length < 2 || grid.some((x, k2) => k2 + 1 < grid.length && !(cmpQ(x, grid[k2 + 1]) < 0))) {
      fails.add("fam.f1.gridlines", where, `axis ${i}: gridlines must be >= 2, strictly increasing`);
      return;
    }
    const leak = [...termFreeWires(drift)].filter((w) => !wires.includes(w));
    if (leak.length)
      fails.add("fam.f3.confinement", where, `axis ${i} drift mentions non-axis wires ${JSON.stringify(leak.sort())}`);
    if (!scalarTreeFragment(drift))
      fails.add("fam.f1.drift-fragment", where, `axis ${i} drift outside the scalar tree fragment (F-A5)`);
  }
  const n = nCells(L);
  const cs = cellsPerAxis(L);
  if (!L.blocks.length) {
    fails.add("fam.f1.blocks", where, "n_blocks must be >= 1");
    return;
  }
  const seen = new Set<string>();
  for (let bi = 0; bi < L.blocks.length; bi++) {
    const b = L.blocks[bi];
    const cellSet = new Set(b.cells);
    if (!(cellSet.size >= 1 && cellSet.size < n && b.cells.every((cix) => cix >= 0 && cix < n))) {
      fails.add("fam.f1.block-cells", where, `block ${bi}: must be a nonempty PROPER subset of the ${n} cells`);
      return;
    }
    const key = [...cellSet].sort((a, z) => a - z).join(",");
    if (seen.has(key)) {
      fails.add("fam.f1.block-dup", where, `block ${bi}: duplicate`);
      return;
    }
    seen.add(key);
    const facets = boundaryFacets(cellSet, cs);
    if (b.facets.length !== facets.length) {
      fails.add(
        "fam.f1.facet-count",
        where,
        `block ${bi}: ${b.facets.length} facet proofs != ${facets.length} recomputed boundary facets`,
      );
      return;
    }
    for (let k = 0; k < facets.length; k++) {
      if (checkNodes)
        checkProof(b.facets[k], new Set([...wires]), fails, `${where}.b${bi}.f${k}`);
      f2CheckFacet(L, k, facets[k], b.facets[k], fails, `${where}.b${bi}`);
    }
  }
}

function sameAxes(a: BlockLatticeM["axes"], b: BlockLatticeM["axes"]): boolean {
  return (
    a.length === b.length &&
    a.every(
      (ax, i) =>
        ax.wire === b[i].wire &&
        sameTerm(ax.drift, b[i].drift) &&
        ax.grid.length === b[i].grid.length &&
        ax.grid.every((g, k) => g.eq(b[i].grid[k])),
    )
  );
}

function productLatticeBlocks(left: BlockLatticeM, right: BlockLatticeM): string[] {
  const nR = nCells(right);
  const leftAll = [...left.blocks.map((b) => b.cells), Array.from({ length: nCells(left) }, (_, i) => i)];
  const rightAll = [...right.blocks.map((b) => b.cells), Array.from({ length: nR }, (_, i) => i)];
  const out: string[] = [];
  for (let i1 = 0; i1 < leftAll.length; i1++)
    for (let i2 = 0; i2 < rightAll.length; i2++) {
      if (i1 === leftAll.length - 1 && i2 === rightAll.length - 1) continue;
      const cells = new Set<number>();
      for (const a of leftAll[i1]) for (const b of rightAll[i2]) cells.add(a * nR + b);
      out.push([...cells].sort((a, b) => a - b).join(","));
    }
  return out;
}

function checkProductLattice(node: Proof & { k: "pprod" }, fails: Failures, where = "root") {
  // (the reader guarantees concludes carries the composite record)
  checkBlocklattice(node.left, fails, where + ".left");
  checkBlocklattice(node.right, fails, where + ".right");
  checkBlocklattice(node.composite, fails, where + ".composite");
  const lw = new Set(node.left.axes.map((a) => a.wire));
  const shared = node.right.axes.map((a) => a.wire).filter((w) => lw.has(w));
  if (shared.length) {
    fails.add("fam.f4.disjoint", where, `factor axis wires shared: ${JSON.stringify(shared.sort())}`);
    return;
  }
  if (!sameAxes(node.composite.axes, [...node.left.axes, ...node.right.axes])) {
    fails.add(
      "fam.f5.axes",
      where,
      "composite axes != left's then right's (wires, drift terms, gridlines verbatim)",
    );
    return;
  }
  const want = productLatticeBlocks(node.left, node.right);
  const got = node.composite.blocks.map((b) => [...b.cells].sort((a, z) => a - z).join(","));
  if (got.length !== want.length || got.some((g, i) => g !== want[i]))
    fails.add(
      "fam.f5.blocks",
      where,
      `composite blocks != extended-product enumeration (${got.length} stored vs ${want.length} expected, or order/content mismatch)`,
    );
}

// ---------------------------------------------------------------------------
// enclosure-v1: tag-28 remainder-bound check ([E1]-[E3])
// ---------------------------------------------------------------------------

function qPow(a: Q, e: number): Q {
  let out = Q1;
  for (let i = 0; i < e; i++) out = qMul(out, a);
  return out;
}

function encTailBound(n: number, r: Q): Q {
  // r^(n+1)/(n+1)! * (n+2)/(n+2-r); caller guarantees 0 <= r < n+2.
  const np2 = mkQ(BigInt(n + 2), 1n);
  return qMul(
    qDiv(qPow(r, n + 1), mkQ(factorial(n + 1), 1n)),
    qDiv(np2, qSub(np2, r)),
  );
}

function checkEnclosure(node: Proof & { k: "penc" }, fails: Failures, where = "root") {
  // func/n/r/R shapes are reader-enforced ([E1] coefficients are a pure
  // recomputation of the canonical Maclaurin prefix — no stored data to
  // compare; the executed clauses are [E2] and [E3], exactly as python).
  const { n, r, R } = node;
  if (!(cmpQ(r, Q0) >= 0 && cmpQ(r, mkQ(BigInt(n + 2), 1n)) < 0)) {
    fails.add("enc.radius", where, `radius ${r} outside [0, ${n + 2}) for n=${n}`);
    return;
  }
  if (!(cmpQ(encTailBound(n, r), R) <= 0))
    fails.add("enc.tail", where, `R = ${R} below tail(${n}, ${r}) = ${encTailBound(n, r)}`);
}

// ---------------------------------------------------------------------------
// top-level certificate check
// ---------------------------------------------------------------------------

/** Full check over a reconstructed reader: hypernet wf + root-sequent
 * identity (VC hypothesis AND synthesized SP_H — verified, never trusted)
 * + recursive proof check. Empty list <=> ACCEPT. */
export function checkCertificate(r: RowsReader): Failures {
  const fails = new Failures();
  checkHypernet(r, fails);
  if (r.root.k !== "pprod" && r.root.k !== "penc") {
    const rj = (r.root as { j: Judgment }).j;
    const expectedPre: Formula = { k: "and", l: r.vcHyp!, r: spH() };
    if (!sameFormula(rj.pre, expectedPre))
      fails.add(
        "root.pre",
        "root",
        "root pre != (VC hypothesis AND synthesized SP_H) — sp-facts are verified against the hypernet, never trusted (B4)",
      );
    if (!sameFormula(rj.post, r.vcPost!)) fails.add("root.post", "root", "root post != VC conclusion");
  }
  const wireNames = new Set(r.wires.map((w) => w.name));
  checkProof(r.root, wireNames, fails);
  return fails;
}
