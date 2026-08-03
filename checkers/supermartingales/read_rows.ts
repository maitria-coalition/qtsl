/**
 * read_rows.ts — reference reader for Bernstein Logic certificates stored
 * as GeologMeta object rows.
 *
 * The rows sibling of `read_bernfmt.py`: it parses the STORED row form
 * directly (no Rust projection anywhere in the path) and reconstructs the
 * same certificate model surface the reference checker consumes — wires,
 * the proof tree, and the root sequent's `Phi AND SP_H` decomposition.
 * Run it with node (>= 22, type stripping):
 *
 *   node --experimental-strip-types read_rows.ts \
 *     --stack BLstack.rows.txt --cert BLCert.rows.txt cert.rows.txt
 *
 * On success it prints a canonical model dump (`rows-model-dump v1`, the
 * differential-test surface shared with `dump_model.py`); on a malformed
 * or out-of-subset input it prints one `REFUSED <reason>` line and exits
 * 3 — loudly, with no partial output.
 *
 * CONTAINER SURFACE: this reader consumes the reference LISTING notation
 * (`op[i] elta/rela/funa ...`), the stable structure-normative rendering
 * of a row body. The container layer is the small `parseListing` /
 * `parseTheoryListing` pair below; a binary-cell container for the same
 * op stream can replace it without touching the semantics layer, which
 * starts at `reconstruct(ops, vocab)`.
 *
 * ROW-BODY SPEC: geolog-beta/design/c2-blcert-contract.md (C2). Section
 * references in comments below are to that contract. Name resolution
 * rides the two theory revision listings (R11: "theory meta-rows for
 * reference resolution") — the reader derives every arity, field order
 * (bytewise-sorted, C1 sect. 2), and sort expectation from the stored
 * theory rows rather than hard-coding them; only the CONSTRUCTOR set
 * (which funs define their value element) is pinned here, per C2 sect. 1.
 *
 * READER SUBSET: exactly `read_bernfmt.py`'s — app-free hypernets,
 * payload-free wires, Q/B wire dtypes, cell-free complexes, proof rules
 * {Ax, Cut, AndI, AndE, OrE, EqElim, ConvIntro, ConvElim, BernCone,
 * Farkas, Promise, Syzygy} plus the two judgment-kind roots
 * (productLattice, enclosure). Anything else is a loud REFUSED, never a
 * skip: this is a checking instrument, not a general parser.
 *
 * Wire-shape inversions mirrored from `read_bernfmt.py` (so the two
 * readers reconstruct the SAME model from their two stored forms):
 *   - `FSpH` reads back as tt (the SP_H terminus is FTrue in the model);
 *   - Farkas is stored leaf-form (combination term only); each entry
 *     must be a literal `(e <= 0)` conjunct of the node's own pre;
 *   - Syzygy lambda signs are recovered from entry polarity against the
 *     component posts;
 *   - wire names do not ride the rows; wires are named `w<index>`.
 *
 * Trust posture: untrusted tooling in exactly `read_bernfmt.py`'s sense —
 * a misparse yields a certificate that fails checking, never a false
 * ACCEPT. Differential partner: `dump_model.py` over the same
 * certificates' bernfmt bytes.
 */

// ---------------------------------------------------------------------------
// small utilities
// ---------------------------------------------------------------------------

class ReadError extends Error {}

function need(cond: unknown, msg: string): asserts cond {
  if (!cond) throw new ReadError(msg);
}

function gcd(a: bigint, b: bigint): bigint {
  a = a < 0n ? -a : a;
  while (b) [a, b] = [b, a % b];
  return a;
}

/** Canonical rational: reduced, den >= 1. Listing literals arrive
 * canonical (Literal::q_big reduces before encoding); we VERIFY rather
 * than repair — a non-canonical rational on the stored form is a refusal. */
export class Q {
  readonly n: bigint;
  readonly d: bigint;
  constructor(n: bigint, d: bigint) {
    need(d >= 1n, `rational denominator must be >= 1 (got ${d})`);
    need(d === 1n || gcd(n, d) === 1n, `non-canonical rational ${n}/${d}`);
    this.n = n;
    this.d = d;
  }
  toString() {
    return `${this.n}/${this.d}`;
  }
  eq(o: Q) {
    return this.n === o.n && this.d === o.d;
  }
  neg() {
    return new Q(-this.n, this.d);
  }
}

// ---------------------------------------------------------------------------
// container layer: the listing notation
// ---------------------------------------------------------------------------

export type Val =
  | { t: "L"; n: number } // local ref: op index
  | { t: "G"; name: string } // resolved cross-commit ref
  | { t: "nat"; v: bigint }
  | { t: "z"; v: bigint }
  | { t: "b"; v: boolean }
  | { t: "q"; v: Q }
  | { t: "str"; s: string }
  /** Opaque notation extension (`tfam:…`, `artifact:…`, …): legal in
   * THEORY listings (rows the vocabulary layer does not consume);
   * refused in certificate bodies (P-CELL). */
  | { t: "x"; raw: string };

export type Op =
  | { i: number; kind: "elta"; sort: string }
  | { i: number; kind: "rela"; rel: string; args: Val[] }
  | { i: number; kind: "funa"; fun: string; args: Val[]; value: Val };

/** One value token. The grammar is deliberately strict (unknown syntax is
 * an error, never a skip) — this parse IS the P-KIND / P-CELL layer of
 * the C2 sect. 4.2 conformance table for the listing container: only
 * elta/rela/funa rows exist here, and every cell is a ref or a
 * primordial literal. */
function parseVal(tok: string, at: string): Val {
  let m: RegExpMatchArray | null;
  if ((m = tok.match(/^L(\d+)$/))) return { t: "L", n: Number(m[1]) };
  if ((m = tok.match(/^G<([A-Za-z0-9_/@-]+)>$/))) return { t: "G", name: m[1] };
  // X<hex64>:<n> — a cross-commit ref the renderer could not name;
  // carried as an (unresolvable) G-form token: harmless in theory
  // listings, and a loud unknown-token refusal if a cert body uses one.
  if (/^X[0-9a-f]{64}:\d+$/.test(tok)) return { t: "G", name: tok };
  if ((m = tok.match(/^nat:(\d+)$/))) return { t: "nat", v: BigInt(m[1]) };
  if ((m = tok.match(/^z:(-?\d+)$/))) return { t: "z", v: BigInt(m[1]) };
  if ((m = tok.match(/^b:(true|false)$/))) return { t: "b", v: m[1] === "true" };
  if ((m = tok.match(/^q:(-?\d+)\/(\d+)$/)))
    return { t: "q", v: new Q(BigInt(m[1]), BigInt(m[2])) };
  if ((m = tok.match(/^str:"([^"\\]*)"$/))) return { t: "str", s: m[1] };
  if (/^[a-z][a-z0-9_]*:\S*$/.test(tok)) return { t: "x", raw: tok };
  throw new ReadError(`${at}: unparseable value token \`${tok}\``);
}

function splitArgs(inner: string, at: string): Val[] {
  const trimmed = inner.trim();
  if (trimmed === "") return [];
  return trimmed.split(",").map((s) => parseVal(s.trim(), at));
}

const OP_RE =
  /^op\[\s*(\d+)\] (elta sort=(\S+)|rela rel=(\S+) args=\[([^\]]*)\]|funa fun=(\S+) args=\[([^\]]*)\] value=(\S+))\s*(?:\/\/.*)?$/;

export function parseListing(text: string, name: string): Op[] {
  const ops: Op[] = [];
  let lineno = 0;
  for (const raw of text.split("\n")) {
    lineno += 1;
    const line = raw.trimEnd();
    if (line === "" || line.startsWith("//")) continue;
    const at = `${name}:${lineno}`;
    const m = line.match(OP_RE);
    need(m, `${at}: unparseable listing line`);
    const i = Number(m[1]);
    need(i === ops.length, `${at}: op index ${i}, expected ${ops.length}`);
    const ref = (tok: string): string => {
      const v = parseVal(tok, at);
      need(v.t === "L" || v.t === "G", `${at}: schema position needs a ref`);
      // A LOCAL schema ref (sort/fun/rel declared in this same body) is
      // legal in the notation but outside certificate bodies (P-KIND:
      // cert bodies carry assertion rows against external theory
      // revisions only); theory listings do use them, so resolution is
      // the caller's concern — encode as a synthetic token.
      return v.t === "G" ? v.name : `@local:${v.n}`;
    };
    if (m[3]) {
      ops.push({ i, kind: "elta", sort: ref(m[3]) });
    } else if (m[4]) {
      ops.push({ i, kind: "rela", rel: ref(m[4]), args: splitArgs(m[5], at) });
    } else {
      ops.push({
        i,
        kind: "funa",
        fun: ref(m[6]),
        args: splitArgs(m[7], at),
        value: parseVal(m[8], at),
      });
    }
  }
  return ops;
}

// ---------------------------------------------------------------------------
// theory vocabulary (R11 reference resolution, from the stored revisions)
// ---------------------------------------------------------------------------

export type FunDecl = {
  token: string;
  /** null = nullary; "unary" = single anonymous arg; else bytewise-sorted
   * record field names (C1 sect. 2 argument order). */
  domain: null | "unary" | string[];
  /** Sort tokens per argument position (parallel to the domain), for the
   * P-REF sort-agreement check; ground sorts expect literals. */
  argSorts: string[];
  codomain: string | null;
  relational: boolean;
};

export type Vocab = {
  funs: Map<string, FunDecl>;
  sorts: Set<string>;
};

/** Extract declarations from one theory revision listing. `prefix` is the
 * namespace the certificate bodies use for this revision's names
 * ("stack" / "cert" — the same tokens `render_listing` mints). */
export function parseTheoryListing(text: string, prefix: string, into: Vocab, name: string) {
  const ops = parseListing(text, name);
  // Local elta index -> meta-kind, and local sort elems -> declared name.
  const eltaSort = new Map<number, string>();
  for (const op of ops) if (op.kind === "elta") eltaSort.set(op.i, op.sort);

  const sortName = new Map<number, string>(); // local Sort elem -> token
  const funRows = new Map<number, { name?: string; argSort?: Val; codomain?: Val; relational?: boolean }>();
  const fieldRows = new Map<number, { fun?: number; name?: string; sort?: Val }>();

  const localFun = (v: Val, what: string): number => {
    need(v.t === "L", `${name}: ${what} must be a local ref`);
    return v.n;
  };
  for (const op of ops) {
    if (op.kind === "funa") {
      const sub = op.args[0];
      switch (op.fun) {
        case "Sort/name":
          need(op.value.t === "str", `${name}: Sort/name value`);
          sortName.set(localFun(sub, "Sort/name arg"), op.value.s);
          break;
        case "Fun/name": {
          need(op.value.t === "str", `${name}: Fun/name value`);
          const e = localFun(sub, "Fun/name arg");
          funRows.set(e, { ...funRows.get(e), name: op.value.s });
          break;
        }
        case "Fun/arg_sort": {
          const e = localFun(sub, "Fun/arg_sort arg");
          funRows.set(e, { ...funRows.get(e), argSort: op.value });
          break;
        }
        case "Fun/codomain": {
          const e = localFun(sub, "Fun/codomain arg");
          funRows.set(e, { ...funRows.get(e), codomain: op.value });
          break;
        }
        case "Field/fun": {
          const e = localFun(sub, "Field/fun arg");
          need(op.value.t === "L", `${name}: Field/fun value`);
          fieldRows.set(e, { ...fieldRows.get(e), fun: op.value.n });
          break;
        }
        case "Field/name": {
          const e = localFun(sub, "Field/name arg");
          need(op.value.t === "str", `${name}: Field/name value`);
          fieldRows.set(e, { ...fieldRows.get(e), name: op.value.s });
          break;
        }
        case "Field/sort": {
          const e = localFun(sub, "Field/sort arg");
          fieldRows.set(e, { ...fieldRows.get(e), sort: op.value });
          break;
        }
        default:
          break; // theory/axiom bookkeeping — not needed for resolution
      }
    } else if (op.kind === "rela" && op.rel === "Fun/relational") {
      const e = localFun(op.args[0], "Fun/relational arg");
      funRows.set(e, { ...funRows.get(e), relational: true });
    }
  }

  // Resolve a sort VALUE (local Sort elem or G<...> ground/cross ref) to
  // its canonical token.
  const sortToken = (v: Val): string => {
    if (v.t === "G") return v.name;
    if (v.t === "x") return v.raw; // e.g. tfam:Q codomains — opaque
    need(v.t === "L", `${name}: sort ref shape`);
    const n = sortName.get(v.n);
    need(n !== undefined, `${name}: sort elem L${v.n} carries no Sort/name`);
    return `${prefix}/${n}`;
  };

  for (const [, nm] of sortName) into.sorts.add(`${prefix}/${nm}`);

  // Assemble records per fun.
  const byFun = new Map<number, { name: string; sort: string }[]>();
  for (const [, f] of fieldRows) {
    if (f.fun === undefined || f.name === undefined || f.sort === undefined) continue;
    const list = byFun.get(f.fun) ?? [];
    list.push({ name: f.name, sort: sortToken(f.sort) });
    byFun.set(f.fun, list);
  }
  for (const [e, f] of funRows) {
    if (f.name === undefined) continue;
    const token = `${prefix}/${f.name}`;
    const fields = byFun.get(e);
    let domain: FunDecl["domain"];
    let argSorts: string[];
    if (fields && fields.length > 0) {
      // bytewise field order (ASCII names; UTF-16 compare coincides)
      for (const fl of fields)
        need(/^[\x20-\x7e]+$/.test(fl.name), `${name}: non-ASCII field name`);
      fields.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
      domain = fields.map((x) => x.name);
      argSorts = fields.map((x) => x.sort);
    } else if (f.argSort !== undefined) {
      domain = "unary";
      argSorts = [sortToken(f.argSort)];
    } else {
      domain = null;
      argSorts = [];
    }
    into.funs.set(token, {
      token,
      domain,
      argSorts,
      codomain: f.codomain !== undefined ? sortToken(f.codomain) : null,
      relational: f.relational ?? false,
    });
  }
}

// ---------------------------------------------------------------------------
// the model (mirrors bl_cert.py's shapes; plain tagged objects)
// ---------------------------------------------------------------------------

export type Term =
  | { k: "var"; wire: string | null } // null = the predicate hole
  | { k: "const"; q: Q }
  | { k: "add" | "mul" | "sub"; l: Term; r: Term }
  | { k: "neg"; c: Term }
  | { k: "idx"; c: Term; i: number };

export type Simplex = { k: "splx"; complex: number; verts: number[]; coords: Q[][] };

export type Formula =
  | { k: "tt" }
  | { k: "ff" }
  | { k: "atom"; op: "<" | "<=" | "=" | ">=" | ">"; l: Term; r: Term }
  | { k: "inreg"; t: Term; s: Simplex; S: number[] }
  | { k: "and" | "or"; l: Formula; r: Formula };

export type Judgment = { k: "judg"; pre: Formula; post: Formula };

export type BLAxisM = { wire: string; drift: Term; grid: Q[] };
export type FamBlockM = { cells: number[]; facets: Proof[] };
export type BlockLatticeM = { axes: BLAxisM[]; blocks: FamBlockM[] };

export type Proof =
  | { k: "ax"; j: Judgment }
  | { k: "cut"; j: Judgment; cf: Formula; l: Proof; r: Proof }
  | { k: "andi"; j: Judgment; l: Proof; r: Proof }
  | { k: "ande"; j: Judgment; prem: Proof; which: "l" | "r" }
  | { k: "orectx"; j: Judgment; path: ("l" | "r")[]; l: Proof; r: Proof }
  | { k: "eqelim"; j: Judgment; eq: Proof; body: Proof; wire: string | null; tT: Term; tU: Term; bf: Formula }
  | { k: "convintro" | "convelim"; j: Judgment; prem: Proof; t: Term; s: Simplex; S: number[] }
  | { k: "berncone"; j: Judgment; rp: Proof; tx: Term; s: Simplex; S: number[]; deg: number; poly: Term; pred: Formula }
  | { k: "farkas"; j: Judgment; lambdas: Q[]; entries: Term[]; concl: Term }
  | { k: "promise"; j: Judgment; sup: Proof; con: Proof; contract: Formula; path: ("l" | "r")[]; iface: string[] }
  | { k: "syzygy"; j: Judgment; comps: Proof[]; lambdas: Q[]; concl: Term; theta: Q | null }
  | { k: "pprod"; composite: BlockLatticeM; left: BlockLatticeM; right: BlockLatticeM; flows: boolean }
  | { k: "penc"; func: "exp" | "sin" | "cos"; n: number; r: Q; R: Q };

const ENC_FUNCS = ["exp", "sin", "cos"] as const;
const ATOM_OPS: Record<string, "<" | "<=" | "=" | ">=" | ">"> = {
  "stack/FAtomLT": "<",
  "stack/FAtomLE": "<=",
  "stack/FAtomEQ": "=",
  "stack/FAtomGE": ">=",
  "stack/FAtomGT": ">",
  // FAtomNE exists in the theory but not in the reader subset (mirrors
  // read_bernfmt's BOWTIE_INV) — reaching one refuses in the builder.
};

/** Funs that DEFINE their value element (C2 sect. 1 / the stack theory's
 * constructor vocabulary). Everything else is a field/assertion fun. */
const CONSTRUCTORS = new Set([
  "stack/TVar", "stack/TConst", "stack/TAdd", "stack/TMul", "stack/TSub",
  "stack/TNeg", "stack/TIdx", "cert/THole",
  "stack/FAtomLT", "stack/FAtomLE", "stack/FAtomEQ", "stack/FAtomGE",
  "stack/FAtomGT", "stack/FAtomNE", "stack/FInRegion", "stack/FAnd",
  "stack/FOr", "stack/FTrue", "stack/FFalse", "cert/FSpH",
  "stack/PathHere", "stack/PathL", "stack/PathR",
  "stack/mkDtype", "stack/mkTensorType", "stack/empty", "stack/cons",
  "stack/KBool", "stack/KInt", "stack/KRat", "stack/KF16", "stack/KBF16",
  "stack/KF32", "stack/KF64", "stack/Ss", "stack/Snn",
  "stack/Efin", "stack/Eext",
  "stack/Rexact", "stack/Rrne", "stack/Rrtz", "stack/Rrup", "stack/Rrdn",
]);

const RULE_SORTS = new Set([
  "stack/PAx", "stack/PCut", "stack/PAndI", "stack/PAndE", "stack/POrE",
  "stack/PEqElim", "stack/PConvIntro", "stack/PConvElim", "stack/PBernCone",
  "stack/PFarkas", "stack/PPromise", "stack/PSyzygy",
]);

// ---------------------------------------------------------------------------
// semantics layer: ops -> model (C2 sect. 4.2, listing container)
// ---------------------------------------------------------------------------

function valKey(v: Val): string {
  switch (v.t) {
    case "L": return `L${v.n}`;
    case "G": return `G${v.name}`;
    case "nat": return `n${v.v}`;
    case "z": return `z${v.v}`;
    case "b": return `b${v.v}`;
    case "q": return `q${v.v}`;
    case "str": return `s${v.s}`;
    case "x": return `x${v.raw}`;
  }
}

export class RowsReader {
  private ops: Op[];
  private vocab: Vocab;
  private consumed: boolean[];
  private eltaSortOf = new Map<number, string>();
  /** (fun|rel token, valKey(args)) -> op index; P-FUN duplicate gate. */
  private rowIndex = new Map<string, number>();
  /** subject elem -> list of op indices whose FIRST ref arg is that elem. */
  private bySubject = new Map<number, number[]>();
  /** constructor rows by VALUE elem. */
  private ctorOf = new Map<number, number>();

  // model tables
  private termOf = new Map<number, Term>();
  private formulaOf = new Map<number, Formula>();
  private judgOf = new Map<number, Judgment>();
  private pathOf = new Map<number, ("l" | "r")[]>();
  private simplexOf = new Map<number, Simplex>();
  private extsetOf = new Map<number, { s: Simplex; S: number[] }>();
  private proofOf = new Map<number, Proof>();
  private latticeOf = new Map<number, BlockLatticeM>();
  private dtypeOf = new Map<number, string>(); // elem -> "Q"|"B" (subset)
  private shapeOf = new Map<number, bigint[]>();
  private ttypeOf = new Map<number, { dtype: string; shape: bigint[] }>();
  private inFlight = new Set<number>(); // P-ACYCLIC belt (refs are backward, but cheap)

  wires: { name: string; dtype: string; shape: bigint[]; elem: number }[] = [];
  complexes: { elem: number; nVertices: number; ambDim: number; coords: Q[][] }[] = [];
  private complexIdxOf = new Map<number, number>();
  root!: Proof;
  vcHyp: Formula | null = null;
  vcPost: Formula | null = null;
  theta: Q | null = null;
  nProofNodes = 0;

  constructor(ops: Op[], vocab: Vocab) {
    this.ops = ops;
    this.vocab = vocab;
    this.consumed = new Array(ops.length).fill(false);
  }

  // ---- generic row access ----------------------------------------------

  private decl(token: string): FunDecl {
    const d = this.vocab.funs.get(token);
    need(d, `unknown fun/rel token \`${token}\` (P-REF: unresolvable schema ref)`);
    return d;
  }

  private checkArgs(op: Op & ({ kind: "funa" } | { kind: "rela" }), d: FunDecl) {
    const arity = d.domain === null ? 0 : d.domain === "unary" ? 1 : d.domain.length;
    need(
      op.args.length === arity,
      `op[${op.i}] ${d.token}: ${op.args.length} args, declaration has ${arity} (P-ARGS)`,
    );
    for (let k = 0; k < arity; k++) {
      const want = d.argSorts[k];
      const got = op.args[k];
      if (want === "Nat") need(got.t === "nat", `op[${op.i}] ${d.token} arg ${k}: Nat position needs a nat literal (P-CELL)`);
      else if (want === "Q") need(got.t === "q", `op[${op.i}] ${d.token} arg ${k}: Q position needs a q literal (P-CELL)`);
      else if (want === "Z") need(got.t === "z", `op[${op.i}] ${d.token} arg ${k}: Z position needs a z literal (P-CELL)`);
      else if (want === "B") need(got.t === "b", `op[${op.i}] ${d.token} arg ${k}: B position needs a b literal (P-CELL)`);
      else if (want === "Str") need(got.t === "str", `op[${op.i}] ${d.token} arg ${k}: Str position needs a str literal (P-CELL)`);
      else {
        need(got.t === "L", `op[${op.i}] ${d.token} arg ${k}: element position needs a local ref (P-REF)`);
        need(got.n < op.i, `op[${op.i}] ${d.token} arg ${k}: ref L${got.n} is not backward (P-REF)`);
        const s = this.eltaSortOf.get(got.n);
        need(s !== undefined, `op[${op.i}] ${d.token} arg ${k}: L${got.n} is not an element (P-REF)`);
        need(s === want, `op[${op.i}] ${d.token} arg ${k}: element of sort ${s}, declaration wants ${want} (P-REF)`);
      }
    }
  }

  private index() {
    for (const op of this.ops) {
      if (op.kind === "elta") {
        need(this.vocab.sorts.has(op.sort), `op[${op.i}]: unknown sort \`${op.sort}\` (P-REF)`);
        this.eltaSortOf.set(op.i, op.sort);
        continue;
      }
      const token = op.kind === "rela" ? op.rel : op.fun;
      const d = this.decl(token);
      if (op.kind === "rela") need(d.relational, `op[${op.i}]: ${token} is not relational (P-KIND)`);
      else need(!d.relational, `op[${op.i}]: relational ${token} used as funa (P-KIND)`);
      this.checkArgs(op, d);
      const key = `${token}|${op.args.map(valKey).join(",")}`;
      need(!this.rowIndex.has(key), `op[${op.i}]: duplicate row for (${token}, args) — first at op[${this.rowIndex.get(key)}] (P-FUN)`);
      this.rowIndex.set(key, op.i);
      if (op.kind === "funa") {
        // value-position hygiene: refs must be backward element refs
        if (op.value.t === "L") {
          need(op.value.n < op.i, `op[${op.i}] ${token}: value ref L${op.value.n} is not backward (P-REF)`);
          need(this.eltaSortOf.has(op.value.n), `op[${op.i}] ${token}: value L${op.value.n} is not an element (P-REF)`);
          if (d.codomain !== null) {
            const s = this.eltaSortOf.get(op.value.n);
            need(s === d.codomain, `op[${op.i}] ${token}: value of sort ${s}, codomain is ${d.codomain} (P-REF)`);
          }
        }
        need(op.value.t !== "G", `op[${op.i}] ${token}: cross-commit value refs are outside certificate bodies (P-KIND)`);
        need(op.value.t !== "x", `op[${op.i}] ${token}: notation-extension value \`${(op.value as { raw: string }).raw}\` outside certificate bodies (P-CELL)`);
        if (CONSTRUCTORS.has(token)) {
          need(op.value.t === "L", `op[${op.i}] ${token}: constructor value must be an element ref`);
          const e = op.value.n;
          need(!this.ctorOf.has(e), `op[${op.i}] ${token}: element L${e} already constructed by op[${this.ctorOf.get(e)}] (P-FUN)`);
          this.ctorOf.set(e, op.i);
        }
      }
      const first = op.args.find((a) => a.t === "L") as { t: "L"; n: number } | undefined;
      if (first) {
        const list = this.bySubject.get(first.n) ?? [];
        list.push(op.i);
        this.bySubject.set(first.n, list);
      }
    }
  }

  private take(i: number) {
    this.consumed[i] = true;
  }

  /** The unique row (token, args starting with elem) — P-TOTAL on demand. */
  private fieldRow(token: string, elem: number): Op & { kind: "funa" } {
    const r = this.fieldRowOpt(token, elem);
    need(r, `element L${elem} (${this.eltaSortOf.get(elem)}): missing required ${token} row (P-TOTAL)`);
    return r;
  }

  private fieldRowOpt(token: string, elem: number): (Op & { kind: "funa" }) | undefined {
    const key = `${token}|L${elem}`;
    const i = this.rowIndex.get(key);
    if (i === undefined) return undefined;
    this.take(i);
    return this.ops[i] as Op & { kind: "funa" };
  }

  /** All rows of `token` whose args-position `pos` is elem (indexed
   * families / relations); consumed. */
  private rowsWith(token: string, pos: number, elem: number): (Op & ({ kind: "funa" } | { kind: "rela" }))[] {
    const out: (Op & ({ kind: "funa" } | { kind: "rela" }))[] = [];
    for (const i of this.bySubject.get(elem) ?? []) {
      const op = this.ops[i] as Op & ({ kind: "funa" } | { kind: "rela" });
      const token_i = op.kind === "rela" ? op.rel : op.fun;
      if (token_i !== token) continue;
      const a = op.args[pos];
      if (a && a.t === "L" && a.n === elem) {
        this.take(i);
        out.push(op);
      }
    }
    return out;
  }

  private natField(token: string, elem: number): bigint {
    const r = this.fieldRow(token, elem);
    need(r.value.t === "nat", `op[${r.i}] ${token}: nat value expected`);
    return r.value.v;
  }

  private refField(token: string, elem: number): number {
    const r = this.fieldRow(token, elem);
    need(r.value.t === "L", `op[${r.i}] ${token}: element value expected`);
    return r.value.n;
  }

  private ctorRow(elem: number, what: string): Op & { kind: "funa" } {
    const i = this.ctorOf.get(elem);
    need(i !== undefined, `element L${elem} (${this.eltaSortOf.get(elem)}): no constructor row (${what}) (P-TOTAL)`);
    this.take(i);
    return this.ops[i] as Op & { kind: "funa" };
  }

  private sortOf(elem: number): string {
    const s = this.eltaSortOf.get(elem);
    need(s !== undefined, `L${elem} is not an element`);
    return s;
  }

  private argRef(op: Op & { kind: "funa" }, k: number): number {
    const a = op.args[k];
    need(a.t === "L", `op[${op.i}]: arg ${k} must be an element ref`);
    return a.n;
  }

  // ---- scaffolding: dtypes, shapes, tensor types ------------------------

  private dtype(elem: number): string {
    const hit = this.dtypeOf.get(elem);
    if (hit !== undefined) return hit;
    const c = this.ctorRow(elem, "Dtype");
    need(c.fun === "stack/mkDtype", `op[${c.i}]: Dtype must be mkDtype-constructed`);
    // fields bytewise [e, k, s]
    const kElem = this.argRef(c, 1);
    const kc = this.ctorRow(kElem, "Kind");
    // consume sign + ext constants structurally (P-CONST), value-unused
    this.ctorRow(this.argRef(c, 2), "Sign");
    this.ctorRow(this.argRef(c, 0), "Ext");
    let d: string;
    if (kc.fun === "stack/KRat") d = "Q";
    else if (kc.fun === "stack/KBool") d = "B";
    else throw new ReadError(`wire dtype kind ${kc.fun} outside the checker's Q/B subset`);
    this.dtypeOf.set(elem, d);
    return d;
  }

  private shape(elem: number): bigint[] {
    const hit = this.shapeOf.get(elem);
    if (hit !== undefined) return hit;
    const c = this.ctorRow(elem, "Shape");
    let out: bigint[];
    if (c.fun === "stack/empty") out = [];
    else {
      need(c.fun === "stack/cons", `op[${c.i}]: Shape constructor`);
      // fields bytewise [head, tail]
      const head = c.args[0];
      need(head.t === "nat", `op[${c.i}] cons head`);
      out = [head.v, ...this.shape(this.argRef(c, 1))];
    }
    this.shapeOf.set(elem, out);
    return out;
  }

  private ttype(elem: number): { dtype: string; shape: bigint[] } {
    const hit = this.ttypeOf.get(elem);
    if (hit !== undefined) return hit;
    const c = this.ctorRow(elem, "TensorType");
    need(c.fun === "stack/mkTensorType", `op[${c.i}]: TensorType constructor`);
    // fields bytewise [dtype, shape]
    const out = { dtype: this.dtype(this.argRef(c, 0)), shape: this.shape(this.argRef(c, 1)) };
    this.ttypeOf.set(elem, out);
    return out;
  }

  // ---- wires ------------------------------------------------------------

  private buildWires(nWires: bigint) {
    const found = new Map<bigint, number>(); // index -> elem
    for (const [elem, sort] of this.eltaSortOf) {
      if (sort !== "stack/Wire") continue;
      const idx = this.natField("cert/Wire/index", elem);
      need(!found.has(idx), `duplicate Wire/index ${idx} (P-DENSE)`);
      need(idx < nWires, `Wire/index ${idx} >= Cert/nWires ${nWires} (P-DENSE)`);
      found.set(idx, elem);
    }
    need(BigInt(found.size) === nWires, `${found.size} wires found, Cert/nWires says ${nWires} (P-DENSE)`);
    for (let i = 0n; i < nWires; i++) {
      const elem = found.get(i)!;
      const t = this.ttype(this.refField("stack/Wire/type", elem));
      for (const p of ["Q", "Z", "B", "F16", "BF16", "F32", "F64"]) {
        need(
          this.fieldRowOpt(`cert/Wire/payload${p}`, elem) === undefined,
          `wire w${i} carries a payload row — reader subset is payload-free wires only`,
        );
      }
      this.wires.push({ name: `w${i}`, dtype: t.dtype, shape: t.shape, elem });
    }
  }

  // ---- complexes / simplices / extension sets ---------------------------

  private buildComplexes(nComplexes: bigint) {
    const found = new Map<bigint, number>();
    for (const [elem, sort] of this.eltaSortOf) {
      if (sort !== "stack/SimpC") continue;
      const idx = this.natField("cert/SimpC/index", elem);
      need(!found.has(idx), `duplicate SimpC/index ${idx} (P-DENSE)`);
      need(idx < nComplexes, `SimpC/index ${idx} >= Cert/nComplexes ${nComplexes} (P-DENSE)`);
      found.set(idx, elem);
    }
    need(BigInt(found.size) === nComplexes, `${found.size} complexes found, Cert/nComplexes says ${nComplexes} (P-DENSE)`);
    for (let ci = 0n; ci < nComplexes; ci++) {
      const elem = found.get(ci)!;
      const nV = Number(this.natField("stack/SimpC/n_vertices", elem));
      const ambD = Number(this.natField("stack/SimpC/amb_dim", elem));
      // P-CARD: exactly one coord per (v, j), in range.
      const coords: Q[][] = Array.from({ length: nV }, () => new Array(ambD).fill(undefined));
      let nCoordRows = 0;
      for (const op of this.rowsWith("stack/SimpC/coord", 0, elem)) {
        need(op.kind === "funa", "coord row kind");
        // fields bytewise [complex, j, v]
        const j = op.args[1], v = op.args[2];
        need(j.t === "nat" && v.t === "nat", `op[${op.i}] SimpC/coord j/v`);
        need(Number(v.v) < nV && Number(j.v) < ambD, `op[${op.i}] SimpC/coord (v=${v.v}, j=${j.v}) out of range (P-CARD)`);
        need(coords[Number(v.v)][Number(j.v)] === undefined, `op[${op.i}] duplicate SimpC/coord (P-CARD)`);
        need(op.value.t === "q", `op[${op.i}] SimpC/coord value`);
        coords[Number(v.v)][Number(j.v)] = op.value.v;
        nCoordRows += 1;
      }
      need(nCoordRows === nV * ambD, `complex ${ci}: ${nCoordRows} coord rows, expected ${nV}x${ambD} (P-CARD)`);
      this.complexIdxOf.set(elem, Number(ci));
      this.complexes.push({ elem, nVertices: nV, ambDim: ambD, coords });
    }
    // second pass: simplex lists + the cell-free gate (simplices may
    // reference any registered complex, so registration completes first)
    for (let ci = 0n; ci < nComplexes; ci++) {
      const elem = found.get(ci)!;
      const nSimp = this.natField("cert/SimpC/nSimplices", elem);
      const seenK = new Set<bigint>();
      for (const op of this.rowsWith("cert/ComplexSimplexAt", 0, elem)) {
        need(op.kind === "funa", "ComplexSimplexAt kind");
        const k = op.args[1];
        need(k.t === "nat", `op[${op.i}] ComplexSimplexAt k`);
        need(k.v < nSimp, `op[${op.i}] ComplexSimplexAt k=${k.v} >= nSimplices ${nSimp} (P-DENSE)`);
        need(!seenK.has(k.v), `op[${op.i}] duplicate ComplexSimplexAt k (P-DENSE)`);
        seenK.add(k.v);
        need(op.value.t === "L", `op[${op.i}] ComplexSimplexAt value`);
        const s = this.simplex(op.value.n);
        need(s.complex === Number(ci), `op[${op.i}] ComplexSimplexAt simplex belongs to complex ${s.complex}, keyed by ${ci} (P-RANGE)`);
      }
      need(BigInt(seenK.size) === nSimp, `complex ${ci}: ${seenK.size} ComplexSimplexAt rows, nSimplices says ${nSimp} (P-DENSE)`);
      const nCells = this.natField("cert/SimpC/nCells", elem);
      need(nCells === 0n, `complex ${ci}: nCells=${nCells} — reader subset is cell-free complexes (n_cells == 0)`);
    }
  }

  private simplex(elem: number): Simplex {
    const hit = this.simplexOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/Simplex", `L${elem}: expected a Simplex element`);
    const cElem = this.refField("stack/Simplex/complex", elem);
    const cIdx = this.complexIdxOf.get(cElem);
    need(cIdx !== undefined, `Simplex/complex does not point at an indexed SimpC (P-RANGE)`);
    const cx = this.complexes[cIdx];
    const verts = new Set<number>();
    for (const op of this.rowsWith("stack/Simplex/contains", 0, elem)) {
      const v = op.args[1];
      need(v.t === "nat", `op[${op.i}] Simplex/contains v`);
      need(Number(v.v) < cx.nVertices, `op[${op.i}] Simplex/contains v=${v.v} out of range (P-RANGE)`);
      need(!verts.has(Number(v.v)), `op[${op.i}] duplicate Simplex/contains (P-FUN)`);
      verts.add(Number(v.v));
    }
    const vs = [...verts].sort((a, b) => a - b);
    const s: Simplex = { k: "splx", complex: cIdx, verts: vs, coords: vs.map((v) => cx.coords[v]) };
    this.simplexOf.set(elem, s);
    return s;
  }

  /** Extension set, in the reference model's basis: S = positions into
   * the simplex's (ascending) vertex list. Rows carry complex-vertex
   * indices; a member outside the simplex is unrepresentable in the
   * reference model and refuses. */
  private extset(elem: number): { s: Simplex; S: number[] } {
    const hit = this.extsetOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/ExtensionSet", `L${elem}: expected an ExtensionSet element`);
    const s = this.simplex(this.refField("stack/ExtensionSet/simplex", elem));
    const pos = new Map<number, number>();
    s.verts.forEach((v, i) => pos.set(v, i));
    const S = new Set<number>();
    for (const op of this.rowsWith("stack/ExtensionSet/contains", 0, elem)) {
      const v = op.args[1];
      need(v.t === "nat", `op[${op.i}] ExtensionSet/contains v`);
      const p = pos.get(Number(v.v));
      need(p !== undefined, `op[${op.i}] ExtensionSet/contains v=${v.v} is not a vertex of the simplex`);
      need(!S.has(p), `op[${op.i}] duplicate ExtensionSet/contains (P-FUN)`);
      S.add(p);
    }
    const out = { s, S: [...S].sort((a, b) => a - b) };
    this.extsetOf.set(elem, out);
    return out;
  }

  // ---- terms / formulas / judgments / paths -----------------------------

  private wireName(elem: number): string {
    const w = this.wires.find((w) => w.elem === elem);
    need(w, `L${elem}: not an indexed wire`);
    return w.name;
  }

  private term(elem: number): Term {
    const hit = this.termOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/Term", `L${elem}: expected a Term element`);
    need(!this.inFlight.has(elem), `Term L${elem}: reference cycle (P-ACYCLIC)`);
    this.inFlight.add(elem);
    const c = this.ctorRow(elem, "Term");
    let t: Term;
    switch (c.fun) {
      case "cert/THole":
        t = { k: "var", wire: null };
        break;
      case "stack/TVar":
        t = { k: "var", wire: this.wireName(this.argRef(c, 0)) };
        break;
      case "stack/TConst": {
        const q = c.args[0];
        need(q.t === "q", `op[${c.i}] TConst arg`);
        t = { k: "const", q: q.v };
        break;
      }
      case "stack/TAdd":
      case "stack/TMul":
      case "stack/TSub": {
        const k = c.fun === "stack/TAdd" ? "add" : c.fun === "stack/TMul" ? "mul" : "sub";
        // fields bytewise [l, r]
        t = { k, l: this.term(this.argRef(c, 0)), r: this.term(this.argRef(c, 1)) };
        break;
      }
      case "stack/TNeg":
        t = { k: "neg", c: this.term(this.argRef(c, 0)) };
        break;
      case "stack/TIdx": {
        // fields bytewise [i, t]
        const iv = c.args[0];
        need(iv.t === "nat", `op[${c.i}] TIdx i`);
        t = { k: "idx", c: this.term(this.argRef(c, 1)), i: Number(iv.v) };
        break;
      }
      default:
        throw new ReadError(`op[${c.i}]: term constructor ${c.fun} outside the producer subset`);
    }
    this.inFlight.delete(elem);
    this.termOf.set(elem, t);
    return t;
  }

  private formula(elem: number): Formula {
    const hit = this.formulaOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/Formula", `L${elem}: expected a Formula element`);
    need(!this.inFlight.has(elem), `Formula L${elem}: reference cycle (P-ACYCLIC)`);
    this.inFlight.add(elem);
    const c = this.ctorRow(elem, "Formula");
    let f: Formula;
    if (c.fun === "stack/FTrue" || c.fun === "cert/FSpH") {
      // FSpH: the SP_H marker reads back as tt (module docstring).
      f = { k: "tt" };
    } else if (c.fun === "stack/FFalse") {
      f = { k: "ff" };
    } else if (c.fun in ATOM_OPS) {
      f = { k: "atom", op: ATOM_OPS[c.fun], l: this.term(this.argRef(c, 0)), r: this.term(this.argRef(c, 1)) };
    } else if (c.fun === "stack/FInRegion") {
      // fields bytewise [S, simplex, t]
      const es = this.extset(this.argRef(c, 0));
      const s = this.simplex(this.argRef(c, 1));
      need(sameSimplex(es.s, s), `op[${c.i}] FInRegion simplex != extset simplex`);
      f = { k: "inreg", t: this.term(this.argRef(c, 2)), s, S: es.S };
    } else if (c.fun === "stack/FAnd" || c.fun === "stack/FOr") {
      f = { k: c.fun === "stack/FAnd" ? "and" : "or", l: this.formula(this.argRef(c, 0)), r: this.formula(this.argRef(c, 1)) };
    } else {
      throw new ReadError(`op[${c.i}]: formula constructor ${c.fun} outside the producer subset`);
    }
    this.inFlight.delete(elem);
    this.formulaOf.set(elem, f);
    return f;
  }

  private judgment(elem: number): Judgment {
    const hit = this.judgOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/Judgment", `L${elem}: expected a Judgment element`);
    const j: Judgment = {
      k: "judg",
      pre: this.formula(this.refField("stack/Judgment/pre", elem)),
      post: this.formula(this.refField("stack/Judgment/post", elem)),
    };
    this.judgOf.set(elem, j);
    return j;
  }

  private path(elem: number): ("l" | "r")[] {
    const hit = this.pathOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/CtxPath", `L${elem}: expected a CtxPath element`);
    const c = this.ctorRow(elem, "CtxPath");
    let p: ("l" | "r")[];
    if (c.fun === "stack/PathHere") p = [];
    else if (c.fun === "stack/PathL") p = ["l", ...this.path(this.argRef(c, 0))];
    else if (c.fun === "stack/PathR") p = ["r", ...this.path(this.argRef(c, 0))];
    else throw new ReadError(`op[${c.i}]: CtxPath constructor ${c.fun}`);
    this.pathOf.set(elem, p);
    return p;
  }

  // ---- proofs -----------------------------------------------------------

  /** Indexed family rows: subject element at `elemPos`, dense nat key at
   * the other position (field order is bytewise, so (k,p) families carry
   * the subject at 1 while (b,f) families carry it at 0). */
  private familyRefs(token: string, elem: number, n: bigint, what: string, elemPos: 0 | 1 = 1): number[] {
    const out: (number | undefined)[] = new Array(Number(n)).fill(undefined);
    for (const op of this.rowsWith(token, elemPos, elem)) {
      need(op.kind === "funa", `${what} row kind`);
      const k = op.args[1 - elemPos];
      need(k.t === "nat", `op[${op.i}] ${what} k`);
      need(k.v < n, `op[${op.i}] ${what} k=${k.v} >= ${n} (P-CARD)`);
      need(out[Number(k.v)] === undefined, `op[${op.i}] duplicate ${what} k (P-CARD)`);
      need(op.value.t === "L", `op[${op.i}] ${what} value`);
      out[Number(k.v)] = op.value.n;
    }
    need(out.every((x) => x !== undefined), `${what}: sparse family, expected ${n} dense entries (P-CARD)`);
    return out as number[];
  }

  private proof(elem: number): Proof {
    const hit = this.proofOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/Proof", `L${elem}: expected a Proof element`);
    need(!this.inFlight.has(elem), `Proof L${elem}: reference cycle (P-ACYCLIC)`);
    this.inFlight.add(elem);
    const j = this.judgment(this.refField("stack/Proof/concludes", elem));
    // the unique rule element claiming this proof (P-TOTAL / P-ORPHAN)
    let rule: { sort: string; relem: number } | undefined;
    for (const s of RULE_SORTS) {
      const key = `${s}/proof|L`;
      void key;
    }
    // find via rowIndex: rule rows are (P<Rule>/proof, [rule elem]) value=proof
    // — indexed by VALUE, so scan the proof elem's incoming value refs.
    for (const [relem, sort] of this.eltaSortOf) {
      if (!sort.startsWith("stack/P")) continue;
      const rowKey = `${sort}/proof|L${relem}`;
      const i = this.rowIndex.get(rowKey);
      if (i === undefined) continue;
      const op = this.ops[i] as Op & { kind: "funa" };
      if (op.value.t === "L" && op.value.n === elem) {
        need(!rule, `Proof L${elem}: claimed by two rule elements (P-FUN)`);
        need(RULE_SORTS.has(sort), `Proof L${elem}: rule sort ${sort} outside the producer subset`);
        this.take(i);
        rule = { sort, relem };
      }
    }
    need(rule, `Proof L${elem}: no rule element claims it (P-TOTAL)`);
    const r = rule.relem;
    let p: Proof;
    switch (rule.sort) {
      case "stack/PAx":
        p = { k: "ax", j };
        break;
      case "stack/PCut":
        p = {
          k: "cut", j,
          cf: this.formula(this.refField("stack/PCut/cut", r)),
          l: this.proof(this.refField("stack/PCut/left", r)),
          r: this.proof(this.refField("stack/PCut/right", r)),
        };
        break;
      case "stack/PAndI":
        p = { k: "andi", j, l: this.proof(this.refField("stack/PAndI/left", r)), r: this.proof(this.refField("stack/PAndI/right", r)) };
        break;
      case "stack/PAndE": {
        const prem = this.proof(this.refField("stack/PAndE/premise", r));
        const whichN = this.natField("stack/PAndE/which", r);
        need(whichN === 0n || whichN === 1n, `PAndE/which must be 0/1`);
        const which = whichN === 0n ? "l" : "r";
        const other = this.formula(this.refField("cert/PAndE/other", r));
        const pj = prem.k === "pprod" || prem.k === "penc" ? null : (prem as { j: Judgment }).j;
        need(pj && pj.post.k === "and", `PAndE premise post is not FAnd`);
        const expect = which === "l" ? (pj.post as { r: Formula }).r : (pj.post as { l: Formula }).l;
        need(sameFormula(other, expect), `PAndE stored \`other\` != the non-selected conjunct`);
        p = { k: "ande", j, prem, which };
        break;
      }
      case "stack/POrE":
        p = {
          k: "orectx", j,
          path: this.path(this.refField("stack/POrE/path", r)),
          l: this.proof(this.refField("stack/POrE/left", r)),
          r: this.proof(this.refField("stack/POrE/right", r)),
        };
        break;
      case "stack/PEqElim": {
        const wElem = this.refField("stack/PEqElim/wire", r);
        p = {
          k: "eqelim", j,
          eq: this.proof(this.refField("stack/PEqElim/eqProof", r)),
          body: this.proof(this.refField("stack/PEqElim/bodyProof", r)),
          wire: this.wireName(wElem),
          tT: this.term(this.refField("stack/PEqElim/termT", r)),
          tU: this.term(this.refField("stack/PEqElim/termU", r)),
          bf: this.formula(this.refField("stack/PEqElim/bodyForm", r)),
        };
        break;
      }
      case "stack/PConvIntro":
      case "stack/PConvElim": {
        const base = rule.sort === "stack/PConvIntro" ? "PConvIntro" : "PConvElim";
        const s = this.simplex(this.refField(`stack/${base}/simplex`, r));
        const es = this.extset(this.refField(`stack/${base}/S`, r));
        need(sameSimplex(es.s, s), `${base} extset simplex != simplex`);
        p = {
          k: base === "PConvIntro" ? "convintro" : "convelim", j,
          prem: this.proof(this.refField(`stack/${base}/premise`, r)),
          t: this.term(this.refField(`stack/${base}/term`, r)),
          s, S: es.S,
        };
        break;
      }
      case "stack/PBernCone": {
        const s = this.simplex(this.refField("stack/PBernCone/simplex", r));
        const es = this.extset(this.refField("stack/PBernCone/S", r));
        need(sameSimplex(es.s, s), `PBernCone extset simplex != simplex`);
        p = {
          k: "berncone", j,
          rp: this.proof(this.refField("stack/PBernCone/regionProof", r)),
          tx: this.term(this.refField("stack/PBernCone/termX", r)),
          s, S: es.S,
          deg: Number(this.natField("stack/PBernCone/degree", r)),
          poly: this.term(this.refField("stack/PBernCone/polynomial", r)),
          pred: this.formula(this.refField("stack/PBernCone/predicate", r)),
        };
        break;
      }
      case "stack/PFarkas": {
        const cc = this.term(this.refField("stack/PFarkas/combinationCoeffs", r));
        const concl = this.term(this.refField("stack/PFarkas/conclusion", r));
        this.natField("stack/PFarkas/denBoundLog2", r); // Q7 metadata; no model weight
        const entries = unzipCombination(cc);
        for (const [, e] of entries)
          need(isPreConjunct(j.pre, { k: "atom", op: "<=", l: e, r: { k: "const", q: new Q(0n, 1n) } }),
            `Farkas entry is not a pre-conjunct (leaf discipline)`);
        p = { k: "farkas", j, lambdas: entries.map(([w]) => w), entries: entries.map(([, e]) => e), concl };
        break;
      }
      case "stack/PPromise": {
        const nIf = this.natField("stack/PPromise/nIfaceWires", r);
        const iface = this.familyRefs("stack/PPromise/ifaceWire", r, nIf, "PPromise/ifaceWire").map((w) => this.wireName(w));
        p = {
          k: "promise", j,
          sup: this.proof(this.refField("stack/PPromise/supplier", r)),
          con: this.proof(this.refField("stack/PPromise/consumer", r)),
          contract: this.formula(this.refField("stack/PPromise/contract", r)),
          path: this.path(this.refField("stack/PPromise/path", r)),
          iface,
        };
        break;
      }
      case "stack/PSyzygy": {
        const n = this.natField("stack/PSyzygy/nComponents", r);
        const comps = this.familyRefs("stack/PSyzygy/component", r, n, "PSyzygy/component").map((c) => this.proof(c));
        const cc = this.term(this.refField("stack/PSyzygy/combinationCoeffs", r));
        const concl = this.term(this.refField("stack/PSyzygy/conclusion", r));
        this.natField("stack/PSyzygy/denBoundLog2", r);
        const thetaRow = this.fieldRowOpt("stack/PSyzygy/theta", r);
        let theta: Q | null = null;
        if (thetaRow) {
          need(thetaRow.value.t === "q", `PSyzygy/theta value`);
          theta = thetaRow.value.v;
        }
        const entries = unzipCombination(cc);
        need(entries.length === comps.length, `syzygy combination arity != component count`);
        const lambdas: Q[] = [];
        for (let i = 0; i < entries.length; i++) {
          const [w, e] = entries[i];
          const comp = comps[i];
          const post = (comp as { j?: Judgment }).j?.post;
          need(post && post.k === "atom", `syzygy component post shape`);
          const a = post as { k: "atom"; op: string; l: Term; r: Term };
          if (a.op === "=") {
            if (sameTerm(e, { k: "sub", l: a.l, r: a.r })) lambdas.push(w);
            else if (sameTerm(e, { k: "sub", l: a.r, r: a.l })) lambdas.push(w.neg());
            else throw new ReadError(`syzygy eq-entry matches neither polarity of the component post`);
          } else {
            need(sameTerm(e, a.l), `syzygy entry != component post LHS`);
            lambdas.push(w);
          }
        }
        p = { k: "syzygy", j, comps, lambdas, concl: concl, theta };
        break;
      }
      default:
        throw new ReadError(`rule sort ${rule.sort} outside the producer subset`);
    }
    this.inFlight.delete(elem);
    this.proofOf.set(elem, p);
    this.nProofNodes += 1;
    return p;
  }

  // ---- judgment-kind roots (tags 27/28 in the wire form) ----------------

  private blocklattice(elem: number): BlockLatticeM {
    const hit = this.latticeOf.get(elem);
    if (hit) return hit;
    need(this.sortOf(elem) === "stack/BlockLattice", `L${elem}: expected a BlockLattice element`);
    const nAxes = this.natField("stack/BlockLattice/nAxes", elem);
    const nBlocks = this.natField("stack/BlockLattice/nBlocks", elem);
    // axes: BLAxis elems with lattice=elem, dense index
    const axisElems: (number | undefined)[] = new Array(Number(nAxes)).fill(undefined);
    const blockElems: (number | undefined)[] = new Array(Number(nBlocks)).fill(undefined);
    for (const [e2, sort] of this.eltaSortOf) {
      if (sort === "stack/BLAxis") {
        const latRow = this.rowIndex.get(`stack/BLAxis/lattice|L${e2}`);
        if (latRow === undefined) continue;
        const op = this.ops[latRow] as Op & { kind: "funa" };
        if (!(op.value.t === "L" && op.value.n === elem)) continue;
        this.take(latRow);
        const idx = this.natField("stack/BLAxis/index", e2);
        need(idx < nAxes, `BLAxis/index ${idx} >= nAxes (P-DENSE)`);
        need(axisElems[Number(idx)] === undefined, `duplicate BLAxis/index ${idx} (P-DENSE)`);
        axisElems[Number(idx)] = e2;
      } else if (sort === "stack/FamBlock") {
        const latRow = this.rowIndex.get(`stack/FamBlock/lattice|L${e2}`);
        if (latRow === undefined) continue;
        const op = this.ops[latRow] as Op & { kind: "funa" };
        if (!(op.value.t === "L" && op.value.n === elem)) continue;
        this.take(latRow);
        const idx = this.natField("stack/FamBlock/index", e2);
        need(idx < nBlocks, `FamBlock/index ${idx} >= nBlocks (P-DENSE)`);
        need(blockElems[Number(idx)] === undefined, `duplicate FamBlock/index ${idx} (P-DENSE)`);
        blockElems[Number(idx)] = e2;
      }
    }
    need(axisElems.every((x) => x !== undefined), `BlockLattice: sparse axes (P-DENSE)`);
    need(blockElems.every((x) => x !== undefined), `BlockLattice: sparse blocks (P-DENSE)`);
    const axes: BLAxisM[] = (axisElems as number[]).map((ax) => {
      const wire = this.wireName(this.refField("stack/BLAxis/wire", ax));
      const drift = this.term(this.refField("stack/BLAxis/drift", ax));
      const nG = this.natField("stack/BLAxis/nGridlines", ax);
      const grid: (Q | undefined)[] = new Array(Number(nG)).fill(undefined);
      for (const op of this.rowsWith("stack/BLAxis/gridline", 1, ax)) {
        need(op.kind === "funa", "gridline kind");
        const g = op.args[0];
        need(g.t === "nat" && g.v < nG, `gridline g out of range (P-CARD)`);
        need(grid[Number(g.v)] === undefined, `duplicate gridline g (P-CARD)`);
        need(op.value.t === "q", `gridline value`);
        grid[Number(g.v)] = op.value.v;
      }
      need(grid.every((x) => x !== undefined), `sparse gridlines (P-CARD)`);
      const gq = grid as Q[];
      for (let i = 0; i + 1 < gq.length; i++)
        need(cmpQ(gq[i], gq[i + 1]) < 0, `gridlines must be strictly increasing`);
      return { wire, drift, grid: gq };
    });
    const cellsPerAxis = axes.map((a) => a.grid.length - 1);
    const nCellsTotal = cellsPerAxis.reduce((a, b) => a * b, 1);
    const blocks: FamBlockM[] = (blockElems as number[]).map((b) => {
      const nC = this.natField("stack/FamBlock/nCells", b);
      const cells: (bigint | undefined)[] = new Array(Number(nC)).fill(undefined);
      for (const op of this.rowsWith("stack/FamBlock/cell", 0, b)) {
        need(op.kind === "funa", "FamBlock/cell kind");
        const c = op.args[1];
        need(c.t === "nat" && c.v < nC, `FamBlock/cell c out of range (P-CARD)`);
        need(cells[Number(c.v)] === undefined, `duplicate FamBlock/cell c (P-CARD)`);
        need(op.value.t === "nat", `FamBlock/cell value`);
        cells[Number(c.v)] = op.value.v;
      }
      need(cells.every((x) => x !== undefined), `sparse FamBlock cells (P-CARD)`);
      const cellIdx = (cells as bigint[]).map((c) => {
        need(c < BigInt(nCellsTotal), `FamBlock cell ${c} outside the grid (P-RANGE)`);
        return Number(c);
      });
      for (let i = 0; i + 1 < cellIdx.length; i++)
        need(cellIdx[i] < cellIdx[i + 1], `FamBlock cells must be strictly ascending`);
      const nF = this.natField("stack/FamBlock/nFacets", b);
      const want = boundaryFacetCount(new Set(cellIdx), cellsPerAxis);
      need(Number(nF) === want, `FamBlock facet count ${nF} != recomputed boundary count ${want}`);
      const facets = this.familyRefs("stack/FamBlock/facetProof", b, nF, "FamBlock/facetProof", 0).map((f) => this.proof(f));
      return { cells: cellIdx, facets };
    });
    const out = { axes, blocks };
    this.latticeOf.set(elem, out);
    return out;
  }

  private productLatticeRoot(elem: number): Proof {
    need(this.sortOf(elem) === "stack/PProductLattice", `root: expected PProductLattice`);
    const fj = this.refField("stack/PProductLattice/concludes", elem);
    need(this.sortOf(fj) === "stack/FamJudgment", `PProductLattice/concludes must be a FamJudgment`);
    const composite = this.blocklattice(this.refField("stack/FamJudgment/lattice", fj));
    const left = this.blocklattice(this.refField("stack/PProductLattice/left", elem));
    const right = this.blocklattice(this.refField("stack/PProductLattice/right", elem));
    const flows = this.natField("stack/PProductLattice/flowsOnly", elem);
    need(flows === 0n || flows === 1n, `flowsOnly must be 0/1`);
    this.nProofNodes += 1;
    return { k: "pprod", composite, left, right, flows: flows === 1n };
  }

  private enclosureRoot(elem: number): Proof {
    need(this.sortOf(elem) === "stack/PEnclosure", `root: expected PEnclosure`);
    const ej = this.refField("stack/PEnclosure/concludes", elem);
    need(this.sortOf(ej) === "stack/EncJudgment", `PEnclosure/concludes must be an EncJudgment`);
    const ft = this.natField("stack/EncJudgment/func", ej);
    need(ft >= 0n && ft <= 2n, `unknown enclosure func_tag ${ft}`);
    const n = Number(this.natField("stack/EncJudgment/n", ej));
    const rRow = this.fieldRow("stack/EncJudgment/r", ej);
    const capRow = this.fieldRow("stack/EncJudgment/cap", ej);
    need(rRow.value.t === "q" && capRow.value.t === "q", `EncJudgment r/cap values`);
    this.nProofNodes += 1;
    return { k: "penc", func: ENC_FUNCS[Number(ft)], n, r: rRow.value.v, R: capRow.value.v };
  }

  // ---- the top-level walk ----------------------------------------------

  reconstruct() {
    this.index();
    // P-ROOT: exactly one Cert element.
    const certs = [...this.eltaSortOf].filter(([, s]) => s === "cert/Cert").map(([e]) => e);
    need(certs.length === 1, `${certs.length} Cert elements, expected exactly 1 (P-ROOT)`);
    const cert = certs[0];
    const nWires = this.natField("cert/Cert/nWires", cert);
    const nApps = this.natField("cert/Cert/nApps", cert);
    const nComplexes = this.natField("cert/Cert/nComplexes", cert);
    need(nApps === 0n, `Cert/nApps=${nApps} — reader subset is app-free hypernets only`);
    this.buildWires(nWires);
    this.buildComplexes(nComplexes);

    const rootSeq = this.fieldRowOpt("cert/Cert/root", cert);
    const rootFam = this.fieldRowOpt("cert/Cert/rootFam", cert);
    const rootEnc = this.fieldRowOpt("cert/Cert/rootEnc", cert);
    const present = [rootSeq, rootFam, rootEnc].filter((x) => x !== undefined);
    need(present.length === 1, `expected exactly one of Cert/root|rootFam|rootEnc (P-ROOT)`);
    const rootRow = present[0]!;
    need(rootRow.value.t === "L", `Cert root value must be an element ref`);
    if (rootSeq) this.root = this.proof(rootRow.value.n);
    else if (rootFam) this.root = this.productLatticeRoot(rootRow.value.n);
    else this.root = this.enclosureRoot(rootRow.value.n);

    const thetaRow = this.fieldRowOpt("cert/Cert/theta", cert);
    if (thetaRow) {
      need(thetaRow.value.t === "q", `Cert/theta value`);
      this.theta = thetaRow.value.v;
    }
    // theta cross-check (BINARY sect. 2 transposed): Cert/theta = min over
    // present per-node syzygy thetas; absent iff none present.
    const nodeThetas: Q[] = [];
    for (const p of this.proofOf.values())
      if (p.k === "syzygy" && p.theta !== null) nodeThetas.push(p.theta);
    if (this.theta === null) {
      need(nodeThetas.length === 0, `Cert/theta absent but per-node thetas present`);
    } else {
      need(nodeThetas.length > 0, `Cert/theta present but no per-node thetas`);
      let min = nodeThetas[0];
      for (const t of nodeThetas) if (cmpQ(t, min) < 0) min = t;
      need(this.theta.eq(min), `Cert/theta != min over present per-node thetas`);
    }

    // the checker's calling convention: root pre = FAnd(vc_hyp, sp_H-terminus)
    if (this.root.k !== "pprod" && this.root.k !== "penc") {
      const pre = (this.root as { j: Judgment }).j.pre;
      need(pre.k === "and" && pre.r.k === "tt", `root pre is not FAnd(vc_hyp, sp_H-terminus)`);
      this.vcHyp = pre.l;
      this.vcPost = (this.root as { j: Judgment }).j.post;
    }

    // P-ORPHAN: every op consumed by the reconstruction.
    const orphans = this.consumed
      .map((c, i) => (c || this.ops[i].kind === "elta" ? -1 : i))
      .filter((i) => i >= 0);
    // elements are consumed via their sort census; rows must all be taken.
    need(
      orphans.length === 0,
      `orphan rows (surplus is never silently dropped, P-ORPHAN): op[${orphans.slice(0, 80).join("], op[")}]${orphans.length > 80 ? ` (+${orphans.length - 80} more)` : ""}`,
    );
    // element reachability: every elta must have been touched by some map.
    for (const [e, sort] of this.eltaSortOf) {
      const reached =
        this.termOf.has(e) || this.formulaOf.has(e) || this.judgOf.has(e) ||
        this.pathOf.has(e) || this.simplexOf.has(e) || this.extsetOf.has(e) ||
        this.proofOf.has(e) || this.latticeOf.has(e) || this.dtypeOf.has(e) ||
        this.shapeOf.has(e) || this.ttypeOf.has(e) ||
        this.wires.some((w) => w.elem === e) || this.complexIdxOf.has(e) ||
        sort === "cert/Cert" ||
        // rule elems / kind constants / fam scaffolding are consumed via
        // their rows; verify by consumption of at least one row about them
        (this.bySubject.get(e) ?? []).some((i) => this.consumed[i]) ||
        // constructed constants (value position, no arg rows)
        (this.ctorOf.has(e) && this.consumed[this.ctorOf.get(e)!]);
      need(reached, `element L${e} (${sort}) unreachable from the reconstruction (P-ORPHAN)`);
    }
  }
}

// ---- structural equality (the reconstruction interns nothing; small) ----

export function sameTerm(a: Term, b: Term): boolean {
  if (a.k !== b.k) return false;
  switch (a.k) {
    case "var": return a.wire === (b as typeof a).wire;
    case "const": return a.q.eq((b as typeof a).q);
    case "add": case "mul": case "sub": {
      const bb = b as typeof a;
      return sameTerm(a.l, bb.l) && sameTerm(a.r, bb.r);
    }
    case "neg": return sameTerm(a.c, (b as typeof a).c);
    case "idx": {
      const bb = b as typeof a;
      return a.i === bb.i && sameTerm(a.c, bb.c);
    }
  }
}

export function sameSimplex(a: Simplex, b: Simplex): boolean {
  return a.complex === b.complex && a.verts.length === b.verts.length &&
    a.verts.every((v, i) => v === b.verts[i]);
}

export function sameFormula(a: Formula, b: Formula): boolean {
  if (a.k !== b.k) return false;
  switch (a.k) {
    case "tt": case "ff": return true;
    case "atom": {
      const bb = b as typeof a;
      return a.op === bb.op && sameTerm(a.l, bb.l) && sameTerm(a.r, bb.r);
    }
    case "inreg": {
      const bb = b as typeof a;
      return sameTerm(a.t, bb.t) && sameSimplex(a.s, bb.s) &&
        a.S.length === bb.S.length && a.S.every((x, i) => x === bb.S[i]);
    }
    case "and": case "or": {
      const bb = b as typeof a;
      return sameFormula(a.l, bb.l) && sameFormula(a.r, bb.r);
    }
  }
}

export function cmpQ(a: Q, b: Q): number {
  const l = a.n * b.d, r = b.n * a.d;
  return l < r ? -1 : l > r ? 1 : 0;
}

/** Inverse of the emitter's combination-term shape:
 * add(mul(const w1, e1), add(..., const 0)) -> [(w1, e1), ...]. */
function unzipCombination(cc: Term): [Q, Term][] {
  const out: [Q, Term][] = [];
  let t = cc;
  while (t.k === "add") {
    const head = t.l;
    need(head.k === "mul" && head.l.k === "const", `combination entry is not mul(const w, e)`);
    out.push([(head.l as { k: "const"; q: Q }).q, head.r]);
    t = t.r;
  }
  need(t.k === "const" && (t as { k: "const"; q: Q }).q.n === 0n, `combination terminator is not const 0`);
  return out;
}

function isPreConjunct(pre: Formula, target: Formula): boolean {
  if (sameFormula(pre, target)) return true;
  if (pre.k === "and") return isPreConjunct(pre.l, target) || isPreConjunct(pre.r, target);
  return false;
}

/** Port of bl_cert.py BlockLattice.boundary_facets, count only. */
function boundaryFacetCount(cells: Set<number>, cs: number[]): number {
  const coords = (idx: number): number[] => {
    const co: number[] = new Array(cs.length);
    for (let a = cs.length - 1; a >= 0; a--) {
      co[a] = idx % cs[a];
      idx = Math.floor(idx / cs[a]);
    }
    return co;
  };
  const index = (co: number[]): number => co.reduce((acc, c, a) => acc * cs[a] + c, 0);
  let n = 0;
  for (const idx of [...cells].sort((a, b) => a - b)) {
    const co = coords(idx);
    for (let axis = 0; axis < cs.length; axis++) {
      for (const d of [-1, 1]) {
        const nb = co.slice();
        nb[axis] += d;
        if (nb[axis] < 0 || nb[axis] >= cs[axis]) continue;
        if (!cells.has(index(nb))) n += 1;
      }
    }
  }
  return n;
}

// ---------------------------------------------------------------------------
// canonical model dump (rows-model-dump v1 — shared with dump_model.py)
// ---------------------------------------------------------------------------

class Dumper {
  private defs: string[] = [];
  private ids = new Map<string, number>();

  private def(body: string): number {
    const hit = this.ids.get(body);
    if (hit !== undefined) return hit;
    const id = this.defs.length;
    this.defs.push(body);
    this.ids.set(body, id);
    return id;
  }

  term(t: Term): number {
    switch (t.k) {
      case "var": return this.def(t.wire === null ? "hole" : `var ${t.wire}`);
      case "const": return this.def(`const ${t.q}`);
      case "add": case "mul": case "sub":
        return this.def(`${t.k} D${this.term(t.l)} D${this.term(t.r)}`);
      case "neg": return this.def(`neg D${this.term(t.c)}`);
      case "idx": return this.def(`idx D${this.term(t.c)} ${t.i}`);
    }
  }

  simplex(s: Simplex): number {
    const coords = s.coords.map((row) => `(${row.join(",")})`).join(";");
    return this.def(`splx ${s.verts.length} [${coords}]`);
  }

  formula(f: Formula): number {
    switch (f.k) {
      case "tt": return this.def("tt");
      case "ff": return this.def("ff");
      case "atom": return this.def(`atom ${f.op} D${this.term(f.l)} D${this.term(f.r)}`);
      case "inreg": return this.def(`inreg D${this.term(f.t)} D${this.simplex(f.s)} {${f.S.join(",")}}`);
      case "and": case "or":
        return this.def(`${f.k} D${this.formula(f.l)} D${this.formula(f.r)}`);
    }
  }

  judgment(j: Judgment): number {
    return this.def(`judg D${this.formula(j.pre)} D${this.formula(j.post)}`);
  }

  lattice(bl: BlockLatticeM): number {
    const axes = bl.axes
      .map((a) => `(${a.wire} D${this.term(a.drift)} [${a.grid.join(",")}])`)
      .join(";");
    const blocks = bl.blocks
      .map((b) => `({${b.cells.join(",")}} [${b.facets.map((f) => `D${this.proof(f)}`).join(",")}])`)
      .join(";");
    return this.def(`blat [${axes}] [${blocks}]`);
  }

  proof(p: Proof): number {
    const path = (x: ("l" | "r")[]) => (x.length ? x.join("") : ".");
    switch (p.k) {
      case "ax": return this.def(`ax D${this.judgment(p.j)}`);
      case "cut":
        return this.def(`cut D${this.judgment(p.j)} D${this.formula(p.cf)} D${this.proof(p.l)} D${this.proof(p.r)}`);
      case "andi":
        return this.def(`andi D${this.judgment(p.j)} D${this.proof(p.l)} D${this.proof(p.r)}`);
      case "ande":
        return this.def(`ande D${this.judgment(p.j)} D${this.proof(p.prem)} ${p.which}`);
      case "orectx":
        return this.def(`orectx D${this.judgment(p.j)} ${path(p.path)} D${this.proof(p.l)} D${this.proof(p.r)}`);
      case "eqelim":
        return this.def(
          `eqelim D${this.judgment(p.j)} D${this.proof(p.eq)} D${this.proof(p.body)} ${p.wire ?? "hole"} D${this.term(p.tT)} D${this.term(p.tU)} D${this.formula(p.bf)}`,
        );
      case "convintro": case "convelim":
        return this.def(
          `${p.k} D${this.judgment(p.j)} D${this.proof(p.prem)} D${this.term(p.t)} D${this.simplex(p.s)} {${p.S.join(",")}}`,
        );
      case "berncone":
        return this.def(
          `berncone D${this.judgment(p.j)} D${this.proof(p.rp)} D${this.term(p.tx)} D${this.simplex(p.s)} {${p.S.join(",")}} ${p.deg} D${this.term(p.poly)} D${this.formula(p.pred)}`,
        );
      case "farkas":
        return this.def(
          `farkas D${this.judgment(p.j)} [${p.lambdas.join(",")}] [${p.entries.map((e) => `D${this.term(e)}`).join(",")}] D${this.term(p.concl)}`,
        );
      case "promise":
        return this.def(
          `promise D${this.judgment(p.j)} D${this.proof(p.sup)} D${this.proof(p.con)} D${this.formula(p.contract)} ${path(p.path)} [${p.iface.join(",")}]`,
        );
      case "syzygy":
        return this.def(
          `syzygy D${this.judgment(p.j)} [${p.comps.map((c) => `D${this.proof(c)}`).join(",")}] [${p.lambdas.join(",")}] D${this.term(p.concl)} ${p.theta ?? "-"}`,
        );
      case "pprod":
        return this.def(
          `pprod D${this.lattice(p.composite)} D${this.lattice(p.left)} D${this.lattice(p.right)} ${p.flows ? 1 : 0}`,
        );
      case "penc":
        return this.def(`penc ${p.func} ${p.n} ${p.r} ${p.R}`);
    }
  }

  render(r: RowsReader): string {
    const lines: string[] = ["FORMAT rows-model-dump v1"];
    for (const w of r.wires)
      lines.push(`W ${w.name} ${w.dtype} [${w.shape.join(",")}]`);
    const rootId = this.proof(r.root);
    const vcH = r.vcHyp === null ? "-" : `D${this.formula(r.vcHyp)}`;
    const vcP = r.vcPost === null ? "-" : `D${this.formula(r.vcPost)}`;
    this.defs.forEach((d, i) => lines.push(`D${i} ${d}`));
    lines.push(`VC_HYP ${vcH}`);
    lines.push(`VC_POST ${vcP}`);
    lines.push(`ROOT D${rootId}`);
    lines.push(
      `COUNTS wires=${r.wires.length} complexes=${r.complexes.length} proof_nodes=${r.nProofNodes} theta=${r.theta ?? "-"}`,
    );
    return lines.join("\n") + "\n";
  }
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

function readOne(vocab: Vocab, fs: typeof import("node:fs"), input: string): { text: string; code: number } {
  try {
    const ops = parseListing(fs.readFileSync(input, "utf8"), input);
    const reader = new RowsReader(ops, vocab);
    reader.reconstruct();
    return { text: new Dumper().render(reader), code: 0 };
  } catch (e) {
    if (e instanceof ReadError) return { text: `REFUSED ${e.message}\n`, code: 3 };
    throw e;
  }
}

async function main() {
  const fs = await import("node:fs");
  const path = await import("node:path");
  const argv = process.argv.slice(2);
  let stackPath = "", certPath = "", input = "", batch = "";
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] === "--stack") stackPath = argv[++i];
    else if (argv[i] === "--cert") certPath = argv[++i];
    else if (argv[i] === "--batch") batch = argv[++i];
    else input = argv[i];
  }
  if (!stackPath || !certPath || (!input && !batch)) {
    console.error(
      "usage: node --experimental-strip-types read_rows.ts --stack BLstack.rows.txt --cert BLCert.rows.txt (cert.rows.txt | --batch pairs.tsv)",
    );
    process.exit(2);
  }
  const vocab: Vocab = { funs: new Map(), sorts: new Set() };
  parseTheoryListing(fs.readFileSync(stackPath, "utf8"), "stack", vocab, stackPath);
  parseTheoryListing(fs.readFileSync(certPath, "utf8"), "cert", vocab, certPath);
  if (batch) {
    // batch: `<input>\t<output>` per line; refusals land in the output
    // file; always exit 0 (results are the files).
    for (const line of fs.readFileSync(batch, "utf8").split("\n")) {
      if (!line) continue;
      const [inp, out] = line.split("\t");
      fs.mkdirSync(path.dirname(out), { recursive: true });
      let text: string;
      try {
        text = readOne(vocab, fs, inp).text;
      } catch (e) {
        text = `CRASH ${(e as Error).message}\n`;
      }
      fs.writeFileSync(out, text);
    }
    return;
  }
  const { text, code } = readOne(vocab, fs, input);
  process.stdout.write(text);
  process.exit(code);
}

// CLI entry only when executed directly (the module surface above is
// imported by bl_check.ts / check_rows.ts without side effects).
import { pathToFileURL } from "node:url";
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
