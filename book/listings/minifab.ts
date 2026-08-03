// minifab.ts — this chapter's model, end to end on the producer surface:
// ground tables as rows, mechanisms as manifests, the composite wired,
// the specification formed, and the obligation set worked in a session
// workspace whose one move drives the release grid to checked
// certificates. Sections mirror the chapter's.

import { createHash } from "node:crypto";
import { mkdirSync, writeFileSync } from "node:fs";
import { Q, lp, spec, system } from "@maitria/mtk";
import { Workspace, type Json, type StatementKind } from "@maitria/mtk-session";
import { fluid, verdictLine, type JsFluidCert } from "./fluidseam.ts";

// ---------------------------------------------------------------- rows
// The ground tables of "The model as rows": data, not code. Stations
// are indexed 0..2, route steps 1..6; every duration is exact.

const STATION = [
  { name: "diffusion", machines: 2, bufcap: 18, batch: 3 },
  { name: "implantation", machines: 2, bufcap: 12, batch: 1 },
  { name: "lithography", machines: 1, bufcap: 12, batch: 1 },
] as const;

const ROUTE_STEP = [
  { idx: 1, st: 0, recipe: "low", proc: 225, load: 20, unload: 40 },
  { idx: 2, st: 1, recipe: "low", proc: 30, load: 15, unload: 15 },
  { idx: 3, st: 2, recipe: "low", proc: 55, load: 10, unload: 10 },
  { idx: 4, st: 1, recipe: "high", proc: 50, load: 15, unload: 15 },
  { idx: 5, st: 0, recipe: "high", proc: 255, load: 20, unload: 40 },
  { idx: 6, st: 2, recipe: "high", proc: 10, load: 10, unload: 10 },
] as const;

const WEEK_MIN = 10080;
const RELEASE = [
  { product: "Test", perWeek: 3 },
  { product: "A", perWeek: 51 }, // one lot every 3360/17 minutes — exact Q
  { product: "B", perWeek: 30 },
] as const;

const SETUP_LITHO_WORST = 12; // sequence-dependent: 5 / 10 / 12 minutes
const FAIL_IMPLANT = { tbf: ["1440", "4560"], repair: ["360", "480"] }; // uniform

// ---------------------------------------------------- mechanisms
// The compositional reading's mechanisms as manifests. The aggregate
// stratum: per-visit queue levels, a busy-machine count, and the one
// device the platform renders every duration with — a timer drifting
// at rate one. Domain constraints carry the declared capacities.

type PolyIn = { vars: number; terms: { exps: number[]; coeff: string }[] };
const mono = (vars: number, at: number): PolyIn => ({
  vars,
  terms: [{ exps: Array.from({ length: vars }, (_, j) => (j === at ? 1 : 0)), coeff: "1" }],
});
const constant = (vars: number, c: string): PolyIn => ({
  vars,
  terms: [{ exps: Array.from({ length: vars }, () => 0), coeff: c }],
});

function station(st: number): system.System {
  const visits = ROUTE_STEP.filter((r) => r.st === st); // two per station
  const n = visits.length;
  const width = n + 2; // queues, busy, timer
  return system.buildSystem({
    name: STATION[st].name,
    state: [
      ...visits.map((r, v) => ({ id: v, name: `q${r.idx}`, sort: "Nat" })),
      { id: n, name: "busy", sort: "Nat" },
      { id: n + 1, name: "tau" },
    ],
    interface: {
      inputs: visits.map((r, v) => ({ id: v, name: `arrive${r.idx}` })),
      outputs: visits.map((r, v) => ({ id: v, name: `complete${r.idx}` })),
    },
    modes: [
      {
        id: 0,
        name: "serving",
        domain: [
          ...visits.map((_, v) => ({ poly: mono(width, v), op: "ge", rhs: 0 })),
          ...visits.map((_, v) => ({
            poly: mono(width, v),
            op: "le",
            rhs: STATION[st].bufcap,
          })),
          { poly: mono(width, n), op: "ge", rhs: 0 },
          { poly: mono(width, n), op: "le", rhs: STATION[st].machines },
        ],
      },
    ],
    drift: [{ mode: 0, var: n + 1, poly: constant(width, "1") }], // tau' = 1
    init: { kind: "point", coords: Array.from({ length: width }, () => 0) },
  });
}

// Release: the thesis's constant-interval signal generators are
// literally the timer-mechanism idiom — one timer per product.
const release = system.buildSystem({
  name: "release",
  state: RELEASE.map((p, i) => ({ id: i, name: `tau_${p.product}` })),
  interface: { outputs: [{ id: 0, name: "released" }] },
  drift: RELEASE.map((_, i) => ({ mode: 0, var: i, poly: constant(3, "1") })),
  modes: [{ id: 0, name: "releasing" }],
  init: { kind: "point", coords: [0, 0, 0] },
});

const sink = system.buildSystem({
  name: "finished-lots",
  state: [
    { id: 0, name: "done", sort: "Nat" },
    { id: 1, name: "flowSum" }, // pool of realized flow times
  ],
  interface: { inputs: [{ id: 0, name: "finish" }] },
  init: { kind: "point", coords: [0, 0] },
});

// The four conserved units — operators, technician, transporter —
// as unit-capacity pool mechanisms.
const pool = (name: string) =>
  system.buildSystem({
    name,
    state: [{ id: 0, name: "held", sort: "Nat" }],
    modes: [
      {
        id: 0,
        name: "conserved",
        domain: [
          { poly: mono(1, 0), op: "ge", rhs: 0 },
          { poly: mono(1, 0), op: "le", rhs: 1 },
        ],
      },
    ],
    init: { kind: "point", coords: [0] },
  });
const pools = ["operator0", "operator1", "technician", "transporter"].map(pool);

// ---------------------------------------------------- the composite
// Directed lot flow is ordinary wiring: a station's completion wire
// feeds the next station's arrival wire, following the re-entrant
// route. The pool-membership and event-fusion seams of the figure are
// the event-port stratum — raw fusion rows now carry a producer
// surface; the pool packaging is still design-tense — and the
// dispatch freedom enters below as the certificate's policy index,
// exactly where the certified claims put it.
const [diff, impl, lith] = [station(0), station(1), station(2)];
const flow = (a: [number, number], b: [number, number]) => ({
  mode: "set" as const,
  from: { component: a[0], wire: a[1] },
  to: { component: b[0], wire: b[1] },
});
// components: 0 release, 1 diffusion, 2 implantation, 3 lithography,
// 4 sink, 5..8 pools
const fab = system.composite({
  name: "minifab",
  components: [release, diff, impl, lith, sink, ...pools],
  wiring: [
    flow([0, 0], [1, 0]), // release      -> diffusion    (step 1)
    flow([1, 0], [2, 0]), // diffusion    -> implantation (step 2)
    flow([2, 0], [3, 0]), // implantation -> lithography  (step 3)
    flow([3, 0], [2, 1]), // lithography  -> implantation (step 4)
    flow([2, 1], [1, 1]), // implantation -> diffusion    (step 5)
    flow([1, 1], [3, 1]), // diffusion    -> lithography  (step 6)
    flow([3, 1], [4, 0]), // lithography  -> finished lots
  ],
});
const notes = fab.preflight();
console.log(
  `composite: ${fab.name} (${fab.termKind}), schema ${fab.schema}; ` +
    `${notes.length} preflight notes, kinds: ` +
    [...new Set(notes.map((n) => n.kind))].join(", "),
);

// ---------------------------------------------------- the specification
// The aggregate interface the certificates are stated against: the six
// per-step levels. Work in progress is their sum, and the worked
// reading of "The certificates" is a formable claim today: from a
// ten-lot backlog at step 1 (V = 7/3), under LBFS at 84 lots/week, the
// line is empty within V/eps = 8400 minutes. Of the limsup/liminf atoms
// of "The specification", the stability atom forms below through the
// average former (poAvg, revision event 4); the throughput atom's
// former — an event rate — is still a deliberate absence of the
// language, and this file does not simulate vocabulary it lacks.
const wip = spec.unwrap(
  spec.poly(
    Array.from({ length: 6 }, (_, i) => ({
      expts: Array.from({ length: 6 }, (_, j) => (j === i ? 1 : 0)),
      coeff: 1,
    })),
  ),
);
const drainSpec = spec.build({
  name: "minifab drain: LBFS core 84/wk, ten lots at step 1",
  forall: [spec.probGe(1, spec.deadline(8400, spec.polyLe(0, wip)))],
  iface: {
    invars: [],
    outvars: ROUTE_STEP.map((r) => ({ name: `q${r.idx}`, shape: [] })),
  },
});
console.log(
  `spec: ${drainSpec.ok ? `built ("${drainSpec.value.name}")` : "refused"}`,
);

// The long-run stability atom, rendered: the Cesàro average of wip,
// capped in upper prevision over every admitted law. For the fluid
// skeleton under LBFS at 84 lots/week the honest cap is zero — the
// line drains and stays drained, so the transient washes out of the
// time average.
const longRunStable = spec.build({
  name: "minifab long-run: LBFS core 84/wk, average wip",
  forall: [spec.returnLe(0, spec.poAvg(spec.oPoly(wip)))],
  iface: {
    invars: [],
    outvars: ROUTE_STEP.map((r) => ({ name: `q${r.idx}`, shape: [] })),
  },
});
console.log(
  `spec: ${longRunStable.ok ? `built ("${longRunStable.value.name}")` : "refused"}`,
);

// ---------------------------------------------------- the fluid skeleton
// The certificates' declared network: occupancy rates from the tables
// (per-batch handling at diffusion), setup-adversarial variant as rate
// intervals, policy as priority orders. Exactly the checker's own
// vocabulary — it rebuilds every polytope from these rows.

interface Net {
  k: number;
  route: number[];
  arrivals: Q[];
  stations: number[][];
  caps: Q[];
  muLo: Q[];
  muHi: Q[];
  prio: number[][];
}

const OCC = ROUTE_STEP.map((r) => {
  const perLot = Q.of(r.load + r.proc + r.unload, STATION[r.st].batch);
  return perLot; // 95, 60, 75, 80, 105, 30 machine-minutes per lot
});
const NEXT = [2, 3, 4, 5, 6, 0]; // successor buffer of each step (0 = out)
const SERVES = [
  [1, 5],
  [2, 4],
  [3, 6],
]; // station -> buffers, 1-based
const PRIO: Record<string, number[][]> = {
  LBFS: [
    [5, 1],
    [4, 2],
    [6, 3],
  ],
  FBFS: [
    [1, 5],
    [2, 4],
    [3, 6],
  ],
};

function makeNet(policy: string, variant: string, lotsPerWeek: number): Net {
  const muHi = OCC.map((o) => Q.from(1).div(o));
  const muLo = [...muHi];
  if (variant === "setup-adversarial") {
    // every lithography job may pay the full worst-case setup
    muLo[2] = Q.from(1).div(OCC[2].add(SETUP_LITHO_WORST));
    muLo[5] = Q.from(1).div(OCC[5].add(SETUP_LITHO_WORST));
  }
  return {
    k: 6,
    route: NEXT,
    arrivals: [Q.of(lotsPerWeek, WEEK_MIN), ...Array.from({ length: 5 }, () => Q.from(0))],
    stations: SERVES,
    caps: STATION.map((s) => Q.from(s.machines)),
    muLo,
    muHi,
    prio: PRIO[policy],
  };
}

// Canonical constraint rows per sign mode, in the checker's own order:
// per-buffer drift variables T then allocations a; rate brackets,
// station capacity, nonnegativity as inequalities; conservation on
// empty buffers (the boundary-equality lemma, as algebra) and
// top-priority saturation as equalities.
type Row = { r: Q[]; rhs: Q };
const zeros = (n: number) => Array.from({ length: n }, () => Q.from(0));

function ineqRows(net: Net): Row[] {
  const k = net.k;
  const rows: Row[] = [];
  for (let i = 0; i < k; i++) {
    const r = zeros(2 * k);
    r[i] = Q.from(1);
    r[k + i] = net.muHi[i].neg();
    rows.push({ r, rhs: Q.from(0) }); // T_i <= muHi_i * a_i
  }
  for (let i = 0; i < k; i++) {
    const r = zeros(2 * k);
    r[i] = Q.from(-1);
    r[k + i] = net.muLo[i];
    rows.push({ r, rhs: Q.from(0) }); // T_i >= muLo_i * a_i
  }
  net.stations.forEach((bufs, s) => {
    const r = zeros(2 * k);
    for (const b of bufs) r[k + b - 1] = Q.from(1);
    rows.push({ r, rhs: net.caps[s] }); // sum of allocations <= machines
  });
  for (let i = 0; i < k; i++) {
    const r = zeros(2 * k);
    r[i] = Q.from(-1);
    rows.push({ r, rhs: Q.from(0) }); // T_i >= 0
  }
  for (let i = 0; i < k; i++) {
    const r = zeros(2 * k);
    r[k + i] = Q.from(-1);
    rows.push({ r, rhs: Q.from(0) }); // a_i >= 0
  }
  return rows;
}

function eqRows(net: Net, mask: number): Row[] {
  const k = net.k;
  const rows: Row[] = [];
  for (let i = 0; i < k; i++) {
    if (!((mask >> i) & 1)) {
      // buffer i empty: inflow = outflow (a.e. zero derivative)
      const r = zeros(2 * k);
      r[i] = Q.from(-1);
      net.route.forEach((succ, j) => {
        if (succ === i + 1) r[j] = r[j].add(Q.from(1));
      });
      rows.push({ r, rhs: net.arrivals[i].neg() });
    }
  }
  net.prio.forEach((order, s) => {
    for (let pos = 0; pos < order.length; pos++) {
      if ((mask >> (order[pos] - 1)) & 1) {
        // a nonempty buffer at priority: everything at or above it
        // saturates the station
        const r = zeros(2 * k);
        for (const j of order.slice(0, pos + 1)) r[k + j - 1] = Q.from(1);
        rows.push({ r, rhs: net.caps[s] });
      }
    }
  });
  return rows;
}

function objective(net: Net, w: Q[]): Q[] {
  const c = zeros(2 * net.k);
  for (let j = 0; j < net.k; j++) {
    const succ = net.route[j];
    c[j] = (succ !== 0 ? w[succ - 1] : Q.from(0)).sub(w[j]);
  }
  return c; // <w, dq/dt> as a linear form in (T, a)
}

// ---------------------------------------------------- propose, dispose
// The producer discipline of the Cookbook: a sloppy float tier
// proposes, an exact tier disposes, and nothing float is ever cited.

function proposeW(net: Net): Q[] | null {
  // One robust linear program over all 63 modes at once: weights w,
  // margin eps, and one dual multiplier per constraint row, solved in
  // floating point (HiGHS) purely as a proposal.
  const k = net.k;
  const per = Array.from({ length: (1 << k) - 1 }, (_, i) => ({
    ineqs: ineqRows(net),
    eqs: eqRows(net, i + 1),
  }));
  const cols: lp.FloatCol[] = [
    ...Array.from({ length: k }, () => ({ cost: 0, lo: 1e-7 })),
    { cost: -1, lo: 0 }, // maximize eps
  ];
  const offs: number[] = [];
  for (const { ineqs, eqs } of per) {
    offs.push(cols.length);
    for (let i = 0; i < ineqs.length; i++) cols.push({ cost: 0, lo: 0 });
    for (let j = 0; j < eqs.length; j++) cols.push({ cost: 0 });
  }
  const rows: lp.FloatRow[] = [];
  per.forEach(({ ineqs, eqs }, mi) => {
    const o = offs[mi];
    for (let col = 0; col < 2 * k; col++) {
      const cidx: number[] = [];
      const coef: number[] = [];
      ineqs.forEach((row, i) => {
        const v = row.r[col].toNumber();
        if (v !== 0) (cidx.push(o + i), coef.push(v));
      });
      eqs.forEach((row, j) => {
        const v = row.r[col].toNumber();
        if (v !== 0) (cidx.push(o + ineqs.length + j), coef.push(v));
      });
      if (col < k) {
        const succ = net.route[col];
        const wc = new Map<number, number>();
        if (succ !== 0) wc.set(succ - 1, -1);
        wc.set(col, (wc.get(col) ?? 0) + 1);
        for (const [j, v] of wc) if (v !== 0) (cidx.push(j), coef.push(v));
      }
      rows.push({ lo: 0, hi: 0, cols: cidx, coefs: coef }); // A^T y = c(w)
    }
    const cidx: number[] = [];
    const coef: number[] = [];
    ineqs.forEach((row, i) => {
      const v = row.rhs.toNumber();
      if (v !== 0) (cidx.push(o + i), coef.push(v));
    });
    eqs.forEach((row, j) => {
      const v = row.rhs.toNumber();
      if (v !== 0) (cidx.push(o + ineqs.length + j), coef.push(v));
    });
    net.arrivals.forEach((l, i) => {
      const v = l.toNumber();
      if (v !== 0) (cidx.push(i), coef.push(v));
    });
    cidx.push(k);
    coef.push(1);
    rows.push({ hi: 0, cols: cidx, coefs: coef }); // dual value + <lam,w> + eps <= 0
  });
  rows.push({
    lo: 1,
    hi: 1,
    cols: Array.from({ length: k }, (_, i) => i),
    coefs: Array.from({ length: k }, () => 1),
  }); // sum w = 1: V is a weighted lot count
  const sol = lp.floatSolve(cols, rows, 1e-9);
  if (sol.status !== "optimal" || sol.x[k] <= 1e-11) return null;
  return sol.x.slice(0, k).map((x) => lp.rationalize(x, 3600));
}

const VACUOUS_PUSH = Q.of(10n ** 9n);

function exactDual(net: Net, mask: number, w: Q[]) {
  // One exact linear program per sign mode: minimize the dual value
  // over Farkas multipliers. Any dual-feasible point is sound (weak
  // duality); an unbounded ray is a vacuous mode, ridden downward.
  const ineqs = ineqRows(net);
  const eqs = eqRows(net, mask);
  const cObj = objective(net, w);
  const [m1, m2, k2] = [ineqs.length, eqs.length, 2 * net.k];
  const a: Q[][] = [];
  const b: Q[] = [];
  for (let col = 0; col < k2; col++) {
    a.push([
      ...ineqs.map((r) => r.r[col]),
      ...eqs.map((r) => r.r[col]),
      ...eqs.map((r) => r.r[col].neg()),
    ]);
    b.push(cObj[col]);
  }
  const cost = [
    ...ineqs.map((r) => r.rhs),
    ...eqs.map((r) => r.rhs),
    ...eqs.map((r) => r.rhs.neg()),
  ];
  return { cost, a, b, m1, m2 };
}

function resolveDual(
  mask: number,
  m1: number,
  m2: number,
  cost: Q[],
  out: lp.SimplexOutcome,
) {
  if (out.status === "infeasible")
    throw new Error(`mode ${mask}: dual infeasible (impossible)`);
  let x: Q[], val: Q;
  if (out.status === "opt") {
    ({ x } = out);
    val = out.value;
  } else {
    const v0 = cost.reduce((s, ci, i) => s.add(ci.mul(out.x[i])), Q.from(0));
    const rho = cost.reduce((s, ci, i) => s.add(ci.mul(out.ray[i])), Q.from(0));
    const t = v0.add(VACUOUS_PUSH).div(rho.neg());
    x = out.x.map((xi, i) => xi.add(t.mul(out.ray[i])));
    val = v0.add(t.mul(rho));
  }
  return {
    val,
    y: x.slice(0, m1),
    z: Array.from({ length: m2 }, (_, j) => x[m1 + j].sub(x[m1 + m2 + j])),
  };
}

interface Cert {
  model: string;
  net: Net;
  w: Q[];
  eps: Q;
  duals: { mode: number; y: Q[]; z: Q[] }[];
}

function selfReplay(net: Net, w: Q[], eps: Q, duals: Cert["duals"]): void {
  // Re-derive every checker obligation in exact arithmetic before
  // emission: dual signs, the Farkas identity per column, the drift
  // bound per mode. Being wrong past this point would cost soundness;
  // being wrong before it costs a retry.
  const check = (c: boolean, m: string) => {
    if (!c) throw new Error(`self-replay: ${m}`);
  };
  const ineqs = ineqRows(net);
  const c = objective(net, w);
  const wl = net.arrivals.reduce((s, l, i) => s.add(l.mul(w[i])), Q.from(0));
  const target = eps.neg().sub(wl);
  check(w.every((wi) => wi.sign() > 0) && eps.sign() > 0, "w > 0, eps > 0");
  check(duals.length === 63, "mode cover");
  duals.forEach(({ mode, y, z }, idx) => {
    check(mode === idx + 1, "mode order");
    const eqs = eqRows(net, mode);
    check(y.every((yi) => yi.sign() >= 0), `mode ${mode}: dual sign`);
    for (let col = 0; col < 2 * net.k; col++) {
      let acc = Q.from(0);
      y.forEach((yi, i) => (acc = acc.add(yi.mul(ineqs[i].r[col]))));
      z.forEach((zj, j) => (acc = acc.add(zj.mul(eqs[j].r[col]))));
      check(acc.eq(c[col]), `mode ${mode}: Farkas identity, column ${col}`);
    }
    let val = y.reduce((s, yi, i) => s.add(yi.mul(ineqs[i].rhs)), Q.from(0));
    val = z.reduce((s, zj, j) => s.add(zj.mul(eqs[j].rhs)), val);
    check(val.cmp(target) <= 0, `mode ${mode}: drift bound`);
  });
}

function produce(policy: string, variant: string, lotsPerWeek: number): Cert | null {
  const net = makeNet(policy, variant, lotsPerWeek);
  const w = proposeW(net);
  if (w === null) return null;
  const problems = Array.from({ length: 63 }, (_, i) => exactDual(net, i + 1, w));
  const outcomes = lp.simplexMinBatch(
    problems.map((p) => ({ c: p.cost, a: p.a, b: p.b })),
  );
  const duals: Cert["duals"] = [];
  let worst: Q | null = null;
  outcomes.forEach((out, i) => {
    const p = problems[i];
    const { val, y, z } = resolveDual(i + 1, p.m1, p.m2, p.cost, out);
    duals.push({ mode: i + 1, y, z });
    if (worst === null || val.cmp(worst) > 0) worst = val;
  });
  const wl = net.arrivals.reduce((s, l, i) => s.add(l.mul(w[i])), Q.from(0));
  const eps = worst!.neg().sub(wl);
  if (eps.sign() <= 0) return null; // no linear certificate at this load
  selfReplay(net, w, eps, duals);
  const model =
    `Kempf-1994 Intel Mini-Fab deterministic-core fluid skeleton; ` +
    `variant=${variant}; policy=${policy}; release=${lotsPerWeek}/wk`;
  return { model, net, w, eps, duals };
}

// ---------------------------------------------------- the workspace
// The obligation set, handed to the session workspace: one obligation
// per grid point, one move — run the producer, emit through the canon
// encoder, and let the checker adjudicate. No certificate is not a
// refutation: the move's honest outcome at an infeasible load is
// inconclusive, with the geometry as evidence.

mkdirSync("out", { recursive: true });

const fluidStable: StatementKind = {
  kind: "minifab.fluidStable",
  validate: (s) => {
    for (const key of ["policy", "variant", "lotsPerWeek"])
      if (s[key] === undefined) throw new Error(`missing ${key}`);
    return s;
  },
  describe: (s) =>
    `fluid skeleton drains under ${s.policy} (${s.variant}) at ${s.lotsPerWeek} lots/week`,
  moves: () => [
    {
      name: "farkas",
      doc: "propose weights (float LP), certify duals (exact LP), emit, check",
      cost: "moderate",
      canDischarge: true,
      canRefute: false,
      canSpawn: false,
      params: [],
    },
  ],
  exec: (s): { outcome: "discharged" | "inconclusive"; witness?: Json; evidence?: Json; note?: string } => {
    const [policy, variant, lots] = [String(s.policy), String(s.variant), Number(s.lotsPerWeek)];
    const cert = produce(policy, variant, lots);
    if (cert === null)
      return {
        outcome: "inconclusive",
        evidence: { reason: "no linear Lyapunov certificate at this load" },
        note: "the load is at or over the variant's capacity; absence of a certificate is not a refutation",
      };
    const doc: JsFluidCert = {
      model: cert.model,
      net: {
        k: cert.net.k,
        route: cert.net.route,
        arrivals: cert.net.arrivals.map(String),
        stations: cert.net.stations,
        caps: cert.net.caps.map(String),
        muLo: cert.net.muLo.map(String),
        muHi: cert.net.muHi.map(String),
        prio: cert.net.prio,
      },
      w: cert.w.map(String),
      eps: cert.eps.toString(),
      duals: cert.duals.map((d) => ({ mode: d.mode, y: d.y.map(String), z: d.z.map(String) })),
    };
    const bytes = fluid.encodeFluidV0(doc);
    const stem = `${policy.toLowerCase()}_${variant === "core" ? "core" : "setupadv"}_${lots}wk`;
    writeFileSync(`out/${stem}.cbor`, bytes);
    const verdict = fluid.verifyBytes(bytes);
    if (!verdict.ok)
      return {
        outcome: "inconclusive",
        evidence: { checker: verdictLine(verdict) },
        note: "checker refused an emitted certificate — producer defect",
      };
    return {
      outcome: "discharged",
      witness: {
        file: `out/${stem}.cbor`,
        sha256: createHash("sha256").update(bytes).digest("hex").slice(0, 16),
        eps: cert.eps.toString(),
        w: cert.w.map(String),
        checker: verdictLine(verdict),
      },
    };
  },
};

// ---------------------------------------------------- the release grid
// The ladder of "The certificates", probes included.
const GRID: [string, string, number][] = [
  ["LBFS", "core", 84],
  ["LBFS", "core", 90],
  ["LBFS", "core", 94],
  ["LBFS", "core", 95],
  ["LBFS", "core", 96], // probe: fluid capacity
  ["FBFS", "core", 84],
  ["FBFS", "core", 95],
  ["LBFS", "setup-adversarial", 72],
  ["LBFS", "setup-adversarial", 76],
  ["LBFS", "setup-adversarial", 78],
  ["LBFS", "setup-adversarial", 79], // probe: over the adversarial ceiling
  ["FBFS", "setup-adversarial", 78],
];

const ws = new Workspace([fluidStable]);
for (const [policy, variant, lotsPerWeek] of GRID) {
  const ob = ws.pose({ kind: "minifab.fluidStable", policy, variant, lotsPerWeek });
  const r = ws.apply(ob.id, "farkas");
  const w = r.attempt.witness as { eps?: string; checker?: string } | undefined;
  console.log(
    `${ob.id} ${ws.describe(ob.id)}\n  -> ${r.attempt.outcome}` +
      (w ? ` eps=${w.eps} (${w.checker})` : ` (${r.attempt.note})`),
  );
}

const open = ws.list().filter((o) => o.status === "open");
console.log(
  `\n${ws.list().length} obligations: ` +
    `${ws.list().filter((o) => o.status === "discharged").length} discharged, ` +
    `${open.length} open (${open.map((o) => `${o.statement.lotsPerWeek}wk`).join(", ")})`,
);
const flagship = ws.get("ob1").witness as { w: string[] };
console.log(`flagship V weights: (${flagship.w.join(", ")})`);
