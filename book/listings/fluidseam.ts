// fluidseam.ts — emission and verdict seam for the fluid-drift
// certificate species: the checker crate linked in-process through a
// node addon, so the bytes written and the bytes judged ride one
// canonical encoder. The addon is a thin `fluid-node` napi binding
// around the same checker crate that the reproduction spine's
// standalone fluidcheck binary imports; the binding crate travels
// with the producer migration that the Experiments chapter's
// reproduction section records. Resolution: the `FLUID_NODE_ADDON`
// environment variable, else `native/fluid.node` beside this file.

import { createRequire } from "node:module";

export interface JsNetwork {
  k: number;
  route: number[];
  arrivals: string[];
  stations: number[][];
  caps: string[];
  muLo: string[];
  muHi: string[];
  prio: number[][];
}
export interface JsModeDual {
  mode: number;
  y: string[];
  z: string[];
}
export interface JsFluidCert {
  model: string;
  net: JsNetwork;
  w: string[];
  eps: string;
  duals: JsModeDual[];
}
export interface JsVerdict {
  ok: boolean;
  locus?: string | null;
  detail?: string | null;
  modes?: number | null;
  obligations?: number | null;
  eps?: string | null;
}
interface FluidModule {
  encodeFluidV0(cert: JsFluidCert): Buffer;
  verifyBytes(bytes: Buffer): JsVerdict;
}

const require = createRequire(import.meta.url);
export const fluid: FluidModule = require(
  process.env.FLUID_NODE_ADDON ??
    new URL("./native/fluid.node", import.meta.url).pathname,
);

/** Verdict, in the standalone checker binary's one-line format. */
export function verdictLine(v: JsVerdict): string {
  return v.ok
    ? `ACCEPT modes=${v.modes} obligations=${v.obligations} eps=${v.eps}`
    : `REFUSE locus=${v.locus} detail=${v.detail}`;
}
