"""ck_manifest — STANDALONE checker for the `circuit-manifest-recurrence`
v0 species (census F2). Zero imports from the producer: own CBOR
decode, own sparse-poly arithmetic, own tensor-product Bernstein transform,
exact Q throughout (stdlib Fraction + cbor2 only).

What an ACCEPT certifies (given the manifest = SV-semantics producer seam,
see species.py): the hypotheses of the machine-checked demonic recurrence
lemma `Qtsl.StreettDemonic.frequently_target_of_ranking`
(`../../lean/qtsl-aux/QtslAux/StreettDemonic.lean`)
hold for the circuit's
step system with target gamma = the union of gamma-marked cells; hence every
run, from every initial state in the box, under every input sequence, takes
gamma-steps infinitely often — the reduced form of the instance's LTL spec.

Check ledger (every check recomputed from the manifest, nothing trusted):

  C0  schema/version; eps0 > 0 exact                     [strictness row]
  C1  arity + bounds well-formedness (wires, cells, pieces, polys)
  C2  cells partition the full (state x input) box       [no unmodeled step]
      (pairwise box-disjointness + exact volume count)
  C3  ranking pieces partition the state box             [R total, single-valued]
  C4  per non-gamma cell: unique ranking piece contains the cell's state
      projection; image_box inside the state box; per state wire the
      Bernstein range of the step polynomial over the cell is inside
      image_box; unique piece contains image_box          [image soundness]
  C5  ranking row per non-gamma cell:
      all Bernstein coefficients of  R_img(step(x,w)) - R_cell(x) + eps0
      over the cell box are <= 0                          [lemma's hR1]
  C6  nonneg row per non-gamma cell:
      all Bernstein coefficients of R_img over image_box are >= 0
                                                          [lemma's hR2]

Bernstein soundness note: coefficients enclose the polynomial on the REAL
box, which contains the integer points — certifying over the relaxation is
sound for the integer-state system (route doc F3), and for the unit-descent
certificate shapes here it is also exact.

Usage: python3 ck_manifest.py fixtures/delay_1.cbor [...]
Exit 0 iff every argument ACCEPTs.
"""

import sys
import time
from fractions import Fraction
from math import comb

import cbor2

F = Fraction
SCHEMA = "circuit-manifest-recurrence"
VERSION = 0


class Reject(Exception):
    pass


# ---------------------------------------------------------------- decode


def dec_frac(x):
    if (not isinstance(x, list)) or len(x) != 2:
        raise Reject(f"C1: bad fraction encoding {x!r}")
    return F(int(x[0]), int(x[1]))


def dec_poly(enc, arity):
    p = {}
    for entry in enc:
        if len(entry) != 2:
            raise Reject("C1: bad poly entry")
        expts, c = entry
        if len(expts) != arity or any((not isinstance(e, int)) or e < 0
                                      for e in expts):
            raise Reject(f"C1: bad exponent tuple {expts!r} (arity {arity})")
        k = tuple(expts)
        if k in p:
            raise Reject("C1: duplicate monomial")
        p[k] = dec_frac(c)
    return p


# ---------------------------------------------------------------- poly ops


def peval(p, xs):
    tot = F(0)
    for k, c in p.items():
        t = c
        for e, x in zip(k, xs):
            t *= F(x) ** e
        tot += t
    return tot


def padd(p, q):
    out = dict(p)
    for k, c in q.items():
        out[k] = out.get(k, F(0)) + c
        if out[k] == 0:
            del out[k]
    return out


def pneg(p):
    return {k: -c for k, c in p.items()}


def pmul(p, q):
    out = {}
    for ka, ca in p.items():
        for kb, cb in q.items():
            k = tuple(a + b for a, b in zip(ka, kb))
            out[k] = out.get(k, F(0)) + ca * cb
            if out[k] == 0:
                del out[k]
    return out


def ppow(p, e, arity):
    out = {(0,) * arity: F(1)}
    for _ in range(e):
        out = pmul(out, p)
    return out


def pconst(c, arity):
    c = F(c)
    return {} if c == 0 else {(0,) * arity: c}


def compose(p, subs, arity_out):
    """p over n vars; subs[j] a poly over arity_out vars; result = p(subs)."""
    out = {}
    for k, c in p.items():
        term = pconst(c, arity_out)
        for j, e in enumerate(k):
            if e:
                term = pmul(term, ppow(subs[j], e, arity_out))
        out = padd(out, term)
    return out


def embed(p, arity_out):
    """poly over first n vars -> same poly over arity_out >= n vars."""
    out = {}
    for k, c in p.items():
        out[k + (0,) * (arity_out - len(k))] = c
    return out


# ------------------------------------------------------- tensor Bernstein


def bernstein_coeffs(p, box):
    """All tensor-product Bernstein coefficients of p on box
    (list of [lo, hi], real-box reading). Returns a list of Fractions.
    Enclosure: min <= p(x) <= max for every x in the box."""
    d = len(box)
    # affine substitution x_j = lo_j + (hi_j - lo_j) t_j, expand in t
    q = {}
    for k, c in p.items():
        # product over j of (lo_j + w_j t_j)^{e_j}
        acc = {(0,) * d: c}
        for j, e in enumerate(k):
            lo, hi = F(box[j][0]), F(box[j][1])
            w = hi - lo
            if e == 0:
                continue
            # (lo + w t_j)^e = sum_m C(e,m) lo^(e-m) w^m t_j^m
            factor = {}
            for m in range(e + 1):
                coef = comb(e, m) * lo ** (e - m) * w ** m
                if coef != 0:
                    key = [0] * d
                    key[j] = m
                    factor[tuple(key)] = coef
            acc = pmul(acc, factor)
        q = padd(q, acc)
    if not q:
        return [F(0)]
    degs = [max(k[j] for k in q) for j in range(d)]
    # b_u = sum_{m <= u} q_m prod_j C(u_j, m_j) / C(deg_j, m_j)
    coeffs = []
    grid = [[]]
    for j in range(d):
        grid = [g + [u] for g in grid for u in range(degs[j] + 1)]
    for u in grid:
        b = F(0)
        for m, qc in q.items():
            if all(m[j] <= u[j] for j in range(d)):
                t = qc
                for j in range(d):
                    t *= F(comb(u[j], m[j]), comb(degs[j], m[j]))
                b += t
        coeffs.append(b)
    return coeffs


# ---------------------------------------------------------------- box ops


def box_wf(box, ranges, tag):
    if len(box) != len(ranges):
        raise Reject(f"C1: {tag}: box arity {len(box)} != {len(ranges)}")
    for (lo, hi), (rlo, rhi) in zip(box, ranges):
        if not (isinstance(lo, int) and isinstance(hi, int)):
            raise Reject(f"C1: {tag}: non-integer bound")
        if lo > hi:
            raise Reject(f"C1: {tag}: empty interval [{lo},{hi}]")
        if lo < rlo or hi > rhi:
            raise Reject(f"C1: {tag}: [{lo},{hi}] outside wire range "
                         f"[{rlo},{rhi}]")


def volume(box):
    v = 1
    for lo, hi in box:
        v *= hi - lo + 1
    return v


def disjoint(a, b):
    return any(ahi < blo or bhi < alo
               for (alo, ahi), (blo, bhi) in zip(a, b))


def contains(outer, inner):
    return all(olo <= ilo and ihi <= ohi
               for (olo, ohi), (ilo, ihi) in zip(outer, inner))


def partition_check(boxes, full, cid):
    for i in range(len(boxes)):
        for j in range(i + 1, len(boxes)):
            if not disjoint(boxes[i], boxes[j]):
                raise Reject(f"{cid}: boxes {i} and {j} overlap")
    tot = sum(volume(b) for b in boxes)
    if tot != volume(full):
        raise Reject(f"{cid}: volumes {tot} != full {volume(full)} "
                     "(cover gap or leak)")


# ---------------------------------------------------------------- checker


def check(m):
    t0 = time.perf_counter()
    # C0
    if m.get("schema") != SCHEMA or m.get("v") != VERSION:
        raise Reject("C0: schema/version mismatch")
    eps0 = dec_frac(m["eps0"])
    if not eps0 > 0:
        raise Reject(f"C0: eps0 = {eps0} not > 0")
    # C1 wires
    sw, iw = m["state_wires"], m["input_wires"]
    for n, lo, hi in sw + iw:
        if lo > hi:
            raise Reject(f"C1: wire {n} empty range")
    ns, ni = len(sw), len(iw)
    sranges = [(lo, hi) for _, lo, hi in sw]
    iranges = [(lo, hi) for _, lo, hi in iw]
    full = [list(r) for r in sranges + iranges]
    sbox = [list(r) for r in sranges]
    # C1 cells + pieces
    cells = m["cells"]
    pieces = m["pieces"]
    for idx, c in enumerate(cells):
        box_wf(c["box"], sranges + iranges, f"cell {idx}")
        if not c["gamma"]:
            if "step" not in c or "image_box" not in c:
                raise Reject(f"C1: non-gamma cell {idx} lacks step/image_box")
        if "step" in c:
            if len(c["step"]) != ns:
                raise Reject(f"C1: cell {idx} step arity")
            c["_step"] = [dec_poly(s, ns + ni) for s in c["step"]]
        if "image_box" in c:
            box_wf(c["image_box"], sranges, f"cell {idx} image")
    for idx, p in enumerate(pieces):
        box_wf(p["box"], sranges, f"piece {idx}")
        p["_poly"] = dec_poly(p["poly"], ns)
    # C2 / C3
    partition_check([c["box"] for c in cells], full, "C2")
    partition_check([p["box"] for p in pieces], sbox, "C3")

    nrows = 0
    for idx, c in enumerate(cells):
        if c["gamma"]:
            continue
        cbox = c["box"]
        cproj = cbox[:ns]
        img = c["image_box"]
        # C4a unique piece over the cell's state projection
        cps = [p for p in pieces if contains(p["box"], cproj)]
        if len(cps) != 1:
            raise Reject(f"C4: cell {idx} state-projection in "
                         f"{len(cps)} pieces (want 1)")
        # C4b image inside state box
        if not contains(sbox, img):
            raise Reject(f"C4: cell {idx} image outside state box")
        # C4c Bernstein range of each step poly inside the image interval
        for j in range(ns):
            bc = bernstein_coeffs(c["_step"][j], cbox)
            lo, hi = min(bc), max(bc)
            if lo < img[j][0] or hi > img[j][1]:
                raise Reject(f"C4: cell {idx} wire {sw[j][0]}: step range "
                             f"[{lo},{hi}] not in image [{img[j][0]},"
                             f"{img[j][1]}]")
        # C4d unique piece over the image
        ips = [p for p in pieces if contains(p["box"], img)]
        if len(ips) != 1:
            raise Reject(f"C4: cell {idx} image in {len(ips)} pieces")
        # C5 ranking row: R_img(step(x,w)) - R_cell(x) + eps0 <= 0 on cell
        row = padd(padd(compose(ips[0]["_poly"], c["_step"], ns + ni),
                        pneg(embed(cps[0]["_poly"], ns + ni))),
                   pconst(eps0, ns + ni))
        bc = bernstein_coeffs(row, cbox)
        if max(bc) > 0:
            raise Reject(f"C5: cell {idx} ranking row max Bernstein "
                         f"coefficient {max(bc)} > 0")
        nrows += 1
        # C6 nonneg row: R_img >= 0 on image box
        bc = bernstein_coeffs(ips[0]["_poly"], img)
        if min(bc) < 0:
            raise Reject(f"C6: cell {idx} nonneg row min Bernstein "
                         f"coefficient {min(bc)} < 0")
        nrows += 1
    ms = (time.perf_counter() - t0) * 1000.0
    return {"instance": m.get("instance"), "cells": len(cells),
            "gamma_cells": sum(1 for c in cells if c["gamma"]),
            "pieces": len(pieces), "rows": nrows, "check_ms": ms}


def main(paths):
    ok = True
    for path in paths:
        with open(path, "rb") as fh:
            m = cbor2.load(fh)
        try:
            r = check(m)
            print(f"ACCEPT {r['instance']}: {r['cells']} cells "
                  f"({r['gamma_cells']} gamma), {r['pieces']} pieces, "
                  f"{r['rows']} rows, {r['check_ms']:.2f} ms")
        except Reject as e:
            print(f"REJECT {path}: {e}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
