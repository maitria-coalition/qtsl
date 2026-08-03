#!/usr/bin/env python3
"""Frozen cross-implementation corpus for the Bernstein-cone float
lane (`allForwardDiffBernIntvEnclosuresSatisfyP`).

Independent python arm: the Lean `FloatFmt` rounding maps
(`Core/Dyadic.lean` — gridExp/rdnRaw/rdn/rup transcribed from the
Lean text over `fractions.Fraction`, NOT from the Rust), the
∞-routed enclosure endpoints (`roundE` story), interval polynomial
arithmetic with outward rounding at every binary operation, the
forward-difference pipeline implemented VERBATIM (substInto →
homogenize → the j/k/β loops with the bAt·multinomial dance → the
bernCoeffRows division — no S=∅ mathematical shortcuts, so the
rounding sites line up with any faithful implementation), the
verdict trichotomy with its own upward-closed-conic recognizer.

Corpus scope (stated honestly): 1-D line geometries, S = ∅, affine
single-wire polynomials, GE/LE atom conjunctions — the float lane's
NEW content is the rounding substrate and the trichotomy; the mask
combinatorics are pinned by the exact lane's corpus (the pipeline
code shape is shared) and by the battery's hand cases.

Verdicts are DERIVED here, never asserted.
"""

import itertools
import json
import os
from fractions import Fraction

# ---------------------------------------------------------------- formats

FMTS = {
    "F16": (11, -24, 5),
    "BF16": (8, -133, 120),
    "F32": (24, -149, 104),
    "F64": (53, -1074, 971),
}


def max_fin(fmt):
    prec, _emin, emax = fmt
    return (2**prec - 1) * Fraction(2) ** emax


def nat_log2(n):
    # Lean Nat.log2: 0 at 0, else floor(log2 n).
    return 0 if n <= 0 else n.bit_length() - 1


def clog2(n):
    # Lean Prim.clog2 recursion.
    c = 0
    while n >= 2:
        n = (n + 1) // 2
        c += 1
    return c


def int_log2(q):
    # Lean Prim.intLog2 (callers pass |q|).
    if q >= 1:
        return nat_log2(int(q))  # floor then Nat.log2
    if q <= 0:
        return 0
    inv = 1 / q
    c = -(-inv.numerator // inv.denominator)  # ceil
    return -clog2(int(c))


def grid_exp(fmt, q):
    prec, emin, _emax = fmt
    return max(emin, int_log2(abs(q)) + 1 - prec)


def rdn(fmt, q):
    mf = max_fin(fmt)
    if q >= mf:
        return mf
    if q < -mf:
        return -mf
    g = grid_exp(fmt, q)
    scaled = q / Fraction(2) ** g
    return Fraction(scaled.numerator // scaled.denominator) * Fraction(2) ** g


def rup(fmt, q):
    return -rdn(fmt, -q)


NEG_INF = "neginf"
POS_INF = "posinf"


def round_down(fmt, q):
    return NEG_INF if q < -max_fin(fmt) else rdn(fmt, q)


def round_up(fmt, q):
    return POS_INF if q > max_fin(fmt) else rup(fmt, q)


def is_fin(e):
    return e is not NEG_INF and e is not POS_INF


# ---------------------------------------------------------------- intervals


def iv_from_q(fmt, q):
    return (round_down(fmt, q), round_up(fmt, q))


IV_ZERO = (Fraction(0), Fraction(0))
IV_ONE = (Fraction(1), Fraction(1))


def iv_is_exact_zero(iv):
    return is_fin(iv[0]) and is_fin(iv[1]) and iv[0] == 0 and iv[1] == 0


def iv_add(fmt, a, b):
    lo = (
        round_down(fmt, a[0] + b[0])
        if is_fin(a[0]) and is_fin(b[0])
        else NEG_INF
    )
    hi = (
        round_up(fmt, a[1] + b[1])
        if is_fin(a[1]) and is_fin(b[1])
        else POS_INF
    )
    return (lo, hi)


def ext_mul(a, b):
    # Containment semantics: 0·∞ = 0.
    if is_fin(a) and is_fin(b):
        return a * b
    if is_fin(a) or is_fin(b):
        f, inf = (a, b) if is_fin(a) else (b, a)
        if f == 0:
            return Fraction(0)
        if f > 0:
            return inf
        return NEG_INF if inf is POS_INF else POS_INF
    if a == b:
        return POS_INF
    return NEG_INF


def end_key(e):
    # Ordering key: NegInf < Fin < PosInf.
    if e is NEG_INF:
        return (0, 0)
    if e is POS_INF:
        return (2, 0)
    return (1, e)


def iv_mul(fmt, a, b):
    combos = [ext_mul(x, y) for x in (a[0], a[1]) for y in (b[0], b[1])]
    lo = min(combos, key=end_key)
    hi = max(combos, key=end_key)
    lo = round_down(fmt, lo) if is_fin(lo) else lo
    hi = round_up(fmt, hi) if is_fin(hi) else hi
    return (lo, hi)


def iv_scale_q(fmt, a, c):
    return iv_mul(fmt, a, (c, c))


def iv_div_nat(fmt, a, n):
    return iv_scale_q(fmt, a, Fraction(1, n))


# ------------------------------------------------------ interval polynomials
# Monos are tuples of (var, exp) pairs, sorted — matching the Rust
# BTreeMap iteration order.


def poly_add_term(fmt, p, mono, iv):
    if iv_is_exact_zero(iv):
        return
    if mono in p:
        s = iv_add(fmt, p[mono], iv)
        if iv_is_exact_zero(s):
            del p[mono]
        else:
            p[mono] = s
    else:
        p[mono] = iv


def poly_add(fmt, a, b):
    out = dict(a)
    for m, c in sorted(b.items()):
        poly_add_term(fmt, out, m, c)
    return out


def mono_mul(a, b):
    d = {}
    for v, e in a:
        d[v] = d.get(v, 0) + e
    for v, e in b:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def poly_mul(fmt, a, b):
    out = {}
    for ma, ca in sorted(a.items()):
        for mb, cb in sorted(b.items()):
            poly_add_term(fmt, out, mono_mul(ma, mb), iv_mul(fmt, ca, cb))
    return out


def poly_scale_q(fmt, a, c):
    if c == 0:
        return {}
    out = {}
    for m, iv in sorted(a.items()):
        poly_add_term(fmt, out, m, iv_scale_q(fmt, iv, c))
    return out


def poly_var(v):
    return {((v, 1),): IV_ONE}


def poly_pow(fmt, p, e):
    acc = {(): IV_ONE}
    for _ in range(e):
        acc = poly_mul(fmt, acc, p)
    return acc


def sum_vars(m):
    return {((i, 1),): IV_ONE for i in range(m)}


def subst_into(fmt, p_exact, sigma):
    # p_exact: dict mono -> Fraction (the term translation is exact).
    acc = {}
    for mono, c in sorted(p_exact.items()):
        term = {(): IV_ONE}
        for v, e in mono:
            term = poly_mul(fmt, term, poly_pow(fmt, sigma[v], e))
        acc = poly_add(fmt, acc, poly_scale_q(fmt, term, c))
    return acc


class Indeterminate(Exception):
    pass


def homogenize(fmt, m, d, p):
    sv = sum_vars(m)
    acc = {}
    for mono, c in sorted(p.items()):
        e = sum(x for _, x in mono)
        if e > d:
            lo, hi = c
            excludes = (is_fin(lo) and lo > 0) or (is_fin(hi) and hi < 0)
            if excludes:
                return None  # certain degree lie → decided false
            raise Indeterminate("degree-lie straddle")
        mp = {mono: c}
        acc = poly_add(fmt, acc, poly_mul(fmt, mp, poly_pow(fmt, sv, d - e)))
    return acc


def multinomial(v):
    from math import comb

    out = 1
    rest = list(v)
    while rest:
        a = rest.pop(0)
        out *= comb(a + sum(rest), a)
    return out


def compositions(parts, total):
    if parts == 0:
        return [[]] if total == 0 else []
    out = []
    for a in range(total + 1):
        for rest in compositions(parts - 1, total - a):
            out.append([a] + rest)
    return out


def compositions_up_to(parts, bound):
    out = []
    for total in range(bound + 1):
        out.extend(compositions(parts, total))
    return out


def sub_compositions(j):
    if not j:
        return [[]]
    out = []
    tails = sub_compositions(j[1:])
    for k in range(j[0] + 1):
        for t in tails:
            out.append([k] + t)
    return out


def assemble_vec(smask, k, beta):
    out, ki, bi = [], 0, 0
    for s in smask:
        if s:
            out.append(k[ki] if ki < len(k) else 0)
            ki += 1 if ki < len(k) else 0
        else:
            out.append(beta[bi] if bi < len(beta) else 0)
            bi += 1 if bi < len(beta) else 0
    return out


def vec_to_mono(v):
    return tuple((i, e) for i, e in enumerate(v) if e != 0)


def fd_bernstein_grid(fmt, coords, smask, d, p_exact):
    m = len(coords)
    m_s = sum(smask)
    m_b = m - m_s
    if m_b == 0:
        return None
    amb = len(coords[0])
    sigma = []
    for j in range(amb):
        s = {}
        for i, vc in enumerate(coords):
            s = poly_add(fmt, s, poly_scale_q(fmt, poly_var(i), vc[j]))
        sigma.append(s)
    p_lam = subst_into(fmt, p_exact, sigma)
    hp = homogenize(fmt, m, d, p_lam)
    if hp is None:
        return None

    def b_at(k, beta):
        alpha = assemble_vec(smask, k, beta)
        mono = vec_to_mono(alpha)
        c = hp.get(mono, IV_ZERO)
        return iv_div_nat(fmt, c, multinomial(alpha))

    from math import comb

    out = []
    for j in compositions_up_to(m_s, d):
        pj = {}
        for k in sub_compositions(j):
            k_sum = sum(k)
            neg = k_sum % 2 == 1
            binom = 1
            for ji, ki in zip(j, k):
                binom *= comb(ji, ki)
            qk = {}
            for beta in compositions(m_b, d - k_sum):
                mono = vec_to_mono(beta)
                coeff = iv_scale_q(fmt, b_at(k, beta), Fraction(multinomial(beta)))
                if not iv_is_exact_zero(coeff):
                    qk = poly_add(fmt, qk, {mono: coeff})
            hk = poly_mul(fmt, qk, poly_pow(fmt, sum_vars(m_b), k_sum))
            scale = Fraction(-binom if neg else binom)
            pj = poly_add(fmt, pj, poly_scale_q(fmt, hk, scale))
        for alpha in compositions(m_b, d):
            mono = vec_to_mono(alpha)
            out.append(iv_div_nat(fmt, pj.get(mono, IV_ZERO), multinomial(alpha)))
    return out


# ---------------------------------------------------------------- predicates


def pred_eval(atoms, v):
    # v is a Fraction; atoms are (op, c).
    for op, c in atoms:
        if op == "GE" and not v >= c:
            return False
        if op == "LE" and not v <= c:
            return False
    return True


def pred_up_closed_conic(atoms):
    conic = True
    up = True
    for op, c in atoms:
        if op == "GE":
            conic &= c == 0
        elif op == "LE":
            conic &= c == 0
            up = False
        else:
            return False
    return conic and up


def verdict(fmt, verts, c0, c1, degree, atoms):
    # Structural arms: 2 verts on a 1-D line, full-dim, affine
    # idx-free single-wire poly — all pass by construction here
    # (nonconstant requires amb 1, satisfied).
    coords = [[Fraction(*v)] for v in verts]
    smask = [False, False]
    p_exact = {}
    if Fraction(*c0) != 0:
        p_exact[()] = Fraction(*c0)
    if Fraction(*c1) != 0:
        p_exact[((0, 1),)] = Fraction(*c1)
    try:
        grid = fd_bernstein_grid(fmt, coords, smask, degree, p_exact)
    except Indeterminate:
        return "refused"
    if grid is None:
        return "false"
    all_lo = True
    for lo, _hi in grid:
        if not (is_fin(lo) and pred_eval(atoms, lo)):
            all_lo = False
    if all_lo:
        return "holds"
    if pred_up_closed_conic(atoms):
        for _lo, hi in grid:
            if is_fin(hi) and not pred_eval(atoms, hi):
                return "false"
    return "refused"


# ---------------------------------------------------------------- generation


def main():
    vert_pool = [
        ((0, 1), (1, 1)),
        ((1, 1), (2, 1)),
        ((-1, 2), (1, 2)),
        ((1, 3), (1, 1)),
        ((1, 3), (2, 3)),
        ((-1, 3), (1, 7)),
        ((1, 10), (7, 10)),
    ]
    poly_pool = [
        ((1, 2), (2, 1)),
        ((0, 1), (1, 1)),
        ((-1, 1), (-1, 1)),
        ((1, 10), (0, 1)),
        ((-1, 1), (3, 1)),
        ((1, 3), (-1, 3)),
        ((0, 1), (-2, 7)),
        ((1, 1000000007), (0, 1)),
    ]
    pred_pool = [
        [("GE", (0, 1))],
        [("LE", (0, 1))],
        [("GE", (1, 1))],
        [("GE", (0, 1)), ("GE", (0, 1))],
        [("GE", (0, 1)), ("LE", (5, 1))],
        [("GE", (1, 3))],
    ]
    dtypes = ["F64", "F32", "F16", "BF16"]
    degrees = [1, 2]

    cases = []
    n = 0
    for verts, poly, atoms, dt, deg in itertools.product(
        vert_pool, poly_pool, pred_pool, dtypes, degrees
    ):
        n += 1
        # Deterministic thinning to corpus scale (keep every third).
        if n % 3 != 0:
            continue
        fmt = FMTS[dt]
        vd = verdict(
            fmt,
            verts,
            poly[0],
            poly[1],
            deg,
            [(op, Fraction(*c)) for op, c in atoms],
        )
        cases.append(
            {
                "verts": [list(v) for v in verts],
                "poly": {"c0": list(poly[0]), "c1": list(poly[1])},
                "degree": deg,
                "pred": [{"op": op, "c": list(c)} for op, c in atoms],
                "dtype": dt,
                "verdict": vd,
            }
        )

    counts = {}
    for c in cases:
        counts[c["verdict"]] = counts.get(c["verdict"], 0) + 1
    assert len(cases) >= 200, len(cases)
    assert all(k in counts for k in ("holds", "false", "refused")), counts

    out = os.path.join(os.path.dirname(__file__), "bernintv_pyref_corpus.json")
    with open(out, "w") as f:
        json.dump({"generator": "bernintv_pyref_gen.py", "counts": counts, "cases": cases}, f, indent=1)
    print(f"{len(cases)} cases → {out}; verdicts {counts}")


if __name__ == "__main__":
    main()
