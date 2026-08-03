#!/usr/bin/env python3
"""Frozen cross-implementation corpus for the Bernstein-cone family.

An INDEPENDENT python transcription of the Lean checkers
(`bernConeCoeffCheck` and `coverCheck`, `lean/qtsl/Qtsl/Core/
Catalogue.lean`; the arithmetic pipeline `fdBernstein` and its
combinatorial substrate, `lean/qtsl/Qtsl/Core/QArith.lean`) over
`fractions.Fraction` and dict-of-monomial polynomials — sharing no
code, no representation, and no language with the Rust evaluators.
Verdicts are DERIVED by running this transcription, never asserted.

Regenerate with:  python3 berncone_pyref_gen.py > berncone_pyref_corpus.json
"""

import itertools
import json
import random
from fractions import Fraction as F
from math import comb

# ---------------------------------------------------------------------
# Sparse polynomials: dict{ mono(tuple[(var, exp)]) : Fraction }
# ---------------------------------------------------------------------


def canon(p):
    return {m: c for m, c in p.items() if c != 0}


def p_const(c):
    return canon({(): F(c)})


def p_var(v):
    return {((v, 1),): F(1)}


def p_add(p, q):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, F(0)) + c
    return canon(out)


def p_neg(p):
    return {m: -c for m, c in p.items()}


def p_sub(p, q):
    return p_add(p, p_neg(q))


def p_scale(a, p):
    if a == 0:
        return {}
    return {m: a * c for m, c in p.items()}


def mono_mul(a, b):
    d = {}
    for v, e in a + b:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def p_mul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = mono_mul(m1, m2)
            out[m] = out.get(m, F(0)) + c1 * c2
    return canon(out)


def p_pow(p, e):
    acc = p_const(1)
    for _ in range(e):
        acc = p_mul(acc, p)
    return acc


def p_vars(p):
    return sorted({v for m in p for v, _ in m})


def mono_deg(m):
    return sum(e for _, e in m)


def coeff_of(p, m):
    return p.get(m, F(0))


# ---------------------------------------------------------------------
# The combinatorial substrate (Lean Core/QArith.lean)
# ---------------------------------------------------------------------


def multinomial(v):
    if not v:
        return 1
    a, rest = v[0], v[1:]
    return comb(a + sum(rest), a) * multinomial(rest)


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
    for t in range(bound + 1):
        out.extend(compositions(parts, t))
    return out


def sub_compositions(j):
    if not j:
        return [[]]
    a, rest = j[0], j[1:]
    return [[k] + t for k in range(a + 1) for t in sub_compositions(rest)]


def assemble_vec(smask, k, beta):
    out, ki, bi = [], 0, 0
    for s in smask:
        if s:
            if ki < len(k):
                out.append(k[ki])
                ki += 1
            else:
                out.append(0)
        else:
            if bi < len(beta):
                out.append(beta[bi])
                bi += 1
            else:
                out.append(0)
    return out


def vec_to_mono(v):
    return tuple((i, e) for i, e in enumerate(v) if e != 0)


def sum_vars(m):
    p = {}
    for i in range(m):
        p = p_add(p, p_var(i))
    return p


def subst_into(p, sigma):
    acc = {}
    for m, c in p.items():
        term = p_const(1)
        for v, e in m:
            term = p_mul(term, p_pow(sigma[v], e))
        acc = p_add(acc, p_scale(c, term))
    return acc


def homogenize(m, d, p):
    acc = {}
    sv = sum_vars(m)
    for mono, c in p.items():
        e = mono_deg(mono)
        if e > d:
            return None
        acc = p_add(acc, p_mul({mono: c}, p_pow(sv, d - e)))
    return acc


def bern_coeff_rows(m, d, hp):
    return [
        (alpha, coeff_of(hp, vec_to_mono(alpha)) / multinomial(alpha))
        for alpha in compositions(m, d)
    ]


def fd_bernstein_grid(coords, smask, d, p):
    """The grid coefficients of the Lean `fdBernstein` (gridAll sweeps
    only the grid), or None on the construction's none branches."""
    m = len(coords)
    m_s = sum(1 for s in smask if s)
    m_b = m - m_s
    if m_b == 0:
        return None
    amb = len(coords[0]) if coords else 0
    sigma = [
        p_add({}, canon({((i, 1),): coords[i][j] for i in range(m)}))
        for j in range(amb)
    ]
    p_lam = subst_into(p, sigma)
    hp = homogenize(m, d, p_lam)
    if hp is None:
        return None

    def b_at(k, beta):
        alpha = assemble_vec(smask, k, beta)
        return coeff_of(hp, vec_to_mono(alpha)) / multinomial(alpha)

    out = []
    for j in compositions_up_to(m_s, d):
        pj = {}
        for k in sub_compositions(j):
            k_sum = sum(k)
            sgn = 1 if k_sum % 2 == 0 else -1
            binom_prod = 1
            for ji, ki in zip(j, k):
                binom_prod *= comb(ji, ki)
            qk = canon(
                {
                    vec_to_mono(beta): b_at(k, beta) * multinomial(beta)
                    for beta in compositions(m_b, d - k_sum)
                }
            )
            hk = p_mul(qk, p_pow(sum_vars(m_b), k_sum))
            pj = p_add(pj, p_scale(F(sgn * binom_prod), hk))
        out.extend(c for _, c in bern_coeff_rows(m_b, d, pj))
    return out


# ---------------------------------------------------------------------
# Terms and formulas (the corpus AST; the Lean Term/Formula shapes)
# ---------------------------------------------------------------------


def idx_free(t):
    tag = t[0]
    if tag in ("var", "const"):
        return True
    if tag == "idx":
        return False
    if tag == "neg":
        return idx_free(t[1])
    return idx_free(t[1]) and idx_free(t[2])


def idx_bounded(t, n):
    tag = t[0]
    if tag in ("var", "const"):
        return True
    if tag == "idx":
        return t[2] < n and idx_bounded(t[1], n)
    if tag == "neg":
        return idx_bounded(t[1], n)
    return idx_bounded(t[1], n) and idx_bounded(t[2], n)


def to_poly_wire(t):
    """Term.toPoly over wire variables (keys ('w', pool index))."""
    tag = t[0]
    if tag == "var":
        return {((("w", t[1]), 1),): F(1)}
    if tag == "const":
        return p_const(F(*t[1]))
    if tag == "add":
        return p_add(to_poly_wire(t[1]), to_poly_wire(t[2]))
    if tag == "sub":
        return p_sub(to_poly_wire(t[1]), to_poly_wire(t[2]))
    if tag == "mul":
        return p_mul(to_poly_wire(t[1]), to_poly_wire(t[2]))
    if tag == "neg":
        return p_neg(to_poly_wire(t[1]))
    raise AssertionError(f"unexpected wire-poly tag {tag}")


def coord_poly_plain(t):
    """Term.asCoordPolyIdx? — None = outside the fragment."""
    tag = t[0]
    if tag == "var":
        return None
    if tag == "const":
        return p_const(F(*t[1]))
    if tag == "idx":
        return p_var(t[2]) if t[1][0] == "var" else None
    if tag == "neg":
        inner = coord_poly_plain(t[1])
        return None if inner is None else p_neg(inner)
    l, r = coord_poly_plain(t[1]), coord_poly_plain(t[2])
    if l is None or r is None:
        return None
    return {"add": p_add, "sub": p_sub, "mul": p_mul}[tag](l, r)


def as_coord_poly(t):
    """Term.asCoordPoly? — None = outside the fragment (decided false
    for the checker)."""
    if idx_free(t):
        p = to_poly_wire(t)
        vs = p_vars(p)
        if len(vs) == 0:
            return p
        if len(vs) == 1:
            return {tuple((0, e) for _, e in m): c for m, c in p.items()}
        return None
    return coord_poly_plain(t)


def term_eval(t, c):
    tag = t[0]
    if tag == "hole":
        return c
    if tag in ("var", "idx"):
        return None
    if tag == "const":
        return F(*t[1])
    if tag == "neg":
        v = term_eval(t[1], c)
        return None if v is None else -v
    l, r = term_eval(t[1], c), term_eval(t[2], c)
    if l is None or r is None:
        return None
    return {"add": l + r, "sub": l - r, "mul": l * r}[tag]


def formula_eval(f, c):
    tag = f[0]
    if tag == "true":
        return True
    if tag == "false":
        return False
    if tag == "sph":
        return None
    if tag == "atom":
        l, r = term_eval(f[2], c), term_eval(f[3], c)
        if l is None or r is None:
            return None
        return {
            "lt": l < r,
            "le": l <= r,
            "eq": l == r,
            "ge": l >= r,
            "gt": l > r,
            "ne": l != r,
        }[f[1]]
    l, r = formula_eval(f[1], c), formula_eval(f[2], c)
    if l is None or r is None:
        return None
    return (l and r) if tag == "and" else (l or r)


def satisfies(pred, c):
    return formula_eval(pred, c) is True


# ---------------------------------------------------------------------
# The two checkers (Lean Core/Catalogue.lean)
# ---------------------------------------------------------------------


def bern_check(geom, degree, poly, pred):
    n, amb = geom["n"], geom["amb"]
    sverts = sorted(geom["sverts"])
    everts = set(geom["everts"])
    if len(sverts) != amb + 1:
        return False
    p = as_coord_poly(poly)
    if p is None:
        return False
    if idx_free(poly):
        if p_vars(p) and amb != 1:
            return False
    else:
        if everts or not idx_bounded(poly, amb):
            return False
    coords = [[F(*geom["coords"][v][j]) for j in range(amb)] for v in sverts]
    smask = [v in everts for v in sverts]
    grid = fd_bernstein_grid(coords, smask, degree, p)
    if grid is None:
        return False
    return all(satisfies(pred, c) for c in grid)


def interval_1d(geom):
    if geom["amb"] != 1:
        return None
    if geom["everts"]:
        return None
    sverts = sorted(geom["sverts"])
    if len(sverts) != 2:
        return None
    a, b = sverts
    v0, v1 = F(*geom["coords"][a][0]), F(*geom["coords"][b][0])
    if v0 < v1:
        return (v0, v1)
    if v1 < v0:
        return (v1, v0)
    return None


def cover_check(parent, branches):
    main = interval_1d(parent)
    if main is None:
        return False
    ivs = []
    for br in branches:
        iv = interval_1d(br)
        if iv is None:
            return False
        ivs.append(iv)
    lo, hi = main
    r = lo
    for _ in range(len(ivs)):
        for a, b in ivs:
            if a <= r < b:
                r = b
    return hi <= r


# ---------------------------------------------------------------------
# Case generation (seeded; verdicts derived above)
# ---------------------------------------------------------------------

rng = random.Random(0x15B3)


def qpair():
    return [rng.randint(-6, 6), rng.randint(1, 4)]


def qpair_nonzero():
    while True:
        q = qpair()
        if q[0] != 0:
            return q


def line_geom(everts=(), coords=None, extra_verts=0, mask=None):
    n = 2 + extra_verts
    if coords is None:
        while True:
            coords = [[qpair()] for _ in range(n)]
            if F(*coords[0][0]) != F(*coords[1][0]):
                break
    return {
        "n": n,
        "amb": 1,
        "coords": coords,
        "sverts": list(mask) if mask is not None else [0, 1],
        "everts": list(everts),
    }


def nd_geom(amb, everts=()):
    n = amb + 1
    coords = [[qpair() for _ in range(amb)] for _ in range(n)]
    return {
        "n": n,
        "amb": amb,
        "coords": coords,
        "sverts": list(range(n)),
        "everts": list(everts),
    }


def wire_poly(deg, w=0):
    """A random univariate wire polynomial of exact degree `deg`,
    built as nested add/mul AST."""
    t = ["const", qpair()]
    for e in range(1, deg + 1):
        c = qpair_nonzero() if e == deg else qpair()
        mono = ["var", w]
        for _ in range(e - 1):
            mono = ["mul", mono, ["var", w]]
        t = ["add", t, ["mul", ["const", c], mono]]
    return t


def idx_poly(amb, deg):
    """A random idx-form polynomial in x₀..x_{amb−1}, total degree ≤
    `deg`, at least one idx node."""
    terms = ["const", qpair()]
    for _ in range(rng.randint(1, 3)):
        e = rng.randint(1, max(1, deg))
        mono = ["idx", ["var", 0], rng.randrange(amb)]
        for _ in range(e - 1):
            mono = ["mul", mono, ["idx", ["var", 0], rng.randrange(amb)]]
        terms = ["add", terms, ["mul", ["const", qpair()], mono]]
    return terms


def atom_pred():
    cmp_op = rng.choice(["lt", "le", "eq", "ge", "gt", "ne"])
    if rng.random() < 0.5:
        return ["atom", cmp_op, ["hole"], ["const", qpair()]]
    return ["atom", cmp_op, ["const", qpair()], ["hole"]]


def rand_pred(depth=2):
    if depth == 0 or rng.random() < 0.5:
        return atom_pred()
    tag = rng.choice(["and", "or"])
    return [tag, rand_pred(depth - 1), rand_pred(depth - 1)]


coeffs_cases = []


def add_coeffs(kind, geom, degree, poly, pred):
    coeffs_cases.append(
        {
            "kind": kind,
            "geom": geom,
            "degree": degree,
            "poly": poly,
            "pred": pred,
            "verdict": bern_check(geom, degree, poly, pred),
        }
    )


# 1-D wire polynomials, empty and nonempty extension masks, honest
# degrees.
for i in range(60):
    deg = rng.randint(0, 3)
    ev = rng.choice([(), (0,), (1,)])
    g = line_geom(everts=ev)
    add_coeffs("holds1d" if i % 2 == 0 else "sweep1d", g, deg, wire_poly(deg), rand_pred())

# Degree lies and slack degrees.
for _ in range(15):
    true_deg = rng.randint(1, 3)
    claimed = rng.choice([true_deg - 1, true_deg + 1])
    g = line_geom()
    add_coeffs("degreeplay", g, claimed, wire_poly(true_deg), rand_pred())

# mB = 0 (the whole simplex extended): decided false.
for _ in range(5):
    g = line_geom(everts=(0, 1))
    add_coeffs("emptycore", g, 1, wire_poly(1), rand_pred())

# Multivariate idx polynomials on random full-dimensional geometries.
for _ in range(30):
    amb = rng.choice([2, 3])
    deg = rng.randint(1, 2)
    g = nd_geom(amb)
    add_coeffs("multivar", g, deg + rng.randint(0, 1), idx_poly(amb, deg), rand_pred())

# The standard simplex fixture family (the Lean comparator fixture's
# geometry) with varied predicates.
std = {
    "n": 4,
    "amb": 3,
    "coords": [
        [[0, 1], [0, 1], [0, 1]],
        [[1, 1], [0, 1], [0, 1]],
        [[0, 1], [1, 1], [0, 1]],
        [[0, 1], [0, 1], [1, 1]],
    ],
    "sverts": [0, 1, 2, 3],
    "everts": [],
}
fixture_poly = [
    "add",
    ["add", ["const", [1, 1]], ["mul", ["idx", ["var", 0], 0], ["idx", ["var", 0], 1]]],
    ["mul", ["idx", ["var", 0], 2], ["idx", ["var", 0], 2]],
]
for thr in ([0, 1], [3, 2], [1, 1], [-1, 1], [2, 1]):
    add_coeffs("fixture", std, 2, fixture_poly, ["atom", "ge", ["hole"], ["const", list(thr)]])

# Gate probes: wire polynomial in higher dimension; two wires; idx out
# of bounds; idx with nonempty extension; non-full-dimensional masks.
for _ in range(6):
    add_coeffs("scalargate", nd_geom(2), 1, wire_poly(1), rand_pred())
for _ in range(4):
    two = ["add", ["var", 0], ["mul", ["const", qpair()], ["var", 1]]]
    add_coeffs("twowires", line_geom(), 1, two, rand_pred())
for _ in range(4):
    amb = 2
    bad = ["add", ["const", qpair()], ["idx", ["var", 0], amb]]
    add_coeffs("idxbound", nd_geom(amb), 1, bad, rand_pred())
for _ in range(4):
    amb = 2
    add_coeffs("idxext", nd_geom(amb, everts=(0,)), 1, idx_poly(amb, 1), rand_pred())
for _ in range(4):
    g = line_geom(extra_verts=1, mask=[0, 1, 2])
    add_coeffs("dimension", g, 1, wire_poly(1), rand_pred())
for _ in range(3):
    g = line_geom(mask=[0])
    add_coeffs("dimension", g, 1, wire_poly(1), rand_pred())

# Unevaluable predicates (free wire / spec hole): decided false.
for _ in range(5):
    bad_pred = rng.choice(
        [
            ["atom", "ge", ["var", 1], ["const", [0, 1]]],
            ["sph"],
            ["or", atom_pred(), ["atom", "le", ["var", 2], ["hole"]]],
        ]
    )
    add_coeffs("unevalpred", line_geom(), 1, wire_poly(1), bad_pred)

# Constant polynomials in any dimension.
for _ in range(5):
    amb = rng.choice([1, 2, 3])
    g = nd_geom(amb) if amb > 1 else line_geom()
    c = qpair()
    pred = ["atom", rng.choice(["ge", "le", "gt", "lt"]), ["hole"], ["const", qpair()]]
    add_coeffs("constant", g, rng.randint(0, 2), ["const", c], pred)

# ---------------------------------------------------------------------
cover_cases = []


def add_cover(kind, parent, branches):
    cover_cases.append(
        {
            "kind": kind,
            "parent": parent,
            "branches": branches,
            "verdict": cover_check(parent, branches),
        }
    )


def interval_geom(a, b, everts=(), mask=(0, 1)):
    return {
        "n": 2,
        "amb": 1,
        "coords": [[list(a)], [list(b)]],
        "sverts": list(mask),
        "everts": list(everts),
    }


def frac_pair(fr):
    return [fr.numerator, fr.denominator]


for i in range(45):
    lo, hi = sorted([F(*qpair()), F(*qpair())])
    if lo == hi:
        hi = lo + 1
    parent = interval_geom(frac_pair(lo), frac_pair(hi))
    nb = rng.randint(1, 4)
    if rng.random() < 0.55:
        # An intended cover: a partition with occasional overlap,
        # permuted.
        cuts = sorted(rng.uniform(0, 1) for _ in range(nb - 1))
        points = [lo] + [lo + F(c).limit_denominator(8) * (hi - lo) for c in cuts] + [hi]
        brs = []
        for k in range(nb):
            a, b = points[k], points[k + 1]
            if rng.random() < 0.3:
                a -= F(1, rng.randint(2, 5))
            if a == b:
                b = b + F(1, 7)
            brs.append(interval_geom(frac_pair(a), frac_pair(b)))
        rng.shuffle(brs)
    else:
        brs = []
        for _ in range(nb):
            a, b = sorted([F(*qpair()), F(*qpair())])
            if a == b:
                b = a + F(1, 3)
            brs.append(interval_geom(frac_pair(a), frac_pair(b)))
    add_cover("chain", parent, brs)

# Gap mutants: a partition with one branch shrunk.
for _ in range(10):
    parent = interval_geom([0, 1], [2, 1])
    brs = [
        interval_geom([0, 1], [1, 1]),
        interval_geom([rng.randint(5, 9), 4], [2, 1]),
    ]
    add_cover("gapmutant", parent, brs)

# Exact single-branch covers and overshoots.
for _ in range(8):
    lo, hi = sorted([F(*qpair()), F(*qpair())])
    if lo == hi:
        hi = lo + 1
    parent = interval_geom(frac_pair(lo), frac_pair(hi))
    slack = F(rng.randint(0, 2), 3)
    brs = [interval_geom(frac_pair(lo - slack), frac_pair(hi + slack))]
    add_cover("single", parent, brs)

# None-branch probes: degenerate, point-mask, extended, 2-D parents.
add_cover(
    "degenerate",
    interval_geom([0, 1], [1, 1]),
    [interval_geom([1, 2], [1, 2])],
)
add_cover(
    "pointmask",
    interval_geom([0, 1], [1, 1]),
    [interval_geom([0, 1], [2, 1], mask=(0,))],
)
add_cover(
    "extbranch",
    interval_geom([0, 1], [1, 1]),
    [interval_geom([0, 1], [2, 1], everts=(0,))],
)
add_cover(
    "extparent",
    interval_geom([0, 1], [1, 1], everts=(1,)),
    [interval_geom([0, 1], [2, 1])],
)
add_cover(
    "reversedcoords",
    interval_geom([2, 1], [0, 1]),
    [interval_geom([5, 2], [-1, 2])],
)
add_cover("zerobranches", interval_geom([0, 1], [1, 1]), [])

corpus = {"coeffs": coeffs_cases, "cover": cover_cases}
hold_c = sum(1 for c in coeffs_cases if c["verdict"])
hold_v = sum(1 for c in cover_cases if c["verdict"])
import sys

print(
    f"coeffs: {len(coeffs_cases)} ({hold_c} hold) · "
    f"cover: {len(cover_cases)} ({hold_v} hold)",
    file=sys.stderr,
)
print(json.dumps(corpus, indent=1))
