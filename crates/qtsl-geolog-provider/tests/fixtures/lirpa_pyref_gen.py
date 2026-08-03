#!/usr/bin/env python3
"""Frozen cross-implementation corpus generator for lirpaConclusionForm.

Independent transcription of the Lean build (Core/Catalogue.lean):

    affineWireTerm offset slope w
      = TAdd(TConst(offset), TMul(TConst(slope), TVar(w)))
    lirpaConclusionForm preact post a b g d F
      <=> F = FAnd(FAtomLE(affineWireTerm(b, a, preact), TVar(post)),
                   FAtomLE(TVar(post), affineWireTerm(d, g, preact)))

Verdicts are DERIVED, never asserted: every case's verdict is the
structural equality of its formula AST against the expected AST built
from its CLAIM parameters — so mutations that happen to be identities
(crossed beta/delta when beta == delta, wire swaps when pre == post)
honestly land as holds, and the rust arm must agree there too.

AST encoding (JSON):
    term    := ["var", wire_index] | ["const", [num, den]]
             | ["add"|"mul"|"sub", term, term]
    formula := ["and"|"or", formula, formula]
             | ["atom", "lt"|"le"|"eq"|"ge"|"gt"|"ne", term, term]
             | ["true"]

Constants are reduced fractions with positive denominator (canonical Q).
Run from this directory: python3 lirpa_pyref_gen.py
"""

import json
import random
from fractions import Fraction

random.seed(20260722)

SPICE = [
    Fraction(0),
    Fraction(1),
    Fraction(-1),
    Fraction(1, 2),
    Fraction(-1, 4),
    Fraction(7, 3),
    Fraction(-22, 7),
    Fraction(10**12, 999983),
    Fraction(-(10**9), 7),
]


def rand_q():
    if random.random() < 0.25:
        return random.choice(SPICE)
    return Fraction(random.randint(-50, 50), random.randint(1, 12))


def qp(q):
    q = Fraction(q)
    return [q.numerator, q.denominator]


def affine(off, slp, w):
    return ["add", ["const", qp(off)], ["mul", ["const", qp(slp)], ["var", w]]]


def expected(a, b, g, d, pre, post):
    return [
        "and",
        ["atom", "le", affine(b, a, pre), ["var", post]],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def case(kind, build, claim, ast):
    """build/claim = (a, b, g, d, pre, post); verdict derived."""
    ca, cb, cg, cd, cpre, cpost = claim
    return {
        "kind": kind,
        "alpha": qp(ca),
        "beta": qp(cb),
        "gamma": qp(cg),
        "delta": qp(cd),
        "pre_w": cpre,
        "post_w": cpost,
        "formula": ast,
        "verdict": ast == expected(ca, cb, cg, cd, cpre, cpost),
    }


def rand_params(pre_pool=(0, 1, 2), post_pool=(0, 1)):
    return (
        rand_q(),
        rand_q(),
        rand_q(),
        rand_q(),
        random.choice(pre_pool),
        random.choice(post_pool),
    )


cases = []

# ---- holds: correct builds over varied parameters --------------------
for i in range(120):
    p = rand_params()
    a, b, g, d, pre, post = p
    cases.append(case(f"holds_random_{i}", p, p, expected(*p)))

# Deterministic edge holds.
EDGES = [
    ("holds_demo_data", (Fraction(1, 2), Fraction(-1, 4), Fraction(1, 2), Fraction(1, 2), 0, 1)),
    ("holds_all_zero", (Fraction(0), Fraction(0), Fraction(0), Fraction(0), 0, 1)),
    ("holds_zero_offset", (Fraction(-3), Fraction(0), Fraction(7, 3), Fraction(12), 0, 1)),
    ("holds_same_wire", (Fraction(1, 3), Fraction(-2, 5), Fraction(4), Fraction(9, 7), 2, 2)),
    ("holds_beta_eq_delta", (Fraction(5), Fraction(3, 8), Fraction(-5), Fraction(3, 8), 1, 0)),
    ("holds_big_values", (Fraction(10**12, 999983), Fraction(-(10**9), 7), Fraction(10**6), Fraction(-1, 10**6), 0, 1)),
]
for name, p in EDGES:
    cases.append(case(name, p, p, expected(*p)))


# ---- mutants: one deliberate deviation each, verdict derived ---------
def m_or(p):
    ast = expected(*p)
    return ["or", ast[1], ast[2]]


def m_swap(p):
    ast = expected(*p)
    return ["and", ast[2], ast[1]]


def m_ltlow(p):
    ast = expected(*p)
    ast[1][1] = "lt"
    return ast


def m_geup(p):
    ast = expected(*p)
    ast[2][1] = "ge"
    return ast


def m_orientlow(p):
    a, b, g, d, pre, post = p
    return [
        "and",
        ["atom", "le", ["var", post], affine(b, a, pre)],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def m_orientup(p):
    a, b, g, d, pre, post = p
    return [
        "and",
        ["atom", "le", affine(b, a, pre), ["var", post]],
        ["atom", "le", affine(d, g, pre), ["var", post]],
    ]


def m_offright(p):
    a, b, g, d, pre, post = p
    lo = ["add", ["mul", ["const", qp(a)], ["var", pre]], ["const", qp(b)]]
    return [
        "and",
        ["atom", "le", lo, ["var", post]],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def m_slpright(p):
    a, b, g, d, pre, post = p
    lo = ["add", ["const", qp(b)], ["mul", ["var", pre], ["const", qp(a)]]]
    return [
        "and",
        ["atom", "le", lo, ["var", post]],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def m_sub(p):
    a, b, g, d, pre, post = p
    lo = ["sub", ["const", qp(b)], ["mul", ["const", qp(a)], ["var", pre]]]
    return [
        "and",
        ["atom", "le", lo, ["var", post]],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def m_bareprod(p):
    a, b, g, d, pre, post = p
    lo = ["mul", ["const", qp(a)], ["var", pre]]
    return [
        "and",
        ["atom", "le", lo, ["var", post]],
        ["atom", "le", ["var", post], affine(d, g, pre)],
    ]


def m_constup(p):
    a, b, g, d, pre, post = p
    return [
        "and",
        ["atom", "le", affine(b, a, pre), ["var", post]],
        ["atom", "le", ["var", post], ["const", qp(d)]],
    ]


def m_truearm(p):
    ast = expected(*p)
    return ["and", ast[1], ["true"]]


def m_atomonly(p):
    return expected(*p)[1]


def m_extraand(p):
    return ["and", expected(*p), ["true"]]


STRUCTURAL = [
    ("mutant_or", m_or),
    ("mutant_swap", m_swap),
    ("mutant_ltlow", m_ltlow),
    ("mutant_geup", m_geup),
    ("mutant_orientlow", m_orientlow),
    ("mutant_orientup", m_orientup),
    ("mutant_offright", m_offright),
    ("mutant_slpright", m_slpright),
    ("mutant_sub", m_sub),
    ("mutant_constup", m_constup),
    ("mutant_truearm", m_truearm),
    ("mutant_atomonly", m_atomonly),
    ("mutant_extraand", m_extraand),
]

for name, fn in STRUCTURAL:
    for i in range(8):
        p = rand_params()
        cases.append(case(f"{name}_{i}", p, p, fn(p)))

# Bare product specifically at beta = 0 (the no-zero-special-case pin).
for i in range(8):
    a, _, g, d, pre, post = rand_params()
    p = (a, Fraction(0), g, d, pre, post)
    cases.append(case(f"mutant_bareprod_{i}", p, p, m_bareprod(p)))


# Claim-side mutants: the build is correct for its own parameters; the
# CLAIM disagrees (or, on engineered diagonals, agrees — derived).
def claim_mut(name, n, transform, engineer=None):
    for i in range(n):
        p = rand_params()
        if engineer:
            p = engineer(p)
        claim = transform(p)
        cases.append(case(f"{name}_{i}", p, claim, expected(*p)))


claim_mut(
    "mutant_alpha",
    8,
    lambda p: (p[0] + 1, p[1], p[2], p[3], p[4], p[5]),
)
claim_mut(
    "mutant_beta",
    8,
    lambda p: (p[0], p[1] - Fraction(1, 3), p[2], p[3], p[4], p[5]),
)
claim_mut(
    "mutant_gamma",
    8,
    lambda p: (p[0], p[1], -p[2], p[3], p[4], p[5]),
)
claim_mut(
    "mutant_delta",
    8,
    lambda p: (p[0], p[1], p[2], p[3] + 2, p[4], p[5]),
)
# Crossed beta/delta — two engineered no-ops (beta == delta) among the
# eight, landing as derived holds.
claim_mut(
    "mutant_crossbd",
    6,
    lambda p: (p[0], p[3], p[2], p[1], p[4], p[5]),
)
claim_mut(
    "mutant_crossbd_noop",
    2,
    lambda p: (p[0], p[3], p[2], p[1], p[4], p[5]),
    engineer=lambda p: (p[0], p[1], p[2], p[1], p[4], p[5]),
)
# Claim wires swapped — two engineered no-ops (pre == post) among them.
claim_mut(
    "mutant_wireswap",
    6,
    lambda p: (p[0], p[1], p[2], p[3], p[5], p[4]),
)
claim_mut(
    "mutant_wireswap_noop",
    2,
    lambda p: (p[0], p[1], p[2], p[3], p[5], p[4]),
    engineer=lambda p: (p[0], p[1], p[2], p[3], 1, 1),
)
# Claim post pointed at the third wire.
claim_mut(
    "mutant_claimpost",
    8,
    lambda p: (p[0], p[1], p[2], p[3], p[4], 2),
)

with open("lirpa_pyref_corpus.json", "w") as fh:
    json.dump({"seed": 20260722, "cases": cases}, fh, indent=1)

n_holds = sum(1 for c in cases if c["kind"].startswith("holds"))
n_mut = sum(1 for c in cases if c["kind"].startswith("mutant"))
n_true = sum(1 for c in cases if c["verdict"])
n_false = len(cases) - n_true
print(
    f"{len(cases)} cases: {n_holds} holds-kind, {n_mut} mutant-kind; "
    f"verdicts {n_true} true / {n_false} false"
)
