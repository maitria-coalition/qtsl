#!/usr/bin/env python3
"""Corpus generator for the enclosure-family cross-implementation
battery (`enclosureWitnessValid`).

Expected verdicts are computed on python Fractions with DIRECT rational
division — an independent arithmetic path from the row-native
evaluator, which decides the tail clause by cross-multiplication and
never divides:

  maclaurin(tag, k)   the tag's exact coefficient recurrence
  tail(n, r)          r^(n+1)/(n+1)! * (n+2)/((n+2)-r)
  verdict             (0 <= r) and (r < n+2) and (tail(n, r) <= cap)

The coefficient prefix is recomputed here for every case (and its
length asserted) exactly so this generator IS the model-level check,
not a subset of it — the same posture as the wire checker's python
twin. All cases stay inside the spec model's representable states
(tag in {0, 1, 2}; n within the evaluator's degree budget; numerators
and denominators asserted to fit the i64/u64 literal cells). Refusal
behaviour is battery territory, not corpus territory. Deterministic:
reseeded PRNG, frozen output. Regenerate with
`python3 enclosure_pyref_gen.py > enclosure_pyref_corpus.json` only
alongside a deliberate corpus revision — replay disagreement is
stop-and-investigate, never adjust-the-corpus.
"""

import json
import math
import random
from fractions import Fraction

rng = random.Random(0x536E)  # deterministic corpus

TAGS = (0, 1, 2)  # wire order: 0 = exp, 1 = sin, 2 = cos


def maclaurin(tag, k):
    if tag == 0:
        return Fraction(1, math.factorial(k))
    if tag == 1:
        if k % 2 == 1:
            return Fraction((-1) ** ((k - 1) // 2), math.factorial(k))
        return Fraction(0)
    if tag == 2:
        if k % 2 == 0:
            return Fraction((-1) ** (k // 2), math.factorial(k))
        return Fraction(0)
    raise ValueError(f"unknown tag {tag}")


def tail(n, r):
    # Direct division — the independent arithmetic path.
    return (
        Fraction(r) ** (n + 1)
        / math.factorial(n + 1)
        * Fraction(n + 2)
        / (Fraction(n + 2) - Fraction(r))
    )


def verdict(tag, n, r, cap):
    if not (0 <= r < n + 2):
        return False
    coeffs = tuple(maclaurin(tag, k) for k in range(n + 1))
    assert len(coeffs) == n + 1  # the executed recompute, kept executed
    return tail(n, r) <= cap


def frac_pair(x):
    f = Fraction(x)
    assert -(2**63) <= f.numerator < 2**63, f"numerator overflows i64: {f}"
    assert 0 < f.denominator < 2**64, f"denominator overflows u64: {f}"
    return [f.numerator, f.denominator]


def case(tag, n, r, cap):
    r, cap = Fraction(r), Fraction(cap)
    return {
        "tag": tag,
        "n": n,
        "r": frac_pair(r),
        "cap": frac_pair(cap),
        "verdict": verdict(tag, n, r, cap),
    }


def representable(r, cap):
    for f in (Fraction(r), Fraction(cap)):
        if not (-(2**63) <= f.numerator < 2**63 and 0 < f.denominator < 2**64):
            return False
    return True


cases = []

# The Lean kernel receipts' parameter triples, all three tags (the
# accepts sit exactly at the bound; the two wire-named mutants ride
# along as their falsifying neighbours).
for tag in TAGS:
    cases.append(case(tag, 7, 1, Fraction(1, 35840)))       # at the bound
    cases.append(case(tag, 7, 1, Fraction(1, 40000)))       # tail lie
    cases.append(case(tag, 7, 9, 1))                        # radius overrun (r = n+2)
    cases.append(case(tag, 4, Fraction(1, 2), Fraction(1, 3520)))
    cases.append(case(tag, 6, 1, Fraction(1, 4410)))

# Boundary sweeps: r at 0, interior, just inside n+2; caps at the
# exact tail, one hair below, one hair above, zero, and negative.
for tag in TAGS:
    for n in range(0, 9):
        for r in (
            Fraction(0),
            Fraction(1, 3),
            Fraction(1),
            Fraction(n + 1),
            Fraction(n + 2) - Fraction(1, 7),
        ):
            if not (0 <= r < n + 2):
                continue
            t = tail(n, r)
            hair = Fraction(1, 10**6)
            for cap in (
                t,
                t * (1 - hair),
                t * (1 + hair),
                Fraction(0),
                Fraction(-1, 3),
            ):
                if representable(r, cap):
                    cases.append(case(tag, n, r, cap))

# Decided-false radius classes: negative r, r = n+2 exactly, r beyond.
for tag in TAGS:
    for n in (0, 3, 7):
        cases.append(case(tag, n, Fraction(-1, 2), 1))
        cases.append(case(tag, n, Fraction(n + 2), 10**9))
        cases.append(case(tag, n, Fraction(n + 3), 10**9))

# Random interior sweep, verdicts recomputed from the arithmetic
# (never assumed from which branch generated them).
for _ in range(120):
    tag = rng.choice(TAGS)
    n = rng.randint(0, 10)
    r = Fraction(rng.randint(0, (n + 2) * 12 - 1), 12)  # in [0, n+2)
    t = tail(n, r)
    mode = rng.random()
    if mode < 0.4:
        cap = t * Fraction(rng.randint(1, 40), rng.randint(1, 40))
    elif mode < 0.7:
        cap = t + Fraction(rng.randint(-3, 3), rng.randint(1, 10**4))
    else:
        cap = Fraction(rng.randint(-5, 5), rng.randint(1, 20))
    if representable(r, cap):
        cases.append(case(tag, n, r, cap))

n_true = sum(1 for c in cases if c["verdict"])
corpus = {
    "comment": "frozen cross-implementation corpus for enclosureWitnessValid; "
    "generated by enclosure_pyref_gen.py (python Fractions, direct division)",
    "counts": {"total": len(cases), "holds": n_true, "fails": len(cases) - n_true},
    "cases": cases,
}
print(json.dumps(corpus, indent=1))
