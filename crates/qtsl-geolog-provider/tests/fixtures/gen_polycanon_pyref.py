#!/usr/bin/env python3
"""Generator for the qtsl_poly_canonical cross-implementation corpus.

The independent authority is sympy: a stored term list is canonical
iff it EQUALS the canonical form of the polynomial it denotes —
sympy merges duplicate monomials, drops zero coefficients, and the
canonical order is plain ascending tuple sort on dense exponent
tuples (carillon manifest.Poly's `tuple(sorted(...))`, transcribed).
The rust evaluator decides the same property through three local
predicates (nonzero coeffs, uniform width, strict lex ascent); the
corpus is the bridge asserting the two decision procedures agree on
the merge/zero-drop/sort semantics. Width mutants are deliberately
absent here — a mixed-width list denotes no sympy polynomial, so the
authority has no verdict; that obligation is covered by the unit and
dispatch mutants instead.

Deterministic (seeded); regenerate with:
    python3 gen_polycanon_pyref.py > polycanon_pyref_corpus.json
"""

import itertools
import json
import random
import sys
from fractions import Fraction

import sympy

random.seed(0x536)  # fixed seed: the committed fixture corpus depends on it

NVARS_CHOICES = [1, 2, 3]
SYMS = sympy.symbols("x0 x1 x2")


def canonical_terms(raw, nvars):
    """sympy's arm: merge, zero-drop, ascending tuple sort."""
    expr = sympy.Integer(0)
    for expts, num, den in raw:
        mono = sympy.Integer(1)
        for v, e in enumerate(expts):
            mono *= SYMS[v] ** e
        expr += sympy.Rational(num, den) * mono
    poly = sympy.Poly(expr, *SYMS[:nvars])
    terms = [(tuple(m), Fraction(str(c))) for m, c in poly.terms()]
    terms.sort()  # ascending tuple sort == carillon's canonical order
    return [
        (list(m), int(c.numerator), int(c.denominator)) for m, c in terms
    ]


def random_raw(nvars, nterms):
    raw = []
    for _ in range(nterms):
        expts = [random.randint(0, 3) for _ in range(nvars)]
        num = random.choice([n for n in range(-5, 6)])
        den = random.randint(1, 4)
        raw.append((expts, num, den))
    return raw


def row(raw, nvars, note):
    # Cells cross the wire in canonical ℚ representation (lowest
    # terms — the ground invariant this oracle does NOT re-adjudicate),
    # so the stored terms are emitted reduced; term ORDER and monomial
    # multiplicity are exactly what the oracle adjudicates.
    reduced = [
        (list(e), int(Fraction(n, d).numerator), int(Fraction(n, d).denominator))
        for e, n, d in raw
    ]
    canon = canonical_terms(raw, nvars)
    # The authority's verdict: the stored list is canonical iff it
    # equals sympy's canonical rendering, coefficient-exactly.
    verdict = reduced == canon
    return {"nvars": nvars, "terms": reduced, "verdict": verdict, "note": note}


def main():
    rows = []
    # 1. sympy-canonicalized random polynomials: always-true rows
    #    (including collapses to zero when everything cancels).
    for i in range(16):
        nvars = random.choice(NVARS_CHOICES)
        raw = random_raw(nvars, random.randint(0, 6))
        canon = canonical_terms(raw, nvars)
        rows.append(
            row(
                [(tuple(e), n, d) for e, n, d in canon],
                nvars,
                f"sympy-canonicalized random poly #{i}",
            )
        )
    # 2. raw random lists (unmerged, unsorted, zero coeffs possible):
    #    verdict decided by the authority, either way.
    for i in range(16):
        nvars = random.choice(NVARS_CHOICES)
        raw = random_raw(nvars, random.randint(1, 6))
        rows.append(row(raw, nvars, f"raw random term list #{i}"))
    # 3. adversarial perturbations of canonical lists.
    for i in range(12):
        nvars = random.choice(NVARS_CHOICES)
        canon = canonical_terms(random_raw(nvars, 5), nvars)
        raw = [(tuple(e), n, d) for e, n, d in canon]
        kind = i % 4
        if kind == 0 and len(raw) >= 2:
            j = random.randrange(len(raw) - 1)
            raw[j], raw[j + 1] = raw[j + 1], raw[j]
            note = "adjacent swap"
        elif kind == 1 and raw:
            e, n, d = raw[random.randrange(len(raw))]
            raw.append((e, 0, 1))  # a zero-coefficient duplicate at the end
            note = "appended zero-coeff term"
        elif kind == 2 and raw:
            j = random.randrange(len(raw))
            e, n, d = raw[j]
            raw[j] = (e, n, 2 * d)
            raw.insert(j + 1, (e, n, 2 * d))  # split one coeff across two terms
            note = "split coefficient (duplicate monomial)"
        else:
            note = "identity perturbation (control)"
        rows.append(row(raw, nvars, note))
    json.dump(rows, sys.stdout, indent=1)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
