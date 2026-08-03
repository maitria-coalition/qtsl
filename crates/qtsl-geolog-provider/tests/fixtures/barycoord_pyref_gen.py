#!/usr/bin/env python3
"""Corpus generator for the barycentric-halfspace cross-implementation
battery.

Expected atom constants and verdicts are computed on python's
`fractions` module — an independent transcription of the spec's
one-dimensional barycentric construction and its positive
primitive-integer rescale (a different language and a different
rational representation from the row-native evaluator):

  lambda_a(x) = (V1 - x) / (V1 - V0),  lambda_b(x) = (x - V0) / (V1 - V0)
  atom_v = prim_affine(+-(slope, offset)), '+' for v in S, '-' otherwise,
  rendered (s'.t [+ c']) <= 0, the bare product exactly when c' = 0,
  the two atoms conjoined in increasing vertex order.

All cases stay inside the spec model's representable states (distinct
vertex coordinates, memberships in range, extension sets proper);
refusal behaviour is battery territory, not corpus territory. The
`none`-branch cases (vertex counts other than two) are included with
verdict false. Deterministic: reseeded PRNG, frozen output. Regenerate
with `python3 barycoord_pyref_gen.py > barycoord_pyref_corpus.json`
only alongside a deliberate corpus revision — replay disagreement is
stop-and-investigate, never adjust-the-corpus.
"""

import json
import random
from fractions import Fraction
from math import gcd

rng = random.Random(0xBA27C002)  # deterministic corpus


def lcm(a, b):
    return a // gcd(a, b) * b


def prim_affine(s, c):
    """The positive primitive-integer rescale of an affine pair."""
    if c == 0:
        sign = 1 if s > 0 else (-1 if s < 0 else 0)
        return (Fraction(sign), Fraction(0))
    big_l = lcm(s.denominator, c.denominator)
    g = gcd(
        abs(s.numerator * (big_l // s.denominator)),
        abs(c.numerator * (big_l // c.denominator)),
    )
    k = Fraction(big_l, g)
    return (k * s, k * c)


def bary_atoms(coords, simplex, ext):
    """The two rescaled atom constants in vertex order, or None on the
    construction's `none` branches."""
    if len(simplex) != 2:
        return None
    a, b = sorted(simplex)
    v0, v1 = coords[a], coords[b]
    if v0 == v1:
        return None
    den = v1 - v0
    coeffs = [
        (a, v1 / den, Fraction(-1) / den),
        (b, -v0 / den, Fraction(1) / den),
    ]
    out = []
    for vert, off, slp in coeffs:
        if vert in ext:
            s, c = slp, off
        else:
            s, c = -slp, -off
        out.append(prim_affine(s, c))
    return out


def atom_json(pair):
    s, c = pair
    entry = {"s": [s.numerator, s.denominator]}
    entry["c"] = None if c == 0 else [c.numerator, c.denominator]
    return entry


COORD_POOL = [
    Fraction(n, d) for d in (1, 2, 3, 4) for n in range(-6, 7) if gcd(abs(n), d) == 1 or n == 0
]
# Deduplicate values (0 appears once per denominator otherwise).
COORD_POOL = sorted(set(COORD_POOL))


def rand_complex():
    n = rng.randint(2, 5)
    coords = rng.sample(COORD_POOL, n)  # distinct along the one axis
    return coords


def rand_case():
    coords = rand_complex()
    n = len(coords)
    a, b = sorted(rng.sample(range(n), 2))
    ext = rng.choice([[], [a], [b]])  # proper subsets only
    atoms = bary_atoms(coords, [a, b], set(ext))
    assert atoms is not None, "distinct coordinates guarantee a build"
    return coords, [a, b], ext, atoms


def coords_json(coords):
    return [[c.numerator, c.denominator] for c in coords]


cases = []

# --- holds: the true rendering replays to a Holds verdict ------------
for _ in range(80):
    coords, simplex, ext, atoms = rand_case()
    cases.append(
        {
            "kind": "holds",
            "coords": coords_json(coords),
            "simplex": simplex,
            "ext": ext,
            "atoms": [atom_json(p) for p in atoms],
            "verdict": True,
        }
    )

# --- mutants: one perturbation each, verdict False --------------------


def perturb(atoms, which, how):
    out = [list(p) for p in atoms]
    s, c = out[which]
    if how == "const_shift":
        out[which] = [s, c + 1]
    elif how == "scale":
        out[which] = [2 * s, 2 * c]
    elif how == "flip":
        out[which] = [-s, -c]
    return [tuple(p) for p in out]


for i in range(80):
    coords, simplex, ext, atoms = rand_case()
    how = ["const_shift", "scale", "flip", "swap"][i % 4]
    if how == "swap":
        mutated = [atoms[1], atoms[0]]
    else:
        mutated = perturb(atoms, i % 2, how)
    assert mutated != atoms, "every mutant differs from the true form"
    cases.append(
        {
            "kind": f"mutant_{how}",
            "coords": coords_json(coords),
            "simplex": simplex,
            "ext": ext,
            "atoms": [atom_json(p) for p in mutated],
            "verdict": False,
        }
    )

# --- none branches: wrong vertex counts, decided False ----------------
FIXED_ATOMS = [
    {"s": [1, 1], "c": [-2, 1]},
    {"s": [-1, 1], "c": [1, 1]},
]
for i in range(20):
    coords = rand_complex()
    n = len(coords)
    k = 1 if i % 2 == 0 else min(3, n)
    if k == 3 and n < 3:
        k = 1
    simplex = sorted(rng.sample(range(n), k))
    ext = []
    cases.append(
        {
            "kind": "none_wrong_count",
            "coords": coords_json(coords),
            "simplex": simplex,
            "ext": ext,
            "atoms": FIXED_ATOMS,
            "verdict": False,
        }
    )

print(json.dumps({"cases": cases}, indent=1))
