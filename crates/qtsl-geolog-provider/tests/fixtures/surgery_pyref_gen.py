#!/usr/bin/env python3
"""Corpus generator for the surgery-family cross-implementation battery.

Expected verdicts are computed on an independent python AST — a
different language and a different tree representation from the
row-native evaluators — transcribing the Lean catalogue's specs
directly:

  conjunctAt(form, path, sub)        <=>  conj_get(form, path) == sub
  conjReplace(form, path, sub, res)  <=>  conj_replace(form, path, sub) == res
  substituteInFormula(form, w, t, r) <=>  subst_formula(form, w, t) == r
  applyPredicateToTerm(P, arg, r)    <=>  apply_pred(P, arg) == r

conj_get/conj_replace return None when the path walks off the ∧-tree
(the Lean `conjGet?`/`conjReplace?` `none` branch): the relation is then
decidedly FALSE — corpus territory, not a refusal. The hole is its own
constructor here, mirroring the row theory's `THole` (the Lean model's
`.var predicateHole`): wire substitution never touches it; predicate
application replaces exactly it.

Terms:    ["var", w] | ["const", n, d] | ["add", l, r] | ["mul", l, r]
        | ["sub", l, r] | ["neg", t] | ["idx", i, t] | ["hole"]
Formulas: ["atom", b, l, r] (b: 0=LT 1=LE 2=EQ 3=GE 4=GT 5=NE)
        | ["and", l, r] | ["or", l, r] | ["tt"] | ["ff"] | ["sph"]
(`FInRegion` needs nominal simplex geometry and is battery territory.)

All cases stay inside the representable model (canonical Q constants,
wires from a small pool); refusal behavior is battery territory, not
corpus territory. Deterministic: reseeded PRNG, frozen output.
Regenerate with `python3 surgery_pyref_gen.py > surgery_pyref_corpus.json`
only alongside a deliberate corpus revision — replay disagreement is
stop-and-investigate, never adjust-the-corpus.
"""

import json
import random
from fractions import Fraction
from math import gcd

rng = random.Random(0x5136_02)  # deterministic corpus

WIRES = [0, 1, 2, 3]


# ---------------------------------------------------------------- specs
# Independent transcriptions of Core/Catalogue.lean. Trees are plain
# lists, equality is list equality (structural).


def conj_get(f, path):
    for step in path:
        if f[0] != "and":
            return None
        f = f[1 + step]
    return f


def conj_replace(f, path, g):
    if not path:
        return g
    if f[0] != "and":
        return None
    step, rest = path[0], path[1:]
    inner = conj_replace(f[1 + step], rest, g)
    if inner is None:
        return None
    return ["and", inner, f[2]] if step == 0 else ["and", f[1], inner]


def subst_term(t, w, s):
    k = t[0]
    if k == "var":
        return s if t[1] == w else t
    if k in ("const", "hole"):
        return t
    if k in ("add", "mul", "sub"):
        return [k, subst_term(t[1], w, s), subst_term(t[2], w, s)]
    if k == "neg":
        return [k, subst_term(t[1], w, s)]
    if k == "idx":
        return [k, t[1], subst_term(t[2], w, s)]
    raise AssertionError(k)


def apply_term(t, arg):
    k = t[0]
    if k == "hole":
        return arg
    if k in ("var", "const"):
        return t
    if k in ("add", "mul", "sub"):
        return [k, apply_term(t[1], arg), apply_term(t[2], arg)]
    if k == "neg":
        return [k, apply_term(t[1], arg)]
    if k == "idx":
        return [k, t[1], apply_term(t[2], arg)]
    raise AssertionError(k)


def map_formula(f, tm):
    k = f[0]
    if k in ("tt", "ff", "sph"):
        return f
    if k == "atom":
        return ["atom", f[1], tm(f[2]), tm(f[3])]
    if k in ("and", "or"):
        return [k, map_formula(f[1], tm), map_formula(f[2], tm)]
    raise AssertionError(k)


def subst_formula(f, w, s):
    return map_formula(f, lambda t: subst_term(t, w, s))


def apply_pred(p, arg):
    return map_formula(p, lambda t: apply_term(t, arg))


# ------------------------------------------------------------ generators


def rand_const():
    while True:
        n = rng.randint(-4, 4)
        d = rng.choice([1, 1, 1, 2, 3])
        if gcd(abs(n), d) == 1 or n == 0:
            fr = Fraction(n, d)
            return ["const", fr.numerator, fr.denominator]


def rand_term(depth, holes=False):
    if depth == 0 or rng.random() < 0.3:
        leaves = ["var", "const"] + (["hole"] if holes else [])
        k = rng.choice(leaves)
        if k == "var":
            return ["var", rng.choice(WIRES)]
        if k == "hole":
            return ["hole"]
        return rand_const()
    k = rng.choice(["add", "mul", "sub", "neg", "idx"])
    if k in ("add", "mul", "sub"):
        return [k, rand_term(depth - 1, holes), rand_term(depth - 1, holes)]
    if k == "neg":
        return [k, rand_term(depth - 1, holes)]
    return ["idx", rng.randint(0, 3), rand_term(depth - 1, holes)]


def rand_formula(depth, holes=False):
    if depth == 0 or rng.random() < 0.25:
        k = rng.choice(["atom", "atom", "atom", "tt", "ff", "sph"])
        if k == "atom":
            return [
                "atom",
                rng.randint(0, 5),
                rand_term(2, holes),
                rand_term(2, holes),
            ]
        return [k]
    k = rng.choice(["and", "and", "or"])
    return [k, rand_formula(depth - 1, holes), rand_formula(depth - 1, holes)]


def rand_and_tree(depth):
    """A formula rich in ∧-nodes so random paths often stay on-tree."""
    if depth == 0 or rng.random() < 0.2:
        return rand_formula(1)
    return ["and", rand_and_tree(depth - 1), rand_and_tree(depth - 1)]


def rand_path(f, allow_interior=True):
    """A random path descending f's ∧-spine (possibly stopping at an
    interior ∧-node)."""
    path = []
    while f[0] == "and" and rng.random() < 0.7:
        step = rng.randint(0, 1)
        path.append(step)
        f = f[1 + step]
        if allow_interior and rng.random() < 0.2:
            break
    return path


def perturb_formula(f):
    """One random structural edit somewhere in the tree. Verdicts are
    recomputed from the trees below regardless, never assumed from
    which branch generated them."""
    k = f[0]
    r = rng.random()
    if k == "atom" and r < 0.5:
        return ["atom", (f[1] + 1 + rng.randint(0, 4)) % 6, f[2], f[3]]
    if k == "atom":
        return ["atom", f[1], perturb_term(f[2]), f[3]]
    if k in ("and", "or"):
        if r < 0.3:
            return [("or" if k == "and" else "and"), f[1], f[2]]
        if r < 0.65:
            return [k, perturb_formula(f[1]), f[2]]
        return [k, f[1], perturb_formula(f[2])]
    return rand_formula(1)  # nullary: swap for something else


def perturb_term(t):
    k = t[0]
    r = rng.random()
    if k == "var":
        return ["var", (t[1] + 1) % len(WIRES)] if r < 0.7 else ["hole"]
    if k == "const":
        return ["const", t[1] + 1, t[2]] if t[2] == 1 else rand_const()
    if k == "hole":
        return ["var", rng.choice(WIRES)] if r < 0.7 else rand_const()
    if k in ("add", "mul", "sub"):
        if r < 0.3:
            others = [x for x in ("add", "mul", "sub") if x != k]
            return [rng.choice(others), t[1], t[2]]
        if r < 0.65:
            return [k, perturb_term(t[1]), t[2]]
        return [k, t[1], perturb_term(t[2])]
    if k == "neg":
        return [k, perturb_term(t[1])] if r < 0.5 else t[1]
    return ["idx", (t[1] + 1) % 5, t[2]] if r < 0.5 else ["idx", t[1], perturb_term(t[2])]


# --------------------------------------------------------------- corpus

N = 80
corpus = {"conjunct_at": [], "conj_replace": [], "subst": [], "apply_pred": []}

for i in range(N):
    form = rand_and_tree(3)
    branch = i % 4
    if branch == 0:  # true by construction
        path = rand_path(form)
        sub = conj_get(form, path)
    elif branch == 1:  # perturbed sub
        path = rand_path(form)
        sub = perturb_formula(conj_get(form, path))
    elif branch == 2:  # off-tree path (extend past a non-∧ node)
        path = rand_path(form, allow_interior=False)
        f = conj_get(form, path)
        while f is not None and f[0] == "and":
            step = rng.randint(0, 1)
            path.append(step)
            f = f[1 + step]
        path.append(rng.randint(0, 1))  # one step past the leaf
        sub = rand_formula(1)
    else:  # unrelated sub
        path = rand_path(form)
        sub = rand_formula(2)
    got = conj_get(form, path)
    corpus["conjunct_at"].append(
        {"form": form, "path": path, "sub": sub, "verdict": got is not None and got == sub}
    )

for i in range(N):
    form = rand_and_tree(3)
    sub = rand_formula(2)
    branch = i % 4
    if branch == 0:  # true by construction
        path = rand_path(form)
        result = conj_replace(form, path, sub)
    elif branch == 1:  # perturbed result
        path = rand_path(form)
        result = perturb_formula(conj_replace(form, path, sub))
    elif branch == 2:  # off-tree path
        path = rand_path(form, allow_interior=False)
        f = conj_get(form, path)
        while f is not None and f[0] == "and":
            step = rng.randint(0, 1)
            path.append(step)
            f = f[1 + step]
        path.append(rng.randint(0, 1))
        result = rand_formula(2)
    else:  # unrelated result
        path = rand_path(form)
        result = rand_and_tree(2)
    expected = conj_replace(form, path, sub)
    corpus["conj_replace"].append(
        {
            "form": form,
            "path": path,
            "sub": sub,
            "result": result,
            "verdict": expected is not None and expected == result,
        }
    )

for i in range(N):
    form = rand_formula(3)
    w = rng.choice(WIRES)
    term = rand_term(2)
    branch = i % 3
    if branch == 0:  # true by construction
        result = subst_formula(form, w, term)
    elif branch == 1:  # perturbed result
        result = perturb_formula(subst_formula(form, w, term))
    else:  # substitution at the wrong wire
        result = subst_formula(form, (w + 1) % len(WIRES), term)
    corpus["subst"].append(
        {
            "form": form,
            "wire": w,
            "term": term,
            "result": result,
            "verdict": subst_formula(form, w, term) == result,
        }
    )

for i in range(N):
    pred = rand_formula(3, holes=True)
    arg = rand_term(2, holes=(i % 8 == 7))  # occasionally a hole in arg
    branch = i % 3
    if branch == 0:  # true by construction
        result = apply_pred(pred, arg)
    elif branch == 1:  # perturbed result
        result = perturb_formula(apply_pred(pred, arg))
    else:  # wrong argument applied
        result = apply_pred(pred, perturb_term(arg))
    corpus["apply_pred"].append(
        {
            "pred": pred,
            "arg": arg,
            "result": result,
            "verdict": apply_pred(pred, arg) == result,
        }
    )

for name, cases in corpus.items():
    holds = sum(c["verdict"] for c in cases)
    assert 10 < holds < N - 10, f"{name}: degenerate verdict split ({holds}/{N})"

print(json.dumps(corpus, indent=1))
