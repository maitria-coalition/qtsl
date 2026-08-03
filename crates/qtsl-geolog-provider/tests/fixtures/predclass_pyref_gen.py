#!/usr/bin/env python3
"""Frozen cross-implementation corpus generator for the predicate
semantic-class family (isConicPredicate / isConvexPredicate /
isUpwardClosedConicPredicate).

Independent arm: this file shares no code with the Rust evaluators and
takes a DIFFERENT decomposition to the same Props — where the Rust
transcribes the Lean's ordered two-arm match (hole side left, then the
flipped reading), this arm computes a symmetric PROFILE for each atom
side (hole-shaped / constant-valued / other) with Fraction arithmetic
and derives orientation and class from the profile pair. The two
decompositions agree everywhere because a hole-shaped side always
contains the hole and therefore never constant-folds — no side can
carry both profiles. Verdicts are DERIVED, never asserted.

Spec (Lean Core/Catalogue.lean):
  parseHoleSide: the hole, or a positive LITERAL scaling of it, one
                 mul deep, either operand order (strict 0 < a)
  evalQ?:        structural constant folding; none on any var/idx/hole
  classifyPredAtom: ge c -> (conic := c==0, upClosed := true)
                    le c -> (c==0, false)
                    eq 0 -> (true, false); eq c!=0 -> none
                    lt/gt/ne -> none; constant-left flips the bowtie
  classifyPred:  and-recursion, both bits combined with &&
  isConic    = class exists and conic
  isConvex   = class exists
  isUpClosed = class exists and conic and upClosed

The corpus deliberately pins the boundary rows: literal-vs-computed
coefficients, evalQ?-foldable vs var/idx-poisoned constant sides
(0 * w does NOT fold — the polynomial fold would accept it), both
orientations, zero/negative scalings, off-origin equalities, strict
rays, and mixed conjunction trees. No spec-hole formulas appear here
(they refuse, and this arm has no refusal channel — the hand battery
carries them).

Regenerate with: python3 predclass_pyref_gen.py > predclass_pyref_corpus.json
(then inspect the diff; disagreement in replay is stop-and-investigate,
never adjust-the-corpus).
"""

import json
import random
from fractions import Fraction

random.seed(0x54D4)

# ---------------------------------------------------------------------
# Terms/formulas: the JSON AST of the surgery/promise corpora.
# term    = [var w] | [const n d] | [add l r] | [mul l r] | [sub l r]
#         | [neg t] | [idx i t] | [hole]
# formula = [atom b l r] | [and l r] | [or l r] | [tt] | [ff]
# ---------------------------------------------------------------------

LT, LE, EQ, GE, GT, NE = range(6)


def evalq(t):
    """Term.evalQ? — structural folding, None on var/idx/hole."""
    tag = t[0]
    if tag == "const":
        return Fraction(t[1], t[2])
    if tag in ("var", "idx", "hole"):
        return None
    if tag == "neg":
        v = evalq(t[1])
        return None if v is None else -v
    l, r = evalq(t[1]), evalq(t[2])
    if l is None or r is None:
        return None
    if tag == "add":
        return l + r
    if tag == "sub":
        return l - r
    if tag == "mul":
        return l * r
    raise ValueError(tag)


def hole_shape(t):
    """parseHoleSide — the coefficient, or None outside the shape."""
    if t[0] == "hole":
        return Fraction(1)
    if t[0] == "mul":
        l, r = t[1], t[2]
        if l[0] == "const" and r[0] == "hole":
            a = Fraction(l[1], l[2])
        elif l[0] == "hole" and r[0] == "const":
            a = Fraction(r[1], r[2])
        else:
            return None
        return a if a > 0 else None
    return None


def profile(t):
    """The symmetric side profile (this arm's decomposition)."""
    a = hole_shape(t)
    if a is not None:
        return ("hole", a)
    v = evalq(t)
    if v is not None:
        return ("const", v)
    return ("other", None)


FLIP = {LT: GT, GT: LT, LE: GE, GE: LE, EQ: EQ, NE: NE}


def classify_atom(b, l, r):
    pl, pr = profile(l), profile(r)
    if pl[0] == "hole" and pr[0] == "const":
        ob, c = b, pr[1]
    elif pr[0] == "hole" and pl[0] == "const":
        ob, c = FLIP[b], pl[1]
    else:
        return None
    if ob == GE:
        return (c == 0, True)
    if ob == LE:
        return (c == 0, False)
    if ob == EQ:
        return (True, False) if c == 0 else None
    return None  # lt / gt / ne


def classify(f):
    """classifyPred: flatten the and-tree, classify every leaf."""
    leaves = []
    stack = [f]
    while stack:
        g = stack.pop()
        if g[0] == "and":
            stack.append(g[2])
            stack.append(g[1])
        else:
            leaves.append(g)
    conic, up = True, True
    for leaf in leaves:
        if leaf[0] != "atom":
            return None  # or / tt / ff: outside the fragment
        row = classify_atom(leaf[1], leaf[2], leaf[3])
        if row is None:
            return None
        conic = conic and row[0]
        up = up and row[1]
    return (conic, up)


def verdicts(f):
    cls = classify(f)
    return {
        "conic": cls is not None and cls[0],
        "convex": cls is not None,
        "upclosed": cls is not None and cls[0] and cls[1],
    }


# ---------------------------------------------------------------------
# Generation — boundary families plus a random sweep.
# ---------------------------------------------------------------------


def qconst(v):
    fr = Fraction(v)
    return ["const", fr.numerator, fr.denominator]


HOLE = ["hole"]


def scaled(a, order="left"):
    if order == "left":
        return ["mul", qconst(a), HOLE]
    return ["mul", HOLE, qconst(a)]


HOLE_SIDES = [
    HOLE,
    scaled(3),
    scaled(Fraction(2, 5)),
    scaled(7, "right"),
    scaled(0),                                   # zero scale: outside
    scaled(-2),                                  # negative: outside
    ["mul", ["add", qconst(1), qconst(1)], HOLE],  # computed: outside
    ["mul", ["neg", qconst(2)], HOLE],             # neg-literal: outside
    ["mul", qconst(2), ["mul", qconst(3), HOLE]],  # nested: outside
    ["idx", 1, HOLE],                              # idx: outside
]

CONST_SIDES = [
    qconst(0),
    qconst(5),
    qconst(-3),
    qconst(Fraction(1, 2)),
    ["sub", qconst(1), qconst(1)],               # folds to 0
    ["neg", qconst(0)],                          # folds to 0
    ["mul", qconst(2), qconst(3)],               # folds to 6
    ["sub", qconst(2), ["add", qconst(1), qconst(1)]],  # folds to 0
    ["mul", qconst(0), ["var", 7]],              # var-poisoned: no fold
    ["idx", 0, qconst(0)],                       # idx-poisoned: no fold
    ["var", 3],                                  # a real wire
    HOLE,                                        # a second hole
]


def gen_atom(rng):
    b = rng.randrange(6)
    hs = rng.choice(HOLE_SIDES)
    cs = rng.choice(CONST_SIDES)
    if rng.random() < 0.5:
        return ["atom", b, hs, cs]
    return ["atom", b, cs, hs]  # flipped orientation


# A pool of classifiable leaves for conjunction trees.
GOOD_LEAVES = [
    ["atom", GE, HOLE, qconst(0)],
    ["atom", LE, HOLE, qconst(0)],
    ["atom", EQ, HOLE, qconst(0)],
    ["atom", GE, scaled(3), qconst(0)],
    ["atom", GE, HOLE, qconst(5)],
    ["atom", LE, HOLE, qconst(-1)],
    ["atom", LE, qconst(0), HOLE],
    ["atom", GE, HOLE, ["sub", qconst(1), qconst(1)]],
]

BAD_LEAVES = [
    ["tt"],
    ["ff"],
    ["atom", GT, HOLE, qconst(0)],
    ["atom", NE, HOLE, qconst(0)],
    ["or", ["atom", GE, HOLE, qconst(0)], ["atom", LE, HOLE, qconst(0)]],
    ["atom", GE, ["var", 4], qconst(0)],
]


def gen_tree(rng, leaves):
    tree = rng.choice(leaves)
    for _ in range(rng.randrange(1, 4)):
        nxt = rng.choice(leaves)
        if rng.random() < 0.5:
            tree = ["and", tree, nxt]
        else:
            tree = ["and", nxt, tree]
    return tree


cases = []

# 1. The systematic atom sweep (every bowtie x both orientations over
#    boundary side-shapes; sampled from the full grid).
for b in range(6):
    for hs in HOLE_SIDES:
        for cs in (qconst(0), qconst(5), ["sub", qconst(1), qconst(1)],
                   ["mul", qconst(0), ["var", 7]]):
            cases.append(["atom", b, hs, cs])
            cases.append(["atom", b, cs, hs])

# 2. Random atoms over the wider side pools.
for _ in range(60):
    cases.append(gen_atom(random))

# 3. Conjunction trees: all-classifiable, and with one bad leaf mixed.
for _ in range(50):
    cases.append(gen_tree(random, GOOD_LEAVES))
for _ in range(25):
    tree = gen_tree(random, GOOD_LEAVES)
    cases.append(["and", tree, random.choice(BAD_LEAVES)])

# 4. Non-atom roots.
cases += [["tt"], ["ff"]]
for _ in range(8):
    cases.append(gen_tree(random, BAD_LEAVES))

out = {"cases": [dict(formula=f, **verdicts(f)) for f in cases]}
print(json.dumps(out, indent=1, sort_keys=False))
