#!/usr/bin/env python3
"""Frozen cross-implementation corpus generator for the promise
interface-confinement family (promiseContractConfined /
promiseWiresSeparated).

Independent arm: this file shares no code with the Rust evaluators and
takes a DIFFERENT route to the same Props — where the Rust walk
collects off-path sibling wires without ever materializing the
recomputed context, this arm literally BUILDS ctx =
conj_replace(consumer_pre, path, TT) as an AST and then takes its free
wires. Verdicts are DERIVED, never asserted.

Spec (Lean Core/Catalogue.lean):
  formulaWiresWithin f iface     := every free wire of f is in iface
  wiresSeparated left ctx post i := every free wire of left that is
                                    also free in ctx or post is in i
  ctx pinned by ctxReads: consumer.pre.conjReplace? path .tt = some ctx

Adjudication carried by the corpus (matches the module header): an
off-tree path (conjReplace? = none) makes promiseWiresSeparated
DECIDEDLY FALSE — including when the supplier premise is closed.

Regenerate with: python3 promise_pyref_gen.py > promise_pyref_corpus.json
(then inspect the diff; disagreement in replay is stop-and-investigate,
never adjust-the-corpus).
"""

import json
import random

random.seed(0x51F5)

# ---------------------------------------------------------------------
# Formula/Term ASTs — the surgery corpus's JSON schema (no InRegion in
# the corpus; the hand battery covers it).
# ---------------------------------------------------------------------


def free_term(t):
    tag = t[0]
    if tag == "var":
        return {t[1]}
    if tag == "const" or tag == "hole":
        return set()
    if tag in ("add", "mul", "sub"):
        return free_term(t[1]) | free_term(t[2])
    if tag == "neg":
        return free_term(t[1])
    if tag == "idx":
        return free_term(t[2])
    raise ValueError(tag)


def free_formula(f):
    tag = f[0]
    if tag == "atom":
        return free_term(f[2]) | free_term(f[3])
    if tag in ("and", "or"):
        return free_formula(f[1]) | free_formula(f[2])
    if tag in ("tt", "ff", "sph"):
        return set()
    raise ValueError(tag)


def conj_replace(f, path, g):
    """Formula.conjReplace? — None when the path walks off the ∧-tree."""
    if not path:
        return g
    step, rest = path[0], path[1:]
    if f[0] != "and":
        return None
    if step == 0:
        left = conj_replace(f[1], rest, g)
        return None if left is None else ["and", left, f[2]]
    right = conj_replace(f[2], rest, g)
    return None if right is None else ["and", f[1], right]


def contract_confined(contract, iface):
    return free_formula(contract) <= set(iface)


def wires_separated(sup_pre, cons_pre, path, post, iface):
    ctx = conj_replace(cons_pre, path, ["tt"])
    if ctx is None:
        return False
    shared = free_formula(ctx) | free_formula(post)
    iset = set(iface)
    return all(w in iset for w in free_formula(sup_pre) if w in shared)


# ---------------------------------------------------------------------
# Random material
# ---------------------------------------------------------------------


def rterm(depth, wires):
    if depth == 0 or random.random() < 0.4:
        r = random.random()
        if r < 0.55 and wires:
            return ["var", random.choice(wires)]
        if r < 0.9:
            return ["const", random.randint(-4, 4), random.choice([1, 2, 3])]
        return ["hole"]
    tag = random.choice(["add", "mul", "sub", "neg", "idx"])
    if tag == "neg":
        return ["neg", rterm(depth - 1, wires)]
    if tag == "idx":
        return ["idx", random.randint(0, 3), rterm(depth - 1, wires)]
    return [tag, rterm(depth - 1, wires), rterm(depth - 1, wires)]


def rformula(depth, wires):
    if depth == 0 or random.random() < 0.35:
        r = random.random()
        if r < 0.7:
            return ["atom", random.randint(0, 5), rterm(2, wires), rterm(2, wires)]
        return [random.choice(["tt", "ff", "sph"])]
    tag = random.choice(["and", "and", "or"])
    return [tag, rformula(depth - 1, wires), rformula(depth - 1, wires)]


def and_paths(f, prefix=()):
    """Every on-tree path (conjReplace?-valid), including non-∧ leaves'
    addresses and the root."""
    yield list(prefix)
    if f[0] == "and":
        yield from and_paths(f[1], prefix + (0,))
        yield from and_paths(f[2], prefix + (1,))


def rand_iface(pool):
    n = random.randint(0, len(pool))
    iface = random.sample(pool, n)
    # Occasionally repeat an entry: iface is a LIST (Lean List Wire);
    # duplicates are well-formed and must not change membership.
    if iface and random.random() < 0.15:
        iface.append(random.choice(iface))
    return iface


POOL = list(range(7))

# ---------------------------------------------------------------------
# contract_confined cases
# ---------------------------------------------------------------------

cc_cases = []
while len(cc_cases) < 110:
    contract = rformula(random.randint(0, 3), random.sample(POOL, random.randint(0, 4)))
    iface = rand_iface(POOL)
    # Bias toward decision-boundary cases: sometimes force the iface to
    # be exactly the free set, or the free set minus one.
    r = random.random()
    fw = sorted(free_formula(contract))
    if r < 0.25 and fw:
        iface = fw[:]
    elif r < 0.45 and fw:
        iface = fw[:-1]
    cc_cases.append(
        {
            "contract": contract,
            "iface": iface,
            "verdict": contract_confined(contract, iface),
        }
    )

# Hand-pinned edges.
cc_cases += [
    {"contract": ["tt"], "iface": [], "verdict": True},
    {"contract": ["atom", 1, ["hole"], ["const", 1, 1]], "iface": [], "verdict": True},
    {"contract": ["atom", 1, ["var", 0], ["var", 0]], "iface": [0], "verdict": True},
    {"contract": ["atom", 1, ["var", 0], ["var", 1]], "iface": [0], "verdict": False},
]

# ---------------------------------------------------------------------
# wires_separated cases
# ---------------------------------------------------------------------

ws_cases = []
while len(ws_cases) < 110:
    wires = random.sample(POOL, random.randint(1, 5))
    cons_pre = rformula(random.randint(1, 3), wires)
    sup_pre = rformula(random.randint(0, 2), random.sample(POOL, random.randint(0, 4)))
    post = rformula(random.randint(0, 2), random.sample(POOL, random.randint(0, 3)))
    iface = rand_iface(POOL)
    paths = list(and_paths(cons_pre))
    r = random.random()
    if r < 0.18:
        # Off-tree: extend a leaf path by steps the tree cannot honor.
        path = random.choice(paths) + [random.randint(0, 1), random.randint(0, 1), 0]
        if conj_replace(cons_pre, path, ["tt"]) is not None:
            continue  # accidentally on-tree (deep ∧ towers): resample
    else:
        path = random.choice(paths)
    ws_cases.append(
        {
            "sup_pre": sup_pre,
            "cons_pre": cons_pre,
            "path": path,
            "post": post,
            "iface": iface,
            "verdict": wires_separated(sup_pre, cons_pre, path, post, iface),
        }
    )

# Hand-pinned edges.
ws_cases += [
    # Here-path: ctx = TT wholesale — nothing shared through ctx.
    {
        "sup_pre": ["atom", 1, ["var", 0], ["const", 1, 1]],
        "cons_pre": ["atom", 1, ["var", 0], ["const", 2, 1]],
        "path": [],
        "post": ["tt"],
        "iface": [],
        "verdict": True,
    },
    # Off-tree with a CLOSED supplier premise: the presupposition pin —
    # no recomputed context exists, decidedly false even though the
    # wire condition would be vacuous.
    {
        "sup_pre": ["tt"],
        "cons_pre": ["atom", 1, ["var", 0], ["const", 1, 1]],
        "path": [0],
        "post": ["tt"],
        "iface": [],
        "verdict": False,
    },
    # Shared through the sibling, confined: holds.
    {
        "sup_pre": ["atom", 1, ["var", 2], ["const", 0, 1]],
        "cons_pre": ["and", ["atom", 2, ["var", 1], ["var", 2]], ["sph"]],
        "path": [1],
        "post": ["ff"],
        "iface": [2],
        "verdict": True,
    },
    # Shared through the sibling, NOT confined: fails.
    {
        "sup_pre": ["atom", 1, ["var", 2], ["const", 0, 1]],
        "cons_pre": ["and", ["atom", 2, ["var", 1], ["var", 2]], ["sph"]],
        "path": [1],
        "post": ["ff"],
        "iface": [1],
        "verdict": False,
    },
    # Shared only with the REPLACED slot (blanked): not shared — holds.
    {
        "sup_pre": ["atom", 1, ["var", 2], ["const", 0, 1]],
        "cons_pre": ["and", ["sph"], ["atom", 2, ["var", 2], ["const", 1, 1]]],
        "path": [1],
        "post": ["tt"],
        "iface": [],
        "verdict": True,
    },
    # Shared with the post only, not confined: fails.
    {
        "sup_pre": ["atom", 1, ["var", 3], ["const", 0, 1]],
        "cons_pre": ["and", ["sph"], ["tt"]],
        "path": [0],
        "post": ["atom", 4, ["var", 3], ["const", 0, 1]],
        "iface": [],
        "verdict": False,
    },
]

corpus = {"contract_confined": cc_cases, "wires_separated": ws_cases}

if __name__ == "__main__":
    import sys

    for name, cases in corpus.items():
        holds = sum(1 for c in cases if c["verdict"])
        print(
            f"{name}: {len(cases)} cases, {holds} hold / {len(cases) - holds} fail",
            file=sys.stderr,
        )
    json.dump(corpus, sys.stdout, indent=1)
    print()
