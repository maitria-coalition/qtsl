#!/usr/bin/env python3
"""Corpus generator for the cell-schema conclusion-form
cross-implementation battery (`cellStrictInteriorForm`,
`cellOneHotForm`, `cellOutWitnessForm`, `cellOutZeroForm`).

Expected formulas and verdicts are computed on python's `fractions`
module — an independent transcription of the spec's builds (a
different language and a different rational representation from the
row-native evaluator):

  baryLambdas1D: for a two-vertex mask {a < b} on a line complex,
    lambda_a(x) = V1/den + (-1/den)*x,  lambda_b(x) = -V0/den + (1/den)*x,
    den = V1 - V0 — the RAW coefficients, laid out
    TAdd(TConst(off), TMul(TConst(slp), TVar(input))); no rescale, no
    zero-offset special case.
  strict interior: per vertex in increasing order, one strict atom
    (< 0 for extended vertices, > 0 for core ones), the two conjoined.
  out-witness: ONE strict atom at the witness vertex (which must be in
    the cell's simplex mask — decided false otherwise), signs REVERSED.
  one-hot: (b_which = 1) AND chainAnd(b_j = 0, j != which, ascending);
    chainAnd([]) = FTrue, chainAnd([f]) = f, cons -> nested FAnd.
  out-zero: the single atom (b_which = 0).
  shared gate: which >= nCells, or output arity != nCells, decides
    false for every formula argument.

Verdicts are DERIVED (expected structure computed, then compared
against the case's formula spec), never asserted by fiat. All cases
stay inside the spec model's representable states; refusal behaviour
is battery territory. Deterministic: reseeded PRNG, frozen output.
Regenerate with `python3 cellform_pyref_gen.py >
cellform_pyref_corpus.json` only alongside a deliberate corpus
revision — replay disagreement is stop-and-investigate, never
adjust-the-corpus.
"""

import json
import random
from fractions import Fraction
from math import gcd

rng = random.Random(0xCE11F02)  # deterministic corpus


# --- the spec builds, on fractions ------------------------------------


def lams(coords, simplex_mask):
    """baryLambdas1D: [(vertex, off, slp)] in increasing vertex order,
    or None on the construction's none branches."""
    if len(simplex_mask) != 2:
        return None
    a, b = sorted(simplex_mask)
    v0, v1 = coords[a], coords[b]
    if v0 == v1:
        return None
    den = v1 - v0
    return [(a, v1 / den, Fraction(-1) / den), (b, -v0 / den, Fraction(1) / den)]


def strict_expected(coords, cells, which):
    """The strict-interior form's expected spec, or None (decided
    false for every formula)."""
    simplex, ext = cells[which]
    ls = lams(coords, simplex)
    if ls is None:
        return None
    atoms = []
    for vert, off, slp in ls:
        op = "lt" if vert in ext else "gt"
        atoms.append({"op": op, "off": off, "slp": slp})
    return {"type": "and2", "atoms": atoms}


def witness_expected(coords, cells, which, witness):
    simplex, ext = cells[which]
    if witness not in simplex:
        return None
    ls = lams(coords, simplex)
    if ls is None:
        return None
    for vert, off, slp in ls:
        if vert == witness:
            op = "gt" if vert in ext else "lt"  # REVERSED signs
            return {"type": "atom", "atom": {"op": op, "off": off, "slp": slp}}
    return None


def onehot_expected(m, which):
    atoms = [[which, 1]] + [[j, 0] for j in range(m) if j != which]
    return {"type": "chain", "atoms": atoms, "tail_true": m == 1}


def zero_expected(which):
    return {"type": "ind", "atom": [which, 0]}


def verdict(form, coords, cells, which, witness, n_outputs, formula):
    """The relation's verdict for a case, derived from the spec."""
    if which >= len(cells) or n_outputs != len(cells):
        return False  # the shared gate
    if form == "strict":
        exp = strict_expected(coords, cells, which)
    elif form == "witness":
        exp = witness_expected(coords, cells, which, witness)
    elif form == "onehot":
        exp = onehot_expected(len(cells), which)
    elif form == "zero":
        exp = zero_expected(which)
    else:
        raise AssertionError(form)
    return exp is not None and exp == formula


# --- JSON rendering ----------------------------------------------------


def frac_json(f):
    return [f.numerator, f.denominator]


def formula_json(spec):
    out = {"type": spec["type"]}
    if spec["type"] == "and2":
        out["atoms"] = [
            {"op": a["op"], "off": frac_json(a["off"]), "slp": frac_json(a["slp"])}
            for a in spec["atoms"]
        ]
    elif spec["type"] == "atom":
        a = spec["atom"]
        out["atom"] = {"op": a["op"], "off": frac_json(a["off"]), "slp": frac_json(a["slp"])}
    elif spec["type"] == "chain":
        out["atoms"] = spec["atoms"]
        out["tail_true"] = spec["tail_true"]
    elif spec["type"] == "ind":
        out["atom"] = spec["atom"]
    return out


def case_json(kind, form, coords, cells, which, witness, n_outputs, formula, v):
    return {
        "kind": kind,
        "form": form,
        "coords": [frac_json(c) for c in coords],
        "cells": [
            {"simplex": sorted(s), "ext": sorted(e)} for (s, e) in cells
        ],
        "which": which,
        "witness": witness,
        "n_outputs": n_outputs,
        "formula": formula_json(formula),
        "verdict": v,
    }


# --- random geometry ---------------------------------------------------

COORD_POOL = sorted(
    set(
        Fraction(n, d)
        for d in (1, 2, 3, 4)
        for n in range(-6, 7)
        if gcd(abs(n), d) == 1 or n == 0
    )
)


def rand_schema():
    """A line complex with 1..4 two-vertex cells over 2..5 distinct
    vertices; each cell a two-vertex simplex mask with a proper
    extension subset."""
    n = rng.randint(2, 5)
    coords = rng.sample(COORD_POOL, n)
    m = rng.randint(1, min(4, n * (n - 1) // 2))
    cells = []
    for _ in range(m):
        a, b = sorted(rng.sample(range(n), 2))
        ext = set(rng.choice([[], [a], [b]]))  # proper subsets only
        cells.append(({a, b}, ext))
    return coords, cells


cases = []


def emit(kind, form, coords, cells, which, witness, n_outputs, formula):
    v = verdict(form, coords, cells, which, witness, n_outputs, formula)
    cases.append(
        case_json(kind, form, coords, cells, which, witness, n_outputs, formula, v)
    )
    return v


# --- holds: the true rendering replays to Holds ------------------------

for i in range(80):
    coords, cells = rand_schema()
    m = len(cells)
    which = rng.randrange(m)
    form = ["strict", "onehot", "witness", "zero"][i % 4]
    witness = None
    if form == "strict":
        exp = strict_expected(coords, cells, which)
    elif form == "onehot":
        exp = onehot_expected(m, which)
    elif form == "witness":
        witness = rng.choice(sorted(cells[which][0]))
        exp = witness_expected(coords, cells, which, witness)
    else:
        exp = zero_expected(which)
    assert exp is not None, "representable geometry guarantees a build"
    assert emit("holds", form, coords, cells, which, witness, m, exp) is True


# --- mutants: one perturbation each, expected verdict False ------------


def perturb_affine(atom, how):
    out = dict(atom)
    if how == "const_shift":
        out["off"] = atom["off"] + 1
    elif how == "prim_rescale":
        # The halfspace form's canonicalization — the spec-grain
        # mutant: the same halfspace, positively rescaled to coprime
        # integers, which the RAW-coefficient build must reject
        # whenever it differs.
        s, c = atom["slp"], atom["off"]
        if c == 0:
            out["slp"] = Fraction(1 if s > 0 else (-1 if s < 0 else 0))
        else:
            big_l = (s.denominator * c.denominator) // gcd(s.denominator, c.denominator)
            g = gcd(
                abs(s.numerator * (big_l // s.denominator)),
                abs(c.numerator * (big_l // c.denominator)),
            )
            k = Fraction(big_l, g)
            out["slp"], out["off"] = k * s, k * c
    elif how == "flip_op":
        out["op"] = "lt" if atom["op"] == "gt" else "gt"
    elif how == "slope_shift":
        out["slp"] = atom["slp"] + 1
    return out


mutant_count = 0
attempts = 0
while mutant_count < 80 and attempts < 4000:
    attempts += 1
    coords, cells = rand_schema()
    m = len(cells)
    which = rng.randrange(m)
    form = ["strict", "onehot", "witness", "zero"][mutant_count % 4]
    witness = None
    if form == "strict":
        exp = strict_expected(coords, cells, which)
        how = ["const_shift", "prim_rescale", "flip_op", "slope_shift", "swap_arms"][
            mutant_count // 4 % 5
        ]
        if how == "swap_arms":
            mut = {"type": "and2", "atoms": [exp["atoms"][1], exp["atoms"][0]]}
        else:
            idx = mutant_count % 2
            atoms = list(exp["atoms"])
            atoms[idx] = perturb_affine(atoms[idx], how)
            mut = {"type": "and2", "atoms": atoms}
        if mut == exp:
            continue  # the perturbation happened to be identity — reroll
        kind = f"mutant_strict_{how}"
    elif form == "onehot":
        exp = onehot_expected(m, which)
        hows = ["wrong_k", "swap_values", "drop_other", "tail_true_wrong", "order"]
        how = hows[mutant_count // 4 % 5]
        if how == "wrong_k" and m >= 2:
            mut = onehot_expected(m, (which + 1) % m)
        elif how == "swap_values":
            atoms = [[w, 1 - v] for w, v in exp["atoms"]]
            mut = {"type": "chain", "atoms": atoms, "tail_true": exp["tail_true"]}
        elif how == "drop_other" and m >= 2:
            mut = {
                "type": "chain",
                "atoms": exp["atoms"][:-1],
                "tail_true": m == 2,
            }
        elif how == "tail_true_wrong" and m >= 2:
            mut = {"type": "chain", "atoms": exp["atoms"], "tail_true": True}
        elif how == "order" and m >= 3:
            atoms = list(exp["atoms"])
            atoms[1], atoms[2] = atoms[2], atoms[1]
            mut = {"type": "chain", "atoms": atoms, "tail_true": False}
        else:
            continue
        if mut == exp:
            continue
        kind = f"mutant_onehot_{how}"
    elif form == "witness":
        witness = rng.choice(sorted(cells[which][0]))
        exp = witness_expected(coords, cells, which, witness)
        how = ["flip_op", "const_shift", "prim_rescale", "other_vertex"][
            mutant_count // 4 % 4
        ]
        if how == "other_vertex":
            # The OTHER mask vertex's lambda, correct signs for it —
            # still the wrong atom for this witness.
            other = [v for v in sorted(cells[which][0]) if v != witness][0]
            mut = witness_expected(coords, cells, which, other)
        else:
            mut = {"type": "atom", "atom": perturb_affine(exp["atom"], how)}
        if mut == exp or mut is None:
            continue
        kind = f"mutant_witness_{how}"
    else:
        exp = zero_expected(which)
        how = ["value_one", "wrong_wire"][mutant_count // 4 % 2]
        if how == "value_one":
            mut = {"type": "ind", "atom": [which, 1]}
        elif m >= 2:
            mut = {"type": "ind", "atom": [(which + 1) % m, 0]}
        else:
            continue
        if mut == exp:
            continue
        kind = f"mutant_zero_{how}"
    assert emit(kind, form, coords, cells, which, witness, m, mut) is False
    mutant_count += 1

assert mutant_count == 80, f"mutant corpus incomplete: {mutant_count}"


# --- gate cases: out-of-range index / arity mismatch, decided False ----

for i in range(16):
    coords, cells = rand_schema()
    m = len(cells)
    form = ["strict", "onehot", "witness", "zero"][i % 4]
    if i % 2 == 0:
        which, n_outputs, kind = m, m, f"gate_range_{form}"  # which == nCells
    else:
        which, n_outputs, kind = 0, m + 1, f"gate_arity_{form}"
    witness = sorted(cells[0][0])[0] if form == "witness" else None
    # A well-shaped formula for SOME reading — the gate must decide
    # false regardless of content.
    if form == "strict":
        formula = strict_expected(coords, cells, 0)
    elif form == "onehot":
        formula = onehot_expected(m, 0)
    elif form == "witness":
        formula = witness_expected(coords, cells, 0, witness)
    else:
        formula = zero_expected(0)
    assert emit(kind, form, coords, cells, which, witness, n_outputs, formula) is False


# --- none branches: cell masks of the wrong size, decided False --------

for i in range(12):
    coords, _ = rand_schema()
    n = len(coords)
    k = 1 if i % 2 == 0 else min(3, n)
    if k == 3 and n < 3:
        k = 1
    bad_cell = (set(rng.sample(range(n), k)), set())
    cells = [bad_cell]
    form = ["strict", "witness"][i % 2]
    witness = sorted(bad_cell[0])[0] if form == "witness" else None
    formula = {
        "type": "and2",
        "atoms": [
            {"op": "gt", "off": Fraction(2), "slp": Fraction(-1)},
            {"op": "gt", "off": Fraction(-1), "slp": Fraction(1)},
        ],
    }
    if form == "witness":
        formula = {"type": "atom", "atom": {"op": "lt", "off": Fraction(2), "slp": Fraction(-1)}}
    assert emit(f"none_mask_{k}_{form}", form, coords, cells, 0, witness, 1, formula) is False


print(json.dumps({"cases": cases}, indent=1))
