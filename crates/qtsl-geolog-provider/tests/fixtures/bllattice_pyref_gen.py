#!/usr/bin/env python3
"""Frozen cross-implementation corpus for the block-lattice family.

Independent reference implementation of the two geometric recomputes
the Rust evaluators own:

  * the canonical boundary-facet enumeration of a block over a
    row-major grid with axis 0 slowest — facets (cell, axis,
    direction) whose neighbouring cell lies inside the grid but
    outside the block, sorted by (cell, axis, lower before upper);
  * the product construction — composite axes are left's then
    right's; composite stored blocks are the extended pairwise
    products {b1 x b2 : b1 in left + [arena], b2 in right + [arena]}
    minus the implicit top, enumerated lexicographically with stored
    blocks first and each factor's arena last, a product block's
    cells being {i1 * N2 + i2}.

This file is written fresh from the format prose (deliberately NOT
ported from the Rust): the value of the corpus is that two
implementations of the same frozen text agree. The Rust test
(`tests/bllattice.rs`) replays the JSON: it emits certificate rows
whose declared facet counts and composite blocks come from THIS
file's computation, and the evaluator's own recompute either agrees
(verdict holds) or the corpus catches the divergence.

Numbers for the product case named `kw_ex_coproduct_flow` are the
Kalies-Wehbe worked witness (two one-dimensional flows, gridline cuts
at 1/4 and 1/3) — the same instance the family format's fixture
producer and its reference checker were built around.

Run:  python3 bllattice_pyref_gen.py   (rewrites bllattice_pyref_corpus.json)
"""

import itertools
import json
import os


# ---------------------------------------------------------------------------
# geometry (independent implementation)
# ---------------------------------------------------------------------------

def coords_of(counts, cell):
    out = [0] * len(counts)
    rem = cell
    for i in reversed(range(len(counts))):
        out[i] = rem % counts[i]
        rem //= counts[i]
    return out


def index_of(counts, coords):
    idx = 0
    for n, c in zip(counts, coords):
        idx = idx * n + c
    return idx


def facets_of(counts, cells):
    cellset = set(cells)
    out = []
    for cell in sorted(cells):
        coords = coords_of(counts, cell)
        for axis in range(len(counts)):
            for upper in (False, True):
                c = coords[axis]
                if upper:
                    if c + 1 >= counts[axis]:
                        continue  # grid-boundary face
                    ncoords = coords[:axis] + [c + 1] + coords[axis + 1:]
                else:
                    if c == 0:
                        continue
                    ncoords = coords[:axis] + [c - 1] + coords[axis + 1:]
                if index_of(counts, ncoords) not in cellset:
                    out.append([cell, axis, upper])
    return out


def counts_of(gridlines):
    return [len(g) - 1 for g in gridlines]


def product_blocks(left, right):
    """Composite stored-block cell lists in the pinned enumeration."""
    nl_cells = 1
    for n in counts_of(left["gridlines"]):
        nl_cells *= n
    nr_cells = 1
    for n in counts_of(right["gridlines"]):
        nr_cells *= n
    left_ext = [sorted(b) for b in left["blocks"]] + [list(range(nl_cells))]
    right_ext = [sorted(b) for b in right["blocks"]] + [list(range(nr_cells))]
    out = []
    for i1, c1 in enumerate(left_ext):
        for i2, c2 in enumerate(right_ext):
            if i1 == len(left_ext) - 1 and i2 == len(right_ext) - 1:
                continue  # the implicit top is never stored
            out.append([a * nr_cells + b
                        for a, b in itertools.product(c1, c2)])
    return out


def lattice_entry(spec):
    counts = counts_of(spec["gridlines"])
    return {
        "gridlines": spec["gridlines"],
        "blocks": [sorted(b) for b in spec["blocks"]],
        "facets": [facets_of(counts, b) for b in spec["blocks"]],
    }


def product_entry(name, left, right):
    comp = {
        "gridlines": left["gridlines"] + right["gridlines"],
        "blocks": product_blocks(left, right),
    }
    return {
        "name": name,
        "left": lattice_entry(left),
        "right": lattice_entry(right),
        "composite": lattice_entry(comp),
    }


def q(n, d=1):
    return [n, d]


# ---------------------------------------------------------------------------
# cases
# ---------------------------------------------------------------------------

WF_SPECS = [
    ("one_d_upper_cell", {
        "gridlines": [[q(0), q(1, 4), q(1)]],
        "blocks": [[1]],
    }),
    ("one_d_disconnected", {
        "gridlines": [[q(0), q(1), q(2), q(3)]],
        "blocks": [[0, 2]],
    }),
    ("two_d_corner", {
        "gridlines": [[q(0), q(1), q(2)], [q(0), q(1), q(2)]],
        "blocks": [[3]],
    }),
    ("two_d_l_shape", {
        "gridlines": [[q(0), q(1), q(2), q(3)], [q(-1), q(0), q(1), q(2)]],
        "blocks": [[0, 3, 4]],
    }),
    ("two_d_ring", {
        "gridlines": [[q(0), q(1), q(2), q(3)], [q(0), q(1), q(2), q(3)]],
        "blocks": [[0, 1, 2, 3, 5, 6, 7, 8]],
    }),
    ("two_d_two_blocks", {
        "gridlines": [[q(0), q(1, 2), q(1)], [q(0), q(1, 3), q(2, 3), q(1)]],
        "blocks": [[1, 2], [4]],
    }),
    ("three_d_corner", {
        "gridlines": [[q(0), q(1), q(2)], [q(0), q(1), q(2)],
                      [q(0), q(1), q(2)]],
        "blocks": [[7]],
    }),
]

PRODUCT_SPECS = [
    ("kw_ex_coproduct_flow",
     {"gridlines": [[q(0), q(1, 4), q(1)]], "blocks": [[1]]},
     {"gridlines": [[q(0), q(1, 3), q(1)]], "blocks": [[1]]}),
    ("one_d_lower_times_middle",
     {"gridlines": [[q(0), q(1), q(2)]], "blocks": [[0]]},
     {"gridlines": [[q(-1), q(0), q(1), q(2)]], "blocks": [[1]]}),
    ("two_d_corner_times_one_d",
     {"gridlines": [[q(0), q(1), q(2)], [q(0), q(1), q(2)]],
      "blocks": [[3]]},
     {"gridlines": [[q(0), q(1, 2), q(1)]], "blocks": [[1]]}),
]


def main():
    # Spot receipts against hand enumeration (documented in the Rust
    # module's unit tests as well — two implementations, one text).
    assert facets_of([2], [1]) == [[1, 0, False]]
    assert facets_of([2, 2], [3]) == [[3, 0, False], [3, 1, False]]
    assert facets_of([3, 3], [0, 3, 4]) == [
        [0, 1, True], [3, 0, True],
        [4, 0, False], [4, 0, True], [4, 1, True],
    ]
    kw = product_blocks(
        {"gridlines": [[q(0), q(1, 4), q(1)]], "blocks": [[1]]},
        {"gridlines": [[q(0), q(1, 3), q(1)]], "blocks": [[1]]},
    )
    assert kw == [[3], [2, 3], [1, 3]], kw

    corpus = {
        "wf": [dict(lattice_entry(spec), name=name)
               for name, spec in WF_SPECS],
        "product": [product_entry(name, left, right)
                    for name, left, right in PRODUCT_SPECS],
    }
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "bllattice_pyref_corpus.json")
    with open(path, "w") as fh:
        json.dump(corpus, fh, indent=1, sort_keys=True)
        fh.write("\n")
    n_facets = sum(len(f) for e in corpus["wf"] for f in e["facets"])
    print(f"wrote {path}: {len(corpus['wf'])} wf cases "
          f"({n_facets} facets), {len(corpus['product'])} product cases")


if __name__ == "__main__":
    main()
