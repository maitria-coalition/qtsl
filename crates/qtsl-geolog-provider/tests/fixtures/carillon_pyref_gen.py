#!/usr/bin/env python3
"""Frozen cross-implementation corpus for the carillon family.

Independent python reference for the four R2-R5 evaluators
(qtsl_cell_cover, qtsl_dbar_closure, qtsl_gap_a, qtsl_floor_boxes):
Fraction arithmetic throughout, written against the frozen specs
(registry rows; carillon_discharge.py / manifest.py / compile.py), and
deliberately on DIFFERENT decision paths than the Rust evaluator where
the spec allows one:

- cell_cover decides coverage by cutting the region at the NAMED
  CELLS' box boundaries and testing every sub-cell for containment
  (the Rust side enumerates spanned grid indices and tests set
  membership);
- floor_boxes decides coverage by MEASURE accounting over the cut
  grid (sum of covered sub-cell volumes == vol(T); the Rust side
  tests per-sub-cell containment). With every part contained in T and
  the grid cut at all part endpoints, each open sub-cell is either
  fully covered or fully uncovered, so the two decisions coincide.

The python twins have no refusal channel, so the corpus carries
in-domain shapes only (matched arities, 1-D gap-A manifests, box
atoms, canonical ascending cell sets); the refusal classes are pinned
by the Rust battery.

Regenerate: python3 carillon_pyref_gen.py > carillon_pyref_corpus.json
(seeded; byte-stable across runs).
"""

import json
import random
from fractions import Fraction as F

random.seed(0x0536)  # deterministic corpus


# ----------------------------------------------------------------- util

def rat(lo=-4, hi=4, dens=(1, 1, 1, 2, 3, 4)):
    d = random.choice(dens)
    n = random.randint(lo * d, hi * d)
    return F(n, d)


def jq(x):
    x = F(x)
    return [x.numerator, x.denominator]


def jbox(box):
    return [[jq(lo), jq(hi)] for lo, hi in box]


def rand_interval(lo=-4, hi=4, nondeg=True):
    a, b = rat(lo, hi), rat(lo, hi)
    if a > b:
        a, b = b, a
    if nondeg and a == b:
        b = a + F(1, random.choice((1, 2, 3)))
    return (a, b)


def rand_box(n, lo=-4, hi=4):
    return [rand_interval(lo, hi) for _ in range(n)]


def sub_box(box):
    """A random sub-box of `box` (possibly touching the boundary)."""
    out = []
    for lo, hi in box:
        w = hi - lo
        a = lo + w * F(random.randint(0, 3), 6)
        b = hi - w * F(random.randint(0, 3), 6)
        if a > b:
            a, b = b, a
        out.append((a, b))
    return out


# ------------------------------------------------- R3: dbar closure

def closed_domain_hull(domain, images):
    box = list(domain)
    for img in images:
        assert len(img) == len(box), "corpus keeps arities matched"
        box = [(min(lo, ilo), max(hi, ihi))
               for (lo, hi), (ilo, ihi) in zip(box, img)]
    return box


def check_dbar(modes, transitions, mode_name, dbar):
    mode = next(m for m in modes if m["name"] == mode_name)
    images = [img for img in mode["jump_images"]]
    images += [t["reset_image"] for t in transitions
               if t["dst"] == mode_name]
    hull = closed_domain_hull(mode["domain"], images)
    return len(dbar) == len(hull) and all(
        c[0] == h[0] and c[1] == h[1] for c, h in zip(dbar, hull))


# ------------------------------------------------------ R4: gap-A

def image_contained(img, dom):
    """1-D containment with the stop set empty; inverted image =
    no landings = vacuous (the reference's sweep does the same)."""
    (ilo, ihi), = img
    (dlo, dhi), = dom
    if ihi < ilo:
        return True
    return dlo <= ilo and ihi <= dhi


def check_gap_a(modes, transitions):
    by_name = {m["name"]: m for m in modes}
    for m in modes:
        for img in m["jump_images"]:
            if not image_contained(img, m["domain"]):
                return False
    for t in transitions:
        dst = by_name[t["dst"]]  # corpus keeps references resolvable
        if not image_contained(t["reset_image"], dst["domain"]):
            return False
    return True


# ------------------------------------------------- R2: cell cover

def cell_boxes(dom, cuts, indices):
    """Named cell boxes from the FULL per-axis cut lists; None for an
    out-of-range index. Linearization: axis 0 fastest (pinned)."""
    full = [[dom[k][0]] + list(cuts[k]) + [dom[k][1]]
            for k in range(len(dom))]
    sizes = [len(f) - 1 for f in full]
    total = 1
    for s in sizes:
        total *= s
    out = []
    for idx in indices:
        if idx >= total:
            return None
        rem, coords = idx, []
        for s in sizes:
            coords.append(rem % s)
            rem //= s
        out.append([(full[k][c], full[k][c + 1])
                    for k, c in enumerate(coords)])
    return out


def covers(target, parts):
    """Closed-box coverage: cut `target` at part endpoints; every
    nondegenerate sub-cell must lie inside some part. Preconditions:
    target nondegenerate on every axis."""
    n = len(target)
    axes = []
    for k in range(n):
        lo, hi = target[k]
        pts = {lo, hi}
        for p in parts:
            for v in p[k]:
                if lo < v < hi:
                    pts.add(v)
        axes.append(sorted(pts))
    def rec(k, cell):
        if k == n:
            return any(all(p[j][0] <= cell[j][0] and cell[j][1] <= p[j][1]
                           for j in range(n)) for p in parts)
        return all(rec(k + 1, cell + [(axes[k][i], axes[k][i + 1])])
                   for i in range(len(axes[k]) - 1))
    return rec(0, [])


def check_cell_cover(dom, cuts, cells, region):
    # In-domain corpus: region nondegenerate, arity-matched, ascending
    # canonical cell sets.
    for k, (lo, hi) in enumerate(region):
        first, last = dom[k]
        if lo < first or last < hi:
            return False  # overhang: no cell can cover it
    boxes = cell_boxes(dom, cuts, cells)
    if boxes is None:
        return False  # out-of-range named index
    return covers(region, boxes)


# ----------------------------------------------- R5: floor boxes

def vol(box):
    v = F(1)
    for lo, hi in box:
        v *= hi - lo
    return v


def check_floor_boxes(cover, dbar, bx):
    assert len(bx) == len(dbar), "corpus keeps arities matched"
    n = len(dbar)
    target = [(max(bx[k][0], dbar[k][0]), min(bx[k][1], dbar[k][1]))
              for k in range(n)]
    if any(hi < lo for lo, hi in target):
        return len(cover) == 0
    # Containment (exactness's subset half) + no inverted parts.
    for p in cover:
        assert len(p) == n
        for k in range(n):
            if p[k][1] < p[k][0]:
                return False
            if p[k][0] < target[k][0] or target[k][1] < p[k][1]:
                return False
    nd = [k for k in range(n) if target[k][0] < target[k][1]]
    if not nd:
        return len(cover) > 0  # a point: any contained part IS it
    if not cover:
        return False
    # Measure accounting over the cut grid (projected to the
    # nondegenerate axes; degenerate axes are pinned by containment).
    axes = []
    for k in nd:
        lo, hi = target[k]
        pts = {lo, hi}
        for p in cover:
            for v in p[k]:
                if lo < v < hi:
                    pts.add(v)
        axes.append(sorted(pts))
    covered = F(0)
    def rec(j, cell):
        nonlocal covered
        if j == len(nd):
            if any(all(p[nd[i]][0] <= cell[i][0] and cell[i][1] <= p[nd[i]][1]
                       for i in range(len(nd))) for p in cover):
                covered += vol(cell)
            return
        for i in range(len(axes[j]) - 1):
            rec(j + 1, cell + [(axes[j][i], axes[j][i + 1])])
    rec(0, [])
    return covered == vol([(target[k][0], target[k][1]) for k in nd])


# ------------------------------------------------------- generation

cases = []


def add(kind, verdict, **payload):
    cases.append({"kind": kind, "verdict": bool(verdict), **payload})


def gen_manifest(n_axes, n_modes, n_jumps_max, n_trans, images_inside):
    """Random manifest; images inside destination domains when asked
    (a fresh sub-box), else unconstrained."""
    modes = []
    for i in range(n_modes):
        dom = rand_box(n_axes)
        jumps = []
        for _ in range(random.randint(0, n_jumps_max)):
            jumps.append(sub_box(dom) if images_inside else rand_box(n_axes))
        modes.append({"name": f"m{i}", "domain": dom, "jump_images": jumps})
    transitions = []
    for _ in range(n_trans):
        src = random.choice(modes)
        dst = random.choice(modes)
        img = sub_box(dst["domain"]) if images_inside else rand_box(n_axes)
        transitions.append({"src": src["name"], "dst": dst["name"],
                            "reset_image": img})
    return modes, transitions


def emit_manifest(modes, transitions):
    return {
        "modes": [{"name": m["name"], "domain": jbox(m["domain"]),
                   "jump_images": [jbox(b) for b in m["jump_images"]]}
                  for m in modes],
        "transitions": [{"src": t["src"], "dst": t["dst"],
                         "reset_image": jbox(t["reset_image"])}
                        for t in transitions],
    }


# R3 cases: exact hulls, perturbed hulls, stale (un-hulled) domains.
for _ in range(40):
    n_axes = random.choice((1, 1, 2, 3))
    modes, transitions = gen_manifest(
        n_axes, random.randint(1, 3), 2, random.randint(0, 3),
        images_inside=random.random() < 0.5)
    mode = random.choice(modes)["name"]
    target = next(m for m in modes if m["name"] == mode)
    images = list(target["jump_images"]) + [
        t["reset_image"] for t in transitions if t["dst"] == mode]
    hull = closed_domain_hull(target["domain"], images)
    roll = random.random()
    if roll < 0.45:
        dbar = hull  # exact: holds
    elif roll < 0.75:
        dbar = [list(iv) for iv in hull]
        k = random.randrange(n_axes)
        side = random.randrange(2)
        dbar[k][side] += F(random.choice((-1, 1)),
                           random.choice((7, 11, 1000000)))
        dbar = [tuple(iv) for iv in dbar]
    else:
        dbar = target["domain"]  # stale iff some image widened it
    v = check_dbar(modes, transitions, mode, dbar)
    add("dbar", v, **emit_manifest(modes, transitions),
        mode=mode, dbar=jbox(dbar))

# R4 cases: 1-D manifests, inside / boundary / escaping / empty images.
for _ in range(50):
    modes, transitions = gen_manifest(
        1, random.randint(1, 3), 2, random.randint(0, 3),
        images_inside=random.random() < 0.6)
    if random.random() < 0.2 and modes:
        # Force one boundary-exact landing (image == destination dom).
        m = random.choice(modes)
        m["jump_images"].append(list(m["domain"]))
    if random.random() < 0.15 and modes:
        # An inverted (empty) image: vacuously contained.
        m = random.choice(modes)
        lo, hi = m["domain"][0]
        m["jump_images"].append([(hi + 1, lo - 1)])
    v = check_gap_a(modes, transitions)
    add("gap_a", v, **emit_manifest(modes, transitions))

# R2 cases: random grids, regions, and cell sets.
for _ in range(60):
    n_axes = random.choice((1, 1, 2, 2, 3))
    dom = []
    cuts = []
    for _ in range(n_axes):
        lo = rat(-3, 1)
        hi = lo + F(random.randint(2, 6), 1)
        dom.append((lo, hi))
        k = random.randint(0, 3)
        interior = sorted(random.sample(
            [lo + (hi - lo) * F(i, 8) for i in range(1, 8)], k))
        cuts.append(interior)
    # A nondegenerate region inside dom (aligned or not).
    region = []
    for (lo, hi) in dom:
        a = lo + (hi - lo) * F(random.randint(0, 5), 8)
        b = lo + (hi - lo) * F(random.randint(random.randint(0, 5) + 1, 8), 8)
        if a >= b:
            a, b = lo, hi
        region.append((a, b))
    # The spanned set (generation-side; the verdict never uses it).
    full = [[dom[k][0]] + cuts[k] + [dom[k][1]] for k in range(n_axes)]
    sizes = [len(f) - 1 for f in full]
    spanned_axes = []
    for k in range(n_axes):
        rlo, rhi = region[k]
        spanned_axes.append([i for i in range(sizes[k])
                             if full[k][i] < rhi and rlo < full[k][i + 1]])
    spanned = [[]]
    for k in range(n_axes):
        spanned = [s + [c] for s in spanned for c in spanned_axes[k]]
    def lin(coords):
        idx = 0
        for k in reversed(range(n_axes)):
            idx = idx * sizes[k] + coords[k]
        return idx
    spanned_idx = sorted(lin(c) for c in spanned)
    total = 1
    for s in sizes:
        total *= s
    roll = random.random()
    if roll < 0.35:
        cells = spanned_idx  # exact: holds
    elif roll < 0.55 and spanned_idx:
        drop = random.randrange(len(spanned_idx))
        cells = spanned_idx[:drop] + spanned_idx[drop + 1:]  # hole
    elif roll < 0.75:
        extras = [i for i in range(total) if i not in spanned_idx]
        random.shuffle(extras)
        cells = sorted(spanned_idx + extras[:2])  # extras: still holds
    elif roll < 0.9:
        cells = sorted(set(spanned_idx[:-1] if spanned_idx else [])
                       | {total + random.randint(0, 3)})  # out of range
    else:
        cells = sorted(random.sample(range(total),
                                     random.randint(0, min(total, 4))))
    v = check_cell_cover(dom, cuts, cells, region)
    add("cell_cover", v, dom=jbox(dom),
        cuts=[[jq(c) for c in axis] for axis in cuts],
        cells=cells, region=jbox(region))

# R5 cases: exact tiles, tilings with holes, overhangs, empty targets.
def tiling(box, depth):
    """Recursive axis-aligned tiling of a closed box."""
    if depth == 0 or all(lo == hi for lo, hi in box):
        return [box]
    nd = [k for k in range(len(box)) if box[k][0] < box[k][1]]
    k = random.choice(nd)
    lo, hi = box[k]
    cut = lo + (hi - lo) * F(random.randint(1, 3), 4)
    a = [iv if j != k else (lo, cut) for j, iv in enumerate(box)]
    b = [iv if j != k else (cut, hi) for j, iv in enumerate(box)]
    return tiling(a, depth - 1) + tiling(b, depth - 1)


for _ in range(60):
    n_axes = random.choice((1, 1, 2, 2, 3))
    dbar = rand_box(n_axes)
    if random.random() < 0.7:
        bx = sub_box(dbar)  # nonempty intersection likely
    else:
        bx = rand_box(n_axes)
    target = [(max(bx[k][0], dbar[k][0]), min(bx[k][1], dbar[k][1]))
              for k in range(n_axes)]
    empty = any(hi < lo for lo, hi in target)
    roll = random.random()
    if empty:
        cover = [] if roll < 0.6 else [target]
    elif roll < 0.3:
        cover = [target]  # exact single box: holds
    elif roll < 0.55:
        cover = tiling(target, random.randint(1, 3))  # tiling: holds
    elif roll < 0.75:
        tiles = tiling(target, random.randint(1, 3))
        if len(tiles) > 1:
            tiles.pop(random.randrange(len(tiles)))  # hole
        cover = tiles
    elif roll < 0.9:
        # Shrink one tile strictly (a hole unless it was degenerate).
        tiles = tiling(target, random.randint(1, 2))
        t = random.randrange(len(tiles))
        tile = [list(iv) for iv in tiles[t]]
        nd = [k for k in range(n_axes) if tile[k][0] < tile[k][1]]
        if nd:
            k = random.choice(nd)
            tile[k][1] = tile[k][0] + (tile[k][1] - tile[k][0]) * F(1, 2)
        tiles[t] = [tuple(iv) for iv in tile]
        cover = tiles
    else:
        # An overhanging part: bx itself when it escapes the target.
        cover = [bx]
    v = check_floor_boxes(cover, dbar, bx)
    add("floor_boxes", v, cover=[jbox(p) for p in cover],
        dbar=jbox(dbar), bx=jbox(bx))

holds = sum(1 for c in cases if c["verdict"])
print(json.dumps(
    {"counts": {"total": len(cases), "holds": holds,
                "fails": len(cases) - holds},
     "cases": cases},
    indent=1))
