#!/usr/bin/env python3
r"""cores -- graded-box specification cores and the constructive tier.

Staggering-forcers need GRADED BOXES: box-facts over formulas
containing A-subformulas, of the shape box ~(AF<=1[p] & AF<=1[q]) --
constraints an atom-row grammar cannot express.  This module defines
graded-box specimens (GSpec: the gnand cores of the companion
chapter, plus escape/lock extensions beyond the fragment) and a
branch-at-seed model builder, probing TWO things mechanically:

  1. WHERE LAZY SCHEDULES MUST STAGGER: the builder gains branched
     staggered placement (the JD witness's shape -- services more
     than a unit apart, opposite orders on distinct branches, is the
     seed pattern, generalized to rotation schedules over the
     gnand-constrained atoms);
  2. WHERE ~box[nu] ESCAPE WITNESSES CAN AND CANNOT SIT relative to
     the demand tree (the ESC question, empirically): escape
     obligations place a nu-violating state at an obligation-
     respecting position; LOCK facts AF<=T[box[nu]] pin the witness
     inside the first T units (attack-map step (ii) made semantic).

Grammar (tiny, per the seed): boxes over Boolean combinations of
atoms and stage formulas --

  gnand (x, d1, y, d2):  box ~(AF<=d1[x] & AF<=d2[y])   [staggering]
  xnand (x, y, d):       box ~(x & AF<=d[y])            [separation]

plus the Spec ingredients (pend/rows/disj/avoid), per-base EXACTNESS
(seed ~AF<=(s-1)[x], the JD ingredient), and ESCAPES:

  Esc(pos, neg, spos, sneg, lock): seed fact ~box[nu] where
  nu := ~(pattern),  pattern := /\pos & /\~neg & /\ AF<=d[y] (spos)
                                & /\ ~AF<=d[y] (sneg);
  lock=T adds the seed fact AF<=T[box[nu]] -- "the pattern-era ends
  by T on every trajectory" -- which pins the witness before T.

THE STAGGERING ALGEBRA (what the solver enforces; all exact, NSQ):
A<=d[x] holds at a point tau iff some x-point lies in [tau, tau+d];
so x's DUE-REGION is the union of [t - d, t + dwell) over x-points t.
gnand (x,d1,y,d2) holds on a branch iff the d1-region of x and the
d2-region of y are disjoint, iff for every pair of instances either
t_x < t_y - d2 (x earlier, gap > d2) or t_y < t_x - d1.  A service
instance's own state satisfies A<=d[self] reflexively (x true now),
which is why same-instant service of a gnand pair is always a
violation and the JD box forces genuine staggering.  Branch duty is
by branch duty: EVERY branch serves all positive obligations
(graded facts quantify over all trajectories); seed negatives
(exactness, avoid) are MAX-over-branches facts and ride one
designated branch each; escapes ride their own spawned branch when no
existing state hosts the pattern.  Pre-branch box safety is implied
by post-branch staggering (at any pre-branch point where both
A-facts held, the earlier service instant of any branch would
witness a post-branch violation).

The three-way refusal classifier:
  REFUSED-SCREENED   -- a deduction-backed screen pattern names the
                        inconsistency (basis derives bottom);
  REFUSED-SEMANTIC   -- a per-trajectory infeasibility certificate
                        fires: sound for BRANCH-AT-SEED models (the
                        builder's class, where post-seed states are
                        linear), NOT a clocked-unsatisfiability
                        verdict -- deep-branching MASKED models can
                        satisfy such specimens (masked.py:
                        pigeon-3's 57-state witness).  Per-specimen
                        clocked-SAT status is open unless a masked
                        witness or a sound refutation settles it;
  REFUSED-ALARM      -- neither: builder limitation or missing law,
                        loud, exit 1.

Checks (battery = all, exit-coded):
  roster  -- curated GSpecs incl. the staggering-forcer rebuilt
             mechanically (its witness was first hand-built), controls,
             the pigeonhole clique, escape/lock/window specimens,
             and screen-liveness controls
  random  -- pre-screened random GSpecs; unscreened-unexplained
             refusal is the alarm; per-specimen probe data (branches
             used, escape positions) aggregated as the ESC ledger

Python as orchestration-class code: exact arithmetic, tiny spaces.
"""

from __future__ import annotations

import argparse
import random
import sys
from dataclasses import dataclass, field
from fractions import Fraction

from oracle import atom, f_not, f_and, f_or, pg, impl, DEAD
from timed import INF, TModel, tstructure, tdenot, pfle
from nstime import NSQ, EPS, is_ceps, subst_model, std_part

ZERO = Fraction(0)
ONE = Fraction(1)
SHADOW_DELTAS = (Fraction(1, 64), Fraction(1, 512))
E2 = EPS + EPS


# ---------------------------------------------------------------------------
# GSpec

@dataclass(frozen=True)
class Esc:
    pos: tuple = ()          # atoms true at the witness state
    neg: tuple = ()          # atoms false at the witness state
    spos: tuple = ()         # ((y, d), ...): AF<=d[y] true at witness
    sneg: tuple = ()         # ((y, d), ...): ~AF<=d[y] at witness
    lock: object = None      # None or integer T: AF<=T[box[nu]] seed fact


@dataclass(frozen=True)
class GSpec:
    name: str
    atoms: tuple
    pend: tuple = ()         # ((x, s), ...)
    exact: tuple = ()        # atoms with seed ~AF<=(s-1)[x]; s >= 2
    rows: tuple = ()         # ((x, y, d), ...)
    disj: tuple = ()         # ((x, y), ...)
    avoid: tuple = ()        # ((z, h), ...)
    gnand: tuple = ()        # ((x, d1, y, d2), ...)
    xnand: tuple = ()        # ((x, y, d), ...)
    esc: tuple = ()          # (Esc, ...)


def esc_pattern(e: Esc):
    """The pattern conjunction (the ~nu the witness state realizes)."""
    g = None

    def add(c):
        nonlocal g
        g = c if g is None else f_and(g, c)

    for x in e.pos:
        add(atom(x))
    for x in e.neg:
        add(f_not(atom(x)))
    for y, d in e.spos:
        add(pfle(Fraction(d), atom(y)))
    for y, d in e.sneg:
        add(f_not(pfle(Fraction(d), atom(y))))
    if g is None:
        raise ValueError('empty escape pattern')
    return g


def gspec_formula(gs: GSpec):
    """The full seed formula, evaluator-checkable: positives +
    exactness + avoid + box(rows, disj, gnand, xnand) + escapes +
    locks + liveness."""
    g = f_not(DEAD)

    def add(c):
        nonlocal g
        g = f_and(g, c)

    stages = dict(gs.pend)
    for x, s in gs.pend:
        add(f_and(f_not(atom(x)), pfle(Fraction(s), atom(x))))
    for x in gs.exact:
        add(f_not(pfle(Fraction(stages[x] - 1), atom(x))))
    for z, h in gs.avoid:
        add(f_not(pfle(Fraction(h), atom(z))))
    box = None

    def badd(c):
        nonlocal box
        box = c if box is None else f_and(box, c)

    for x, y, d in gs.rows:
        badd(impl(atom(x), pfle(Fraction(d), atom(y))))
    for x, y in gs.disj:
        badd(f_not(f_and(atom(x), atom(y))))
    for x, d1, y, d2 in gs.gnand:
        badd(f_not(f_and(pfle(Fraction(d1), atom(x)),
                         pfle(Fraction(d2), atom(y)))))
    for x, y, d in gs.xnand:
        badd(f_not(f_and(atom(x), pfle(Fraction(d), atom(y)))))
    if box is not None:
        add(pg(box))
    for e in gs.esc:
        nu = f_not(esc_pattern(e))
        add(f_not(pg(nu)))                       # ~box[nu]: witness exists
        if e.lock is not None:
            add(pfle(Fraction(e.lock), pg(nu)))  # AF<=T[box[nu]]: the pin
    return g


# ---------------------------------------------------------------------------
# the screen (deduction-backed patterns) and the semantic certifier

def _eff(gs: GSpec):
    """Least derivable service deadline per atom (obligation
    propagation: pend stages + row chains; graded-K + U7 on the
    deductive side).  None = never forced."""
    import heapq
    dist = {x: Fraction(s) for x, s in gs.pend}
    pq = [(d, x) for x, d in dist.items()]
    heapq.heapify(pq)
    rows_from: dict = {}
    for x, y, d in gs.rows:
        rows_from.setdefault(x, []).append((y, Fraction(d)))
    done = set()
    while pq:
        t, x = heapq.heappop(pq)
        if x in done:
            continue
        done.add(x)
        for y, d in rows_from.get(x, []):
            nt = t + d
            if y not in dist or nt < dist[y]:
                dist[y] = nt
                heapq.heappush(pq, (nt, y))
    return dist


def screen(gs: GSpec):
    """Deduction-backed inconsistency patterns.  Returns None or a
    reason string; every pattern cites its derivation engine (all
    from the banked basis -- sketches in the development record)."""
    eff = _eff(gs)
    stages = dict(gs.pend)
    # AV: avoid vs forced deadline (base tier; D1 + reach-interaction)
    for z, h in gs.avoid:
        if z in eff and eff[z] <= h:
            return (f'AV: atom {z} derivably forced by {eff[z]} <= '
                    f'avoid horizon {h}')
    # GB-REFL: gnand pair both forced within their windows at the seed
    # (D1-weaken A<=eff to A<=d, quasi-reflexivity G4 under liveness)
    for x, d1, y, d2 in gs.gnand:
        if x in eff and y in eff and eff[x] <= d1 and eff[y] <= d2:
            return (f'GB-REFL: gnand({x},{d1},{y},{d2}) with both '
                    f'forced at seed (eff {eff[x]}, {eff[y]})')
    # XN-REFL: xnand (x,y,d) where a row x->y within d' <= d exists
    # and x is forced: at x's service, y due within d' <= d (row) and
    # x true (refl) -- box violated pointwise, derivably (U4-current
    # + row-MP + D1)
    for x, y, d in gs.xnand:
        if x not in eff:
            continue
        for rx, ry, rd in gs.rows:
            if rx == x and ry == y and rd <= d:
                return (f'XN-REFL: xnand({x},{y},{d}) with row '
                        f'{x}->{y} within {rd} <= {d} and {x} forced')
    # GB-ROW-REFL: gnand (x,d1,y,d2) with a row x->y within r <= d2
    # (or y->x within r <= d1) and the row source forced: at the
    # source's service cell, source true (U4-current) gives its own
    # A-fact reflexively, the row gives the target within r,
    # D1-weakened into the box's window -- the forbidden conjunction
    # holds pointwise, so box + quasi-reflexivity (G4) + liveness
    # derive bottom.  (sweep-specimen class grand39/13/160/167)
    for x, d1, y, d2 in gs.gnand:
        for rx, ry, rd in gs.rows:
            if rx == x and ry == y and rd <= d2 and x in eff:
                return (f'GB-ROW-REFL: gnand({x},{d1},{y},{d2}) with '
                        f'row {x}->{y} within {rd} <= {d2}, {x} '
                        f'forced')
            if rx == y and ry == x and rd <= d1 and y in eff:
                return (f'GB-ROW-REFL: gnand({x},{d1},{y},{d2}) with '
                        f'row {y}->{x} within {rd} <= {d1}, {y} '
                        f'forced')
    # ESC-CONTRA: escape pattern derivably box-refuted, via the
    # FORCED-STAGE CLOSURE at the witness point.  Everything a
    # pattern-point forces pointwise: pos atoms are due-now (refl);
    # spos conjuncts are due within d; and row chains compose
    # (row-MP at the reached point + U7 window addition) -- Dijkstra
    # from those seeds.  Any box conjunct refuted by the closure
    # refutes the pattern pointwise (D1 + box + G4-liveness), so
    # box[nu] is derivable and the escape fact ~box[nu] is
    # inconsistent.  (Unifies the grand25/117/596/334 sweep catches;
    # every step is pointwise-derivable -- screen tier.)
    import heapq
    for e in gs.esc:
        pos = set(e.pos)
        for x, y in gs.disj:
            if x in pos and y in pos:
                return (f'ESC-CONTRA: escape pos contains disjoint '
                        f'pair ({x},{y})')
        F = {x: Fraction(0) for x in pos}
        for y, d in e.spos:
            dd = Fraction(d)
            if y not in F or dd < F[y]:
                F[y] = dd
        pq = [(d, y) for y, d in F.items()]
        heapq.heapify(pq)
        done = set()
        while pq:
            t, x = heapq.heappop(pq)
            if x in done:
                continue
            done.add(x)
            for rx, ry, rd in gs.rows:
                if rx != x:
                    continue
                nt = t + Fraction(rd)
                if ry not in F or nt < F[ry]:
                    F[ry] = nt
                    heapq.heappush(pq, (nt, ry))
        for a, da, b, db in gs.gnand:
            if a in F and b in F and F[a] <= da and F[b] <= db:
                return (f'ESC-CONTRA: witness closure forces '
                        f'AF<={F[a]}[{a}] & AF<={F[b]}[{b}] inside '
                        f'gnand({a},{da},{b},{db})')
        for a, b, d in gs.xnand:
            if a in pos and b in F and F[b] <= d:
                return (f'ESC-CONTRA: witness has {a} with closure '
                        f'AF<={F[b]}[{b}] inside xnand({a},{b},{d})')
        for y, d in e.sneg:
            if y in F and F[y] <= d:
                return (f'ESC-CONTRA: witness closure forces '
                        f'AF<={F[y]}[{y}] against sneg ~AF<={d}[{y}]')
    return None


def _rows_single_firing(gs: GSpec) -> bool:
    """True when every row fires at most once in any model of the
    obligatory core -- the condition under which the builder's
    instance encoding (bind-to-pend or own-fresh per firing) is
    EXHAUSTIVE over schedules, making search exhaustion a sound
    infeasibility certificate.  (With multiple firings, a real
    schedule may SHARE one re-service between windows, which the
    encoding cannot express.)"""
    cnt: dict = {}
    for x, s in gs.pend:
        cnt[x] = cnt.get(x, 0) + 1
    for e in gs.esc:
        for x in e.pos:
            cnt[x] = cnt.get(x, 0) + 1
        for y, d in e.spos:
            cnt[y] = cnt.get(y, 0) + 1
    fired: dict = {}
    for _ in range(4):
        changed = False
        for x, y, d in gs.rows:
            f = cnt.get(x, 0) + fired.get(x, 0)
            if f > fired.get(y, 0):
                fired[y] = f
                changed = True
        if not changed:
            break
    return all(f <= 1 for f in fired.values())


def semantic_certificate(gs: GSpec, deep: bool = False):
    """Per-trajectory infeasibility certificates: arithmetic facts
    that refute EVERY single trajectory (branching cannot help,
    because positive duties bind on every branch).  Returns None or a
    certificate string.  These are the REFUSED-SEMANTIC patterns --
    semantically sound refusals whose derivability from the basis is
    exactly the question the deductive attack must answer.  With
    deep=True (called only on the refusal path), the NAMED patterns
    are followed by the GENERIC certifier: the builder's own
    exhaustive per-branch search re-run as an infeasibility proof,
    sound whenever the instance encoding is exhaustive
    (_rows_single_firing)."""
    eff = _eff(gs)
    stages = dict(gs.pend)
    # GB-PIGEON: a set of atoms pairwise gnand-constrained must be
    # served pairwise-staggered on EVERY branch; services live in
    # (0, max eff]; a chain of k services with pairwise gaps needs
    # span > sum of the k-1 cheapest consecutive gaps.  Certificate:
    # some pairwise-constrained subset whose minimum possible span
    # exceeds its loosest deadline.  (Exhaustive over subsets of the
    # gnand graph's vertices that are pairwise adjacent and forced.)
    import itertools
    gpairs = {}
    for x, d1, y, d2 in gs.gnand:
        gpairs[frozenset((x, y))] = (min(d1, d2))
    forced = [x for x in eff]
    for k in range(3, len(forced) + 1):
        for sub in itertools.combinations(forced, k):
            if not all(frozenset(p) in gpairs
                       for p in itertools.combinations(sub, 2)):
                continue
            # min span: order services; consecutive gap > the pair's
            # min(d1,d2); cheapest chain = min over orders of the sum
            # of consecutive gaps.  k small: brute-force orders.
            best = None
            for order in itertools.permutations(sub):
                s = sum(gpairs[frozenset((order[i], order[i + 1]))]
                        for i in range(k - 1))
                best = s if best is None or s < best else best
            latest = max(eff[x] for x in sub)
            if best is not None and Fraction(best) >= latest:
                return (f'GB-PIGEON: atoms {sub} pairwise staggered, '
                        f'min chain span {best} >= loosest deadline '
                        f'{latest}: every trajectory refuted')
    # GB-LATE-PINCH: gnand (x,d1,y,d2) where x carries a late-window
    # fact (exactness: first-x > s_x - 1 on some branch; avoid on
    # pending x: first-x > h) and y is pending.  On the designated
    # late branch: x-before-y needs t_y > t_x + d2 > L + d2, so
    # s_y > L + d2; y-before-x needs t_x - t_y > d1 with t_x <= s_x,
    # t_y > 0, so s_x > d1.  Both failing refutes the late branch --
    # and the late branch is obligatory (the seed's negative demands
    # it), so the theory is unsatisfiable.  Cell-tier derivation
    # sketch (O1a avoiding chain + refl + D1 + box-MP + G4) in
    # the development record; direct derivation = rule-harvest question.
    late_windows = {}
    for x in gs.exact:
        if x in stages:
            late_windows[x] = max(late_windows.get(x, 0),
                                  stages[x] - 1)
    for z, h in gs.avoid:
        if z in stages:
            late_windows[z] = max(late_windows.get(z, 0), h)
    for x, d1, y, d2 in gs.gnand:
        for (a, da, b, db) in ((x, d1, y, d2), (y, d2, x, d1)):
            if a in late_windows and b in stages:
                L = late_windows[a]
                if Fraction(stages[b]) <= L + db \
                        and Fraction(stages[a]) <= da:
                    return (f'GB-LATE-PINCH: gnand({x},{d1},{y},{d2})'
                            f' with {a} late past {L}: '
                            f's_{b}={stages[b]} <= {L}+{db} and '
                            f's_{a}={stages[a]} <= {da}: the '
                            f'obligatory late branch is refuted')
    # ESC-LOCK: a lock at T on a pattern whose pos atom must have an
    # instance strictly after T - on every branch or on the branch a
    # max-fact designates.  (a) pending+exact z with s-1 >= T: the
    # late branch's first z-instance exceeds s-1 >= T, so that branch
    # has no pattern-stop by T; (b) pending z with avoid horizon
    # h >= T: same, via the avoiding branch; (c) pending z with
    # eff... a plain pending z needs z <= s on every branch but can
    # sit early, EXCEPT that the pattern-stop needs the LAST
    # z-instance before T: rows firing z from late services force
    # late z-instances: if some row x->z (within d) has x pending
    # exact with s_x - 1 >= T, the late-x branch gets a z-instance
    # after s_x - 1 >= T.
    for e in gs.esc:
        if e.lock is None:
            continue
        T = Fraction(e.lock)
        for z in e.pos:
            if z in stages and z in gs.exact \
                    and Fraction(stages[z] - 1) >= T:
                return (f'ESC-LOCK: lock {e.lock} on pos atom {z} '
                        f'exact at stage {stages[z]}: late-branch '
                        f'z-instance > {stages[z]-1} >= T (LOCK-ABS '
                        f'candidate)')
            for zz, h in gs.avoid:
                if zz == z and z in stages and Fraction(h) >= T:
                    return (f'ESC-LOCK: lock {e.lock} on pos atom '
                            f'{z} pending with avoid horizon {h} >= '
                            f'T: the avoiding branch serves z past '
                            f'{h} (LOCK-ABS candidate)')
            for x, y, d in gs.rows:
                if y == z and x in gs.exact and x in stages \
                        and Fraction(stages[x] - 1) >= T:
                    return (f'ESC-LOCK: lock {e.lock} on pos atom '
                            f'{z} row-fired by exact {x} (stage '
                            f'{stages[x]}): fired instance > '
                            f'{stages[x]-1} >= T (LOCK-ABS '
                            f'candidate)')
    if not deep or not _rows_single_firing(gs):
        return None
    # the generic tier: search exhaustion as certificate
    lock_caps: dict = {}
    for e in gs.esc:
        if e.lock is None:
            continue
        for z in e.pos:
            cap = NSQ(e.lock) - E2
            lock_caps[z] = min(lock_caps.get(z, cap), cap)
    constrained = sorted({a for g in gs.gnand for a in (g[0], g[2])
                          if a in stages}
                         | {a for x in (gs.xnand or ()) for a in
                            (x[0], x[1]) if a in stages})
    rotation_atoms = constrained if constrained else []
    nrot = max(1, len(rotation_atoms))

    def searched(late_here, escapes):
        for rot in range(nrot):
            try:
                if _branch_schedule(gs, rotation_atoms, rot,
                                    late_here, escapes,
                                    lock_caps) is not None:
                    return True
            except Refusal:
                continue
        return False

    if not searched(set(), []):
        return ('BRANCH-CORE-INFEASIBLE (generic): no schedule '
                'serves the obligatory per-branch core under any '
                'order -- every trajectory refuted (exhaustive '
                'search; encoding-exhaustive specimen)')
    for a in sorted(set(gs.exact)
                    | {z for z, h in gs.avoid if z in stages}):
        if not searched({a}, []):
            return (f'LATE-BRANCH-INFEASIBLE (generic): the '
                    f'obligatory late branch for atom {a} admits no '
                    f'schedule under any order (exhaustive search)')
    for eid, e in enumerate(gs.esc):
        if not searched(set(), [(eid, e)]):
            return (f'ESC-BRANCH-INFEASIBLE (generic): escape {eid} '
                    f'({"lock " + str(e.lock) if e.lock is not None else "no lock"}'
                    f') hosts on no branch under any order '
                    f'(exhaustive search) -- ESC placement refuted')
    return None


# ---------------------------------------------------------------------------
# the branched staggered builder

class Refusal(Exception):
    pass


class _System:
    """A per-branch difference system over NSQ times.  Variables are
    service/escape instances; constraints: lower <= t, t <= upper,
    t_a <= t_b + c.  Solve for the LAZY (componentwise-maximal)
    solution by relaxation from uppers; infeasible when a variable
    falls below its lower bound."""

    def __init__(self):
        self.upper: dict = {}
        self.lower: dict = {}
        self.diff: list = []     # (a, b, c): t_a <= t_b + c

    def var(self, v, lower, upper):
        self.lower[v] = max(self.lower.get(v, lower), lower)
        self.upper[v] = min(self.upper.get(v, upper), upper)

    def le(self, a, b, c):
        self.diff.append((a, b, c))

    def solve(self):
        t = dict(self.upper)
        for _ in range(len(t) + 1):
            changed = False
            for a, b, c in self.diff:
                cap = t[b] + c
                if t[a] > cap:
                    t[a] = cap
                    changed = True
            if not changed:
                break
        else:
            return None          # negative cycle: infeasible
        for v, lo in self.lower.items():
            if t[v] < lo:
                return None
        return t


def _serialize(times: dict, diffs):
    """Strictly order instances on one branch: keep the lazy times,
    pushing earlier entries down by EPS where they collide.  Ties are
    broken TOPOLOGICALLY by the c <= 0 difference constraints among
    the tied group (the grand47 lesson: a str-order tie-break
    can push the wrong side of a zero-slack row window).  Returns
    [(time, var)] chronological, or None on floor breach."""
    order_edges = {}
    for a, b, c in diffs:
        if c <= NSQ(0):
            order_edges.setdefault(a, set()).add(b)   # a before b
    groups: dict = {}
    for v, t in times.items():
        groups.setdefault((t.a, t.b), []).append(v)

    def topo(group):
        gset = set(group)
        indeg = {v: 0 for v in group}
        for a in group:
            for b in order_edges.get(a, ()):
                if b in gset:
                    indeg[b] += 1
        out, ready = [], sorted([v for v in group if indeg[v] == 0],
                                key=str)
        while ready:
            v = ready.pop(0)
            out.append(v)
            for b in order_edges.get(v, ()):
                if b in gset:
                    indeg[b] -= 1
                    if indeg[b] == 0:
                        ready.append(b)
            ready.sort(key=str)
        return out if len(out) == len(group) else None

    inst = []
    for key in sorted(groups):
        g = topo(groups[key])
        if g is None:
            return None
        for v in g:
            inst.append((v, times[v]))
    out = []
    hi = None
    for v, t in reversed(inst):
        t2 = t if hi is None or t < hi else hi - EPS
        if t2 < EPS:
            return None
        out.append((t2, v))
        hi = t2
    out.reverse()
    # belt: every difference constraint re-verified on final times
    final = {v: t for t, v in out}
    for a, b, c in diffs:
        if final[a] > final[b] + c:
            return None
    return out


def _build_instances(gs: GSpec, late_here: set, escapes: list,
                     lock_caps: dict, row_modes: dict):
    """The variable set for one branch: pend services, escape
    instances, and row-fired instances (fired from EVERY instance,
    fixpoint -- escapes fire rows too; grand25/92 lesson).
    row_modes: (ri, src_var) -> 'bind' | 'fresh' for firings whose
    target is pending.  Returns (vars, inst_atoms, window_edges)
    where window_edges are the row-window difference constraints."""
    stages = dict(gs.pend)
    sy = _System()
    inst_atoms: dict = {}
    edges = []                   # (a, b, c): t_a <= t_b + c

    def add_instance(v, atoms_true, lower, upper):
        sy.var(v, lower, upper)
        inst_atoms[v] = frozenset(atoms_true)

    for x, s in gs.pend:
        up = NSQ(s)
        if x in lock_caps:
            up = min(up, lock_caps[x])
        lo = E2
        if x in late_here:
            lo = max(lo, NSQ(stages[x] - 1) + EPS)
        for z, h in gs.avoid:
            if z == x and x in late_here:
                lo = max(lo, NSQ(h) + EPS)
        add_instance(('p', x), {x}, lo, up)
    for eid, e in escapes:
        v = ('e', eid)
        up = NSQ(10 ** 6)
        lo = E2
        for x in e.pos:
            if x in lock_caps:
                up = min(up, lock_caps[x])
        if e.lock is not None:
            up = min(up, NSQ(e.lock) - E2)
        add_instance(v, set(e.pos), lo, up)
        for y, d in e.spos:
            if y in set(e.pos):
                continue
            # bind to the pend service, or spawn a voluntary
            # re-service (an atom may be true at several states --
            # the grand187 lesson: the pend service can sit
            # gnand-incompatibly early while a re-service lands in
            # the witness window)
            if y in stages and row_modes.get(('spos', eid, y),
                                             'bind') == 'bind':
                yv = ('p', y)
            else:
                yv = ('w', eid, y)
                add_instance(yv, {y}, E2,
                             lock_caps.get(y, NSQ(10 ** 6)))
            edges.append((v, yv, NSQ(0)))     # t_e <= t_y
            edges.append((yv, v, NSQ(d)))     # t_y <= t_e + d
    # row firing fixpoint over all instances
    fired = set()
    for _ in range(8):
        new = []
        for ri, (x, y, d) in enumerate(gs.rows):
            for v, ats in list(inst_atoms.items()):
                if x not in ats or (ri, v) in fired:
                    continue
                fired.add((ri, v))
                # base-set firings enumerate bind/fresh; deeper
                # firings (from fresh/spos instances) default to
                # FRESH -- bind couples the new obligation to the
                # deadline-tight pend service, which is exactly what
                # killed the grand187 chain (the pend service serves
                # the deadline; a re-service serves the window)
                mode = row_modes.get(
                    (ri, v), 'bind' if v[0] in ('p', 'e')
                    else 'fresh')
                if y in stages and mode == 'bind':
                    yv = ('p', y)
                else:
                    yv = ('r', ri, v)
                    up = NSQ(10 ** 6)
                    if y in lock_caps:
                        up = min(up, lock_caps[y])
                    add_instance(yv, {y}, E2, up)
                    new.append(yv)
                edges.append((yv, v, NSQ(d)))   # t_y <= t_x + d
                edges.append((v, yv, NSQ(0)))   # t_x <= t_y
        if not new:
            break
        if len(inst_atoms) > 24:
            raise Refusal('row-firing fixpoint exceeded 24 instances')
    return sy, inst_atoms, edges


def _row_firing_dims(gs: GSpec, escapes: list):
    """Enumerate the bind/fresh choice points: firings whose target
    is pending.  Approximated on the pre-fixpoint instance set (pend
    + escapes); deeper firings default to bind."""
    stages = dict(gs.pend)
    base = [('p', x) for x, s in gs.pend] \
        + [('e', eid) for eid, e in escapes]
    base_atoms = {('p', x): frozenset((x,)) for x, s in gs.pend}
    for eid, e in escapes:
        base_atoms[('e', eid)] = frozenset(e.pos)
    dims = []
    for ri, (x, y, d) in enumerate(gs.rows):
        if y not in stages:
            continue
        for v in base:
            if x in base_atoms[v]:
                dims.append((ri, v))
    for eid, e in escapes:
        for y, d in e.spos:
            if y in stages and y not in set(e.pos):
                dims.append(('spos', eid, y))
    return dims


def _branch_schedule(gs, rotation_atoms, rot, late_here, escapes,
                     lock_caps, max_configs=256):
    """One branch: enumerate row modes x pair sides x sneg modes,
    solve each difference system lazily, serialize, region-check.
    Pair sides: a gnand/xnand instance pair is rotation-resolved
    when both are pend services of rotation-ranked atoms; every
    other pair is a free two-way dimension (grand187 lesson:
    two instances of one atom can need DIFFERENT sides)."""
    import itertools
    order_pos = {a: i for i, a in enumerate(
        rotation_atoms[rot:] + rotation_atoms[:rot])}
    stages = dict(gs.pend)
    row_dims = _row_firing_dims(gs, escapes)
    tried = 0
    for row_choice in itertools.product(('bind', 'fresh'),
                                        repeat=len(row_dims)):
        row_modes = dict(zip(row_dims, row_choice))
        try:
            sy0, inst_atoms, edges = _build_instances(
                gs, late_here, escapes, lock_caps, row_modes)
        except Refusal:
            continue

        def instances_of(a):
            return [v for v, ats in inst_atoms.items() if a in ats]

        # collect pair dimensions
        pair_dims = []               # (kind, params, vx, vy)
        fixed_pairs = []             # (kind, params, vx, vy, x_first)
        for gi, (x, d1, y, d2) in enumerate(gs.gnand):
            for vx in instances_of(x):
                for vy in instances_of(y):
                    if vx == vy:
                        return None  # one instance carries both
                    if vx == ('p', x) and vy == ('p', y) \
                            and x in order_pos and y in order_pos:
                        fixed_pairs.append(
                            ('g', (d1, d2), vx, vy,
                             order_pos[x] < order_pos[y]))
                    else:
                        pair_dims.append(('g', (d1, d2), vx, vy))
        for xi, (x, y, d) in enumerate(gs.xnand):
            for vx in instances_of(x):
                for vy in instances_of(y):
                    if vx == vy:
                        return None
                    pair_dims.append(('x', (d,), vx, vy))
        sneg_dims = []
        for eid, e in escapes:
            for y, d in e.sneg:
                for yv in instances_of(y):
                    if yv != ('e', eid):
                        sneg_dims.append((eid, y, d, yv))
        ndims = len(pair_dims) + len(sneg_dims)
        if 2 ** ndims > max_configs:
            raise Refusal(f'side-choice space 2^{ndims} exceeds cap')
        for choice in itertools.product((True, False), repeat=ndims):
            tried += 1
            if tried > max_configs:
                raise Refusal('config cap exceeded')
            sy = _System()
            sy.upper.update(sy0.upper)
            sy.lower.update(sy0.lower)
            sy.diff = list(edges)
            ok_config = True
            for (kind, params, vx, vy, x_first) in fixed_pairs:
                if kind == 'g':
                    d1, d2 = params
                    if x_first:
                        sy.le(vx, vy, -NSQ(d2) - E2)
                    else:
                        sy.le(vy, vx, -NSQ(d1) - E2)
            ci = 0
            for (kind, params, vx, vy) in pair_dims:
                first = choice[ci]
                ci += 1
                if kind == 'g':
                    d1, d2 = params
                    if first:
                        sy.le(vx, vy, -NSQ(d2) - E2)   # x earlier
                    else:
                        sy.le(vy, vx, -NSQ(d1) - E2)   # y earlier
                else:
                    (d,) = params
                    if first:
                        sy.le(vx, vy, -NSQ(d) - E2)    # x before win
                    else:
                        sy.le(vy, vx, -E2)             # x after y
            for (eid, y, d, yv) in sneg_dims:
                after = choice[ci]
                ci += 1
                v = ('e', eid)
                if after:
                    sy.le(yv, v, -E2)             # y before witness
                else:
                    sy.le(v, yv, -NSQ(d) - E2)    # witness before win
            # solve / serialize to a fixpoint: a tie-push lowers a
            # variable other constraints referenced, so re-relax with
            # the pushed values as uppers and re-serialize until the
            # serialization is constraint-clean (grand176
            # lesson: one eps push can invalidate an upstream gap)
            ser = None
            for _ in range(64):
                t = sy.solve()
                if t is None:
                    break
                ser = _serialize(t, sy.diff)
                if ser is not None:
                    break
                order = _push_order(t, sy.diff)
                if order is None:
                    break
                changed = False
                hi = None
                for v in reversed(order):
                    tv = t[v]
                    t2 = tv if hi is None or tv < hi else hi - EPS
                    if t2 != tv:
                        sy.upper[v] = min(sy.upper[v], t2)
                        changed = True
                    hi = t2
                if not changed:
                    break
            if ser is None:
                continue
            bad = False
            for tt, v in ser:
                if tt < sy.lower[v]:
                    bad = True
                    break
            if bad:
                continue
            sched = [(tt, inst_atoms[v], v) for tt, v in ser]
            if _branch_region_check(gs, sched):
                continue
            return sched
    return None


def _push_order(times: dict, diffs):
    """Chronological instance order for the push pass, ties broken
    topologically by the c <= 0 constraints (shared with
    _serialize's logic)."""
    order_edges = {}
    for a, b, c in diffs:
        if c <= NSQ(0):
            order_edges.setdefault(a, set()).add(b)
    groups: dict = {}
    for v, t in times.items():
        groups.setdefault((t.a, t.b), []).append(v)
    out = []
    for key in sorted(groups):
        group = groups[key]
        gset = set(group)
        indeg = {v: 0 for v in group}
        for a in group:
            for b in order_edges.get(a, ()):
                if b in gset:
                    indeg[b] += 1
        ready = sorted([v for v in group if indeg[v] == 0], key=str)
        done = []
        while ready:
            v = ready.pop(0)
            done.append(v)
            for b in order_edges.get(v, ()):
                if b in gset:
                    indeg[b] -= 1
                    if indeg[b] == 0:
                        ready.append(b)
            ready.sort(key=str)
        if len(done) != len(group):
            return None
        out.extend(done)
    return out


# region calculus for the post-check ------------------------------------------

def _due_region(points, d):
    """points: [(entry, dwell_end)]; region where AF<=d[atom] holds:
    union of [entry - d, dwell_end)."""
    ivs = sorted((p - NSQ(d), q) for p, q in points)
    out = []
    for a, b in ivs:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def _regions_meet(r1, r2):
    i = j = 0
    while i < len(r1) and j < len(r2):
        a1, b1 = r1[i]
        a2, b2 = r2[j]
        if max(a1, a2) < min(b1, b2):
            return max(a1, a2)
        if b1 <= b2:
            i += 1
        else:
            j += 1
    return None


def _branch_region_check(gs: GSpec, sched):
    """sched: [(entry, atomset, var)] chronological; every service
    state has dwell EPS (all-false waits fill the gaps -- must match
    _assemble).  Verifies gnand/xnand/disj on this branch exactly."""
    pts: dict = {}
    for t, ats, v in sched:
        for a in ats:
            pts.setdefault(a, []).append((t, t + EPS))
    for t, ats, v in sched:
        for x, y in gs.disj:
            if x in ats and y in ats:
                return f'disj({x},{y}) violated at {t}'
    for x, d1, y, d2 in gs.gnand:
        m = _regions_meet(_due_region(pts.get(x, []), d1),
                          _due_region(pts.get(y, []), d2))
        if m is not None:
            return (f'gnand({x},{d1},{y},{d2}) regions meet at {m}')
    for x, y, d in gs.xnand:
        m = _regions_meet([(p, q) for p, q in pts.get(x, [])],
                          _due_region(pts.get(y, []), d))
        if m is not None:
            return f'xnand({x},{y},{d}) meets at {m}'
    return None


def build_core_model(gs: GSpec, want_diag=False):
    """GSpec -> (TModel, diag).  Branched staggered lazy builder.
    Search: number of spine branches B (rotations of the constrained
    atoms) x designated-late assignment; escapes on existing states
    or spawned branches.  Raises Refusal when no configuration
    closes."""
    stages = dict(gs.pend)
    # lock caps apply to every instance of a pos atom everywhere
    lock_caps: dict = {}
    for e in gs.esc:
        if e.lock is None:
            continue
        for z in e.pos:
            cap = NSQ(e.lock) - E2
            lock_caps[z] = min(lock_caps.get(z, cap), cap)
    constrained = sorted({a for g in gs.gnand for a in (g[0], g[2])
                          if a in stages}
                         | {a for x in (gs.xnand or ()) for a in
                            (x[0], x[1]) if a in stages})
    rotation_atoms = constrained if constrained else []
    nrot = max(1, len(rotation_atoms))
    late_atoms = set(gs.exact) | {z for z, h in gs.avoid
                                  if z in stages}
    reasons = []
    configs = []
    for B in range(1, max(2, nrot) + 1):
        for base_rot in range(nrot if B < nrot else 1):
            configs.append((B, base_rot))
    for B, base_rot in configs:
        # late assignment: atom -> branch index; round one: spread by
        # rotation position (atom last in rotation r gets branch r
        # when constrained; unconstrained late atoms ride branch 0,
        # or branch (i mod B) when several)
        rot_of = [(base_rot + b) % nrot for b in range(B)]
        late_of: dict = {}
        for i, a in enumerate(sorted(late_atoms)):
            if a in rotation_atoms and B >= 2:
                # branch whose rotation puts a last
                r = (rotation_atoms.index(a) + 1) % len(rotation_atoms)
                late_of[a] = rot_of.index(r) if r in rot_of else i % B
            else:
                late_of[a] = i % B
        branches = []
        fail = None
        for b in range(B):
            rot = rot_of[b]
            late_here = {a for a, bb in late_of.items() if bb == b}
            try:
                sched = _branch_schedule(gs, rotation_atoms, rot,
                                         late_here, [], lock_caps)
            except Refusal as r:
                fail = f'B={B} rot{rot_of} branch {b}: {r}'
                break
            if sched is None:
                fail = f'B={B} rot{rot_of} branch {b} infeasible'
                break
            branches.append(sched)
        if fail:
            reasons.append(fail)
            continue
        # escapes: existing state, else spawn a branch
        esc_placement = []
        for eid, e in enumerate(gs.esc):
            placed = None
            need = set(e.pos)
            for bi, sched in enumerate(branches):
                for t, ats, v in sched:
                    if need <= ats and not (set(e.neg) & ats):
                        # stage conjuncts verified by evaluator; only
                        # accept obvious hosts (spos reflexive-only)
                        if all(y in need for y, d in e.spos) \
                                and not e.sneg and e.lock is None:
                            placed = ('existing', bi, t)
                            break
                if placed:
                    break
            if not placed:
                sched = None
                for rot_try in range(nrot):
                    try:
                        cand = _branch_schedule(
                            gs, rotation_atoms, rot_try, set(),
                            [(eid, e)], lock_caps)
                    except Refusal:
                        continue
                    if cand is not None:
                        sched = cand
                        break
                if sched is None:
                    fail = (f'escape {eid} unplaceable (B={B}): '
                            'spawned-branch search exhausted')
                    break
                branches.append(sched)
                et = next(t for t, ats, v in sched
                          if v == ('e', eid))
                placed = ('spawned', len(branches) - 1, et)
            esc_placement.append(placed)
        if fail:
            reasons.append(fail)
            continue
        return _assemble(gs, branches, esc_placement, B, want_diag,
                         late_of)
    raise Refusal('; '.join(reasons) if reasons
                  else 'no configuration attempted')


def _assemble(gs: GSpec, branches, esc_placement, B, want_diag,
              late_of=None):
    natoms = max(gs.atoms) + 1 if gs.atoms else 1
    states = [(frozenset(), None)]          # (mask, dwell) seed
    adj = [0]
    stay = 0
    dwell = [EPS]                            # seed dwell = branch pt
    val = [0] * natoms
    for sched in branches:
        # service states are SHORT (dwell EPS); all-false wait states
        # fill the gaps -- an atom's presence must not smear across
        # the waits, or its due-region swallows the staggering
        # margins (an early root bug, caught by the region check +
        # evaluator on the first roster run)
        entries = []                        # (entry time, mask)
        cursor = EPS
        for t, ats, v in sched:
            if t > cursor:
                entries.append((cursor, frozenset()))
            entries.append((t, frozenset(ats)))
            cursor = t + EPS
        entries.append((cursor, frozenset()))   # all-false stay tail
        head = len(states)
        adj[0] |= 1 << head
        for i, (t, ats) in enumerate(entries):
            idx = len(states)
            states.append((ats, None))
            if i + 1 < len(entries):
                adj.append(1 << (idx + 1))
                dwell.append(entries[i + 1][0] - t)
            else:
                adj.append(0)
                stay |= 1 << idx
                dwell.append(INF)
            for a in ats:
                val[a] |= 1 << idx
    n = len(states)
    tm = TModel(tstructure(n, tuple(adj), stay, tuple(dwell)),
                tuple(val))
    diag = {'n': n, 'B': B, 'branches': len(branches),
            'esc': esc_placement,
            'scheds': branches, 'late_of': dict(late_of or {})}
    return tm, diag


# ---------------------------------------------------------------------------
# checking

def esc_position(gs: GSpec, placed):
    """Classify an escape's placement for the probe ledger."""
    kind, bi, t = placed
    if kind == 'existing':
        return 'existing-state'
    s = std_part(t)
    horizon = max([s for x, s in gs.pend], default=0)
    if s < 1:
        return 'eps-attachment(unit 1)'
    if s >= horizon:
        return 'post-busy(lazy tail)'
    return f'mid-schedule(unit {int(s) + 1})'


def check_gspec(gs: GSpec, out, expect=None) -> bool:
    """expect: None (must build) | 'screened' | 'semantic'."""
    scr = screen(gs)
    cert = semantic_certificate(gs)
    try:
        tm, diag = build_core_model(gs)
        built = True
    except Refusal as r:
        built = False
        reason = r
        if cert is None:
            cert = semantic_certificate(gs, deep=True)
    if built:
        if expect in ('screened', 'semantic'):
            print(f'- {gs.name}: !! BUILT though expected {expect} '
                  f'({scr or cert})', file=out)
            return False
        if scr or cert:
            print(f'- {gs.name}: !! built but screen/certificate '
                  f'fired: {scr or cert} -- instrument disagreement',
                  file=out)
            return False
        ok = True
        if not is_ceps(tm):
            print(f'- {gs.name}: !! outside C_eps', file=out)
            return False
        g = gspec_formula(gs)
        g_ok = tdenot(g, tm)[0].contains(ZERO)
        ok &= g_ok
        shadow_ok = True
        for delta in SHADOW_DELTAS:
            try:
                sm = subst_model(tm, delta)
            except ValueError:
                shadow_ok = False
                break
            if not tdenot(g, sm)[0].contains(ZERO):
                shadow_ok = False
        ok &= shadow_ok
        esc_note = ''
        if gs.esc:
            esc_note = '; esc: ' + ', '.join(
                esc_position(gs, p) for p in diag['esc'])
        print(f'- {gs.name}: built n={diag["n"]} B={diag["B"]} '
              f'(+{diag["branches"] - diag["B"]} escape branches); '
              f'seed formula {"PASS" if g_ok else "!! FAIL"}; germ '
              f'shadow {"stable" if shadow_ok else "!! UNSTABLE"}'
              + esc_note, file=out)
        return ok
    # refused; expect None means the specimen was expected to BUILD
    if scr:
        print(f'- {gs.name}: REFUSED-SCREENED ({scr})'
              + ('' if expect == 'screened'
                 else ' !! [expected to build]'), file=out)
        return expect == 'screened'
    if cert:
        print(f'- {gs.name}: REFUSED-SEMANTIC ({cert}) -- '
              f'branch-at-seed infeasibility; clocked-SAT open '
              f'(masking can satisfy such specimens); '
              f'builder detail: {reason}'
              + ('' if expect == 'semantic'
                 else ' !! [expected to build]'), file=out)
        return expect == 'semantic'
    print(f'- {gs.name}: !! REFUSED-ALARM ({reason}) -- no screen, '
          f'no certificate: builder limitation or missing law; '
          f'characterize before anything else', file=out)
    return False


# ---------------------------------------------------------------------------
# curated roster

def g_roster():
    return [
        # 1. the staggering-forcer, rebuilt mechanically (first
        # hand-built, now emitted by the builder)
        GSpec(name='jd-rebuilt (mechanical JD)', atoms=(0, 1),
              pend=((0, 2), (1, 2)), exact=(0, 1),
              gnand=((0, 1, 1, 1),)),
        # 2. staggering control: drop exactness -> a chain suffices
        GSpec(name='jd-relax (no exactness: chain closes)',
              atoms=(0, 1), pend=((0, 2), (1, 2)),
              gnand=((0, 1, 1, 1),)),
        # 3. chain staggering inside one branch (loose deadlines)
        GSpec(name='gnand-chain (stages 1,3: reorder, no branch)',
              atoms=(0, 1), pend=((0, 1), (1, 3)),
              gnand=((0, 1, 1, 1),)),
        # 4. the pigeonhole clique: pairwise staggering, tight span
        GSpec(name='pigeon-3 (pairwise gnand, stages 2,2,2)',
              atoms=(0, 1, 2), pend=((0, 2), (1, 2), (2, 2)),
              gnand=((0, 1, 1, 1), (1, 1, 2, 1), (0, 1, 2, 1))),
        # 5. relaxed pigeonhole: span available
        GSpec(name='pigeon-3-relaxed (stages 2,3,4)',
              atoms=(0, 1, 2), pend=((0, 2), (1, 3), (2, 4)),
              gnand=((0, 1, 1, 1), (1, 1, 2, 1), (0, 1, 2, 1))),
        # 6. free escape: witness atom unconstrained, no lock
        GSpec(name='esc-free (z somewhere, no lock)',
              atoms=(0, 1), pend=((0, 1),),
              esc=(Esc(pos=(1,)),)),
        # 7. locked escape: witness pinned inside 2 units
        GSpec(name='esc-lock (z somewhere, era ends by 2)',
              atoms=(0, 1), pend=((0, 1),),
              esc=(Esc(pos=(1,), lock=2),)),
        # 8. the lock pinch: z exact at 3, lock at 1 -- LOCK-ABS
        GSpec(name='esc-lock-pinch (z exact@3, lock@1)',
              atoms=(0,), pend=((0, 3),), exact=(0,),
              esc=(Esc(pos=(0,), lock=1),)),
        # 9. window escape: witness inside y's due window
        GSpec(name='esc-window (z with AF<=1[y] at witness)',
              atoms=(0, 1), pend=((0, 2),),
              esc=(Esc(pos=(1,), spos=((0, 1),)),)),
        # 10. window escape under lock: the eps-attachment shape
        GSpec(name='esc-window-lock (witness in y-window, era ends '
              'by 1)',
              atoms=(0, 1), pend=((0, 2),), exact=(0,),
              esc=(Esc(pos=(1,), spos=((0, 1),), lock=1),)),
        # 11. screened escape: pattern box-refuted (screen liveness)
        GSpec(name='esc-contra (pos pair disjoint)',
              atoms=(0, 1, 2), pend=((0, 1),), disj=((1, 2),),
              esc=(Esc(pos=(1, 2)),)),
        # 12. xnand separation on a chain
        GSpec(name='xnand-sep (x@1, y@2, sep 1)',
              atoms=(0, 1), pend=((0, 1), (1, 2)),
              xnand=((0, 1, 1),)),
        # 13. avoid + gnand + exactness: three-mechanism interaction
        GSpec(name='avoid-gnand (z avoid 2 pending 4, y@1, gap 1)',
              atoms=(0, 1), pend=((0, 4), (1, 1)),
              avoid=((0, 2),), gnand=((0, 1, 1, 1),)),
        # 14. GB-REFL screen liveness
        GSpec(name='gb-refl (both forced inside windows)',
              atoms=(0, 1), pend=((0, 1), (1, 1)),
              gnand=((0, 2, 1, 2),)),
        # 15. row-fired staggering: the row target enters the gnand
        GSpec(name='row-gnand (x fires y, y gnand z)',
              atoms=(0, 1, 2), pend=((0, 1), (2, 3)),
              rows=((0, 1, 1),), gnand=((1, 1, 2, 1),)),
    ]


def check_roster(out) -> bool:
    print('## roster: curated graded-box specimens (the Spec-grammar '
          'gap closed; JD rebuilt mechanically)', file=out)
    expect = {
        'pigeon-3 (pairwise gnand, stages 2,2,2)': 'semantic',
        'esc-lock-pinch (z exact@3, lock@1)': 'semantic',
        'esc-contra (pos pair disjoint)': 'screened',
        'gb-refl (both forced inside windows)': 'screened',
    }
    ok = True
    for gs in g_roster():
        ok &= check_gspec(gs, out, expect.get(gs.name))
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# the random graded tier

def random_gspec(rng: random.Random, i: int) -> GSpec:
    natoms = rng.randint(2, 4)
    atoms = tuple(range(natoms))
    npend = rng.randint(1, min(3, natoms))
    pend_atoms = rng.sample(atoms, npend)
    pend = tuple((x, rng.randint(1, 3)) for x in pend_atoms)
    stages = dict(pend)
    exact = tuple(x for x, s in pend
                  if s >= 2 and rng.random() < 0.4)
    rows = []
    if rng.random() < 0.25:
        x, y = rng.sample(atoms, 2)
        rows.append((x, y, rng.randint(1, 2)))
    disj = []
    for a in range(natoms):
        for b in range(a + 1, natoms):
            if rng.random() < 0.15:
                disj.append((a, b))
    avoid = []
    if rng.random() < 0.3:
        z = rng.choice(atoms)
        avoid.append((z, rng.randint(1, 3)))
    gnand = []
    pairs = [(a, b) for a in atoms for b in atoms if a < b]
    rng.shuffle(pairs)
    for a, b in pairs[:rng.randint(0, 2)]:
        gnand.append((a, rng.randint(1, 2), b, rng.randint(1, 2)))
    xnand = []
    if rng.random() < 0.25:
        x, y = rng.sample(atoms, 2)
        xnand.append((x, y, rng.randint(1, 2)))
    esc = []
    for _ in range(rng.randint(0, 2)):
        z = rng.choice(atoms)
        spos = []
        sneg = []
        if rng.random() < 0.3:
            y = rng.choice([a for a in atoms if a != z])
            spos.append((y, rng.randint(1, 2)))
        elif rng.random() < 0.2:
            y = rng.choice([a for a in atoms if a != z])
            sneg.append((y, rng.randint(1, 2)))
        lock = rng.randint(1, 3) if rng.random() < 0.4 else None
        esc.append(Esc(pos=(z,), spos=tuple(spos), sneg=tuple(sneg),
                       lock=lock))
    return GSpec(name=f'grand{i}', atoms=atoms, pend=pend,
                 exact=exact, rows=tuple(rows), disj=tuple(disj),
                 avoid=tuple(avoid), gnand=tuple(gnand),
                 xnand=tuple(xnand), esc=tuple(esc))


def check_random(out, rounds: int, seed: int) -> bool:
    print(f'## random: {rounds} graded-box specimens (seed {seed}); '
          'three-way classified refusals; unexplained refusal = '
          'ALARM', file=out)
    rng = random.Random(seed)
    ok = True
    built = screened = semantic = 0
    branched = 0
    esc_ledger: dict = {}
    semantic_kinds: dict = {}
    for i in range(rounds):
        gs = random_gspec(rng, i)
        scr = screen(gs)
        if scr:
            screened += 1
            continue
        cert = semantic_certificate(gs)
        try:
            tm, diag = build_core_model(gs)
        except Refusal as r:
            if cert is None:
                cert = semantic_certificate(gs, deep=True)
            if cert:
                semantic += 1
                semantic_kinds[cert.split(':')[0]] = \
                    semantic_kinds.get(cert.split(':')[0], 0) + 1
                continue
            ok = False
            print(f'- grand{i}: !! ALARM -- refused ({r}); no '
                  f'screen, no certificate: {gs}', file=out)
            continue
        if cert:
            ok = False
            print(f'- grand{i}: !! built but semantic certificate '
                  f'claims infeasibility ({cert}): certificate or '
                  f'builder wrong: {gs}', file=out)
            continue
        good = is_ceps(tm) \
            and tdenot(gspec_formula(gs), tm)[0].contains(ZERO)
        if good:
            sm = subst_model(tm, SHADOW_DELTAS[0])
            good &= tdenot(gspec_formula(gs), sm)[0].contains(ZERO)
        if not good:
            ok = False
            print(f'- grand{i}: !! cross-check FAILED on {gs}',
                  file=out)
            continue
        built += 1
        if diag['B'] > 1:
            branched += 1
        for p in diag['esc']:
            pos = esc_position(gs, p)
            esc_ledger[pos] = esc_ledger.get(pos, 0) + 1
    print(f'- {built} built and evaluator-confirmed ({branched} '
          f'needed staggered branches), {screened} screened '
          f'(deduction-backed), {semantic} refused with semantic '
          f'certificates {dict(semantic_kinds)}, '
          f'{"0 alarms" if ok else "ALARMS ABOVE"}', file=out)
    if esc_ledger:
        print(f'- escape-position ledger (the ESC probe): '
              f'{dict(sorted(esc_ledger.items()))}', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# the SUCC-CON-P offer enumerator (the lemma's semantic shadow)
#
# Lemma SUCC-CON-P (development record): every unit-maximal consistent
# live cell with nonempty pending profile has, PER BRANCH CONTEXT, a
# consistent offer -- a pattern S (due subseteq S subseteq P) whose
#   burst half     = the context view + {A<=1[x] : x in S}   (at t)
#   boundary half  = Box + {A<=(s-1)[x] : x notin S} + decremented context
# are both consistent.  The context view carries Box + the graded
# positives + ONE designated negative (exactness/avoid); the cell's
# other negatives are existential (some-branch) facts realized on their
# own branches -- the u'' contrast in the lemma's statement.
#
# This enumerator checks the lemma's SEMANTIC shadow on GSpec cores:
#   - a builder-closed core must show >= 1 satisfiable offer in EVERY
#     obligatory context, and each built branch's extracted layer-1
#     pattern must be among its context's satisfiable offers ("the
#     schedule realizes one");
#   - a certificate-refused core must show SOME obligatory context in
#     which every pattern has an unsatisfiable half (the aggregation's
#     semantic face); per-trajectory certificates should refuse in
#     every context, late-branch certificates in the late context.
# A builder-closes-but-no-offer specimen would mean the lemma is FALSE
# AS STATED (its offer grammar misses semantic reality) -- alarm,
# first-order cargo.  Escapes ride their own dichotomy, not this
# lemma: the check runs on the esc-free GRADED CORE of each specimen.
#
# EPISTEMIC CAVEAT: this enumerator's SAT
# decisions ride the builder + certificates, i.e. the BRANCH-AT-SEED
# class -- and the lemma it shadows was refuted by a specimen OUTSIDE
# that class: the pigeon cell is clocked-consistent (masked.py's
# deep-branching witness) with all 8 pattern-form offers refused
# PROPOSITIONALLY, which no tier below could see because the refusals
# are genuine and the consistency needs masking.  The sweep's 0-alarm
# result therefore certifies the offer grammar only over the builder
# class; it remains in the battery as the branch-at-seed shadow of
# the successor lemma (SUCC-CON), and as the mechanism ledger the
# aggregation consumes.
#
# Two corners the grammar fixes, machine-checked here:
#   - closed deadlines: the lazy builder serves a stage-s base at
#     exactly t = s, so "served in layer 1" is t <= 1 CLOSED (a due
#     base served at the boundary instant still meets A<=1);
#   - due subseteq S: a due base has no remainder decrement (A<=0 is
#     not in the language), so every pattern serves due content.

def graded_core(gs: GSpec) -> GSpec:
    """The esc-free graded core -- the lemma's scope."""
    return GSpec(name=gs.name, atoms=gs.atoms, pend=gs.pend,
                 exact=gs.exact, rows=gs.rows, disj=gs.disj,
                 avoid=gs.avoid, gnand=gs.gnand, xnand=gs.xnand,
                 esc=())


def offer_contexts(gs: GSpec):
    """Obligatory branch contexts: spine + one per designated
    negative.  An exactness fact ~AF<=(s-1)[x] has the avoid shape
    (x, s-1); avoid facts ride as they are."""
    stages = dict(gs.pend)
    ctxs = [('spine', None)]
    for x in gs.exact:
        if stages[x] - 1 >= 1:
            ctxs.append(('late', (x, stages[x] - 1)))
    for z, h in gs.avoid:
        ctxs.append(('avoid', (z, h)))
    return ctxs


def burst_spec(gs: GSpec, ctx, S) -> GSpec:
    """The burst half as a derived GSpec: the context view plus the
    joint A<=1 commitment for S (pend stages tightened to 1).  The
    carried negative is avoid-encoded; box facts unchanged; the
    cell's other negatives are per-branch and absent from the view."""
    pend = tuple((x, 1 if x in S else s) for x, s in gs.pend)
    avoid = () if ctx[0] == 'spine' else (ctx[1],)
    return GSpec(name=f'{gs.name}/burst{sorted(S)}', atoms=gs.atoms,
                 pend=pend, exact=(), rows=gs.rows, disj=gs.disj,
                 avoid=avoid, gnand=gs.gnand, xnand=gs.xnand, esc=())


def boundary_spec(gs: GSpec, ctx, S) -> GSpec:
    """The boundary half: Box + the unserved remainder at decremented
    stages + the decremented context negative.  Served bases are
    gone (no regeneration in the graded core); due subseteq S keeps
    every remainder stage >= 1.  A context window that closes at the
    boundary (h = 1) leaves only the point fact ~theta, which the
    GSpec grammar carries exactly when theta is a remainder atom
    (its pend entry); for a non-pending avoid atom the point residue
    is dropped -- weaker cell, conservative for existence claims."""
    pend = tuple((x, s - 1) for x, s in gs.pend if x not in S)
    avoid = ()
    if ctx[0] != 'spine':
        z, h = ctx[1]
        if z not in S and h - 1 >= 1:
            avoid = ((z, h - 1),)
    return GSpec(name=f'{gs.name}/bdry{sorted(S)}', atoms=gs.atoms,
                 pend=pend, exact=(), rows=gs.rows, disj=gs.disj,
                 avoid=avoid, gnand=gs.gnand, xnand=gs.xnand, esc=())


def spec_sat(gs: GSpec):
    """Decide a derived cell semantically: ('sat', diag) |
    ('unsat', reason) | ('unknown', builder detail).  Screen and
    certificate fire before the builder (instrument-disagreement
    would surface in the main battery); the deep generic certifier
    runs only on the refusal path, as in check_gspec."""
    if not gs.pend:
        return ('sat', None)     # empty cell: the one-wait model
    scr = screen(gs)
    if scr:
        return ('unsat', 'screen:' + scr.split(':')[0])
    cert = semantic_certificate(gs)
    if cert:
        return ('unsat', 'cert:' + cert.split(':')[0])
    try:
        tm, diag = build_core_model(gs, want_diag=True)
        return ('sat', diag)
    except Refusal as r:
        cert = semantic_certificate(gs, deep=True)
        if cert:
            return ('unsat', 'cert:' + cert.split(':')[0].split(' ')[0])
        return ('unknown', str(r))


def enumerate_offers(gs: GSpec):
    """Per obligatory context: the full pattern table.  Returns
    {ctx: {'offers': [S...], 'refused': {S: (half, reason)},
           'unknown': {S: (half, detail)}}} over due <= S <= P."""
    import itertools
    stages = dict(gs.pend)
    atoms_p = [x for x, s in gs.pend]
    assert len(set(atoms_p)) == len(atoms_p), 'duplicate pend base'
    due = frozenset(x for x, s in gs.pend if s == 1)
    rest = [x for x in atoms_p if x not in due]
    table = {}
    for ctx in offer_contexts(gs):
        offers, refused, unknown = [], {}, {}
        for k in range(len(rest) + 1):
            for extra in itertools.combinations(rest, k):
                S = due | frozenset(extra)
                bv = spec_sat(burst_spec(gs, ctx, S))
                if bv[0] == 'unsat':
                    refused[S] = ('burst', bv[1])
                    continue
                if bv[0] == 'unknown':
                    unknown[S] = ('burst', bv[1])
                    continue
                dv = spec_sat(boundary_spec(gs, ctx, S))
                if dv[0] == 'unsat':
                    refused[S] = ('boundary', dv[1])
                elif dv[0] == 'unknown':
                    unknown[S] = ('boundary', dv[1])
                else:
                    offers.append(S)
        table[ctx] = {'offers': offers, 'refused': refused,
                      'unknown': unknown}
    return table


def realized_patterns(gs: GSpec, diag):
    """Extract, per built branch, the CLOSED-unit-1 served pattern and
    the contexts that branch realizes (its designated negatives, or
    spine when it carries none)."""
    stages = dict(gs.pend)
    late_of = diag.get('late_of', {})
    out = []
    for bi, sched in enumerate(diag.get('scheds', [])):
        S = frozenset(v[1] for t, ats, v in sched
                      if v[0] == 'p' and t <= NSQ(1))
        negs = sorted(a for a, b in late_of.items() if b == bi)
        ctxs = []
        if not negs:
            ctxs.append(('spine', None))
        for a in negs:
            if a in gs.exact:
                ctxs.append(('late', (a, stages[a] - 1)))
            for z, h in gs.avoid:
                if z == a:
                    ctxs.append(('avoid', (z, h)))
        out.append((bi, S, ctxs))
    return out


def check_offers(out, rounds: int, seed: int) -> bool:
    """The SUCC-CON-P sweep: roster cores + a random tier."""
    print(f'## offers: SUCC-CON-P enumerator over graded cores '
          f'(roster + {rounds} randoms, seed {seed}); '
          f'builder-closed core with an offerless obligatory context '
          f'= LEMMA-FALSE alarm', file=out)
    rng = random.Random(seed)
    specs = [(gs, 'roster') for gs in g_roster()]
    for i in range(rounds):
        specs.append((random_gspec(rng, i), 'random'))
    ok = True
    n_built = n_refused = 0
    offer_counts = []
    refusal_mechs: dict = {}
    realized_ok = realized_gap = 0
    converse_ok = 0
    gaps = 0
    for gs0, tier in specs:
        core = graded_core(gs0)
        scr = screen(core)
        cert = None if scr else semantic_certificate(core)
        built = False
        if not scr and not cert:
            try:
                tm, diag = build_core_model(core, want_diag=True)
                built = True
            except Refusal as r:
                cert = semantic_certificate(core, deep=True)
                if cert is None:
                    print(f'- {core.name} [{tier}]: !! core ALARM '
                          f'(refused, no certificate: {r}) -- '
                          f'outside the offer check\'s scope', file=out)
                    ok = False
                    continue
        if scr:
            continue             # derivably-inconsistent seed: no cell
        table = enumerate_offers(core)
        if built:
            n_built += 1
            for ctx, row in table.items():
                offer_counts.append(len(row['offers']))
                for S, (half, mech) in row['refused'].items():
                    refusal_mechs[mech] = refusal_mechs.get(mech, 0) + 1
                if not row['offers']:
                    if row['unknown']:
                        gaps += 1
                        print(f'- {core.name} [{tier}]: INSTRUMENT-GAP '
                              f'ctx {ctx}: no decided offer, unknowns '
                              f'{dict(row["unknown"])}', file=out)
                        ok = False
                    else:
                        print(f'- {core.name} [{tier}]: !! LEMMA-FALSE '
                              f'ALARM ctx {ctx}: builder closed but '
                              f'every offer refused: '
                              f'{dict(row["refused"])}', file=out)
                        ok = False
            for bi, S, ctxs in realized_patterns(core, diag):
                for ctx in ctxs:
                    if ctx not in table:
                        continue
                    if S in table[ctx]['offers']:
                        realized_ok += 1
                    elif S in table[ctx]['unknown']:
                        realized_gap += 1
                        print(f'- {core.name} [{tier}]: realized '
                              f'pattern {sorted(S)} on branch {bi} '
                              f'undecided by the enumerator '
                              f'(instrument gap, witness exists by '
                              f'construction)', file=out)
                    else:
                        print(f'- {core.name} [{tier}]: !! ALARM '
                              f'branch {bi} realizes {sorted(S)} in '
                              f'ctx {ctx} but the enumerator refused '
                              f'it: '
                              f'{table[ctx]["refused"].get(S)}',
                              file=out)
                        ok = False
        else:
            n_refused += 1
            all_refusing = [ctx for ctx, row in table.items()
                            if not row['offers'] and not row['unknown']]
            if all_refusing:
                converse_ok += 1
                for ctx in all_refusing:
                    for S, (half, mech) in \
                            table[ctx]['refused'].items():
                        refusal_mechs[mech] = \
                            refusal_mechs.get(mech, 0) + 1
            else:
                undecided = any(row['unknown']
                                for row in table.values())
                if undecided:
                    gaps += 1
                    print(f'- {core.name} [{tier}]: INSTRUMENT-GAP '
                          f'(refused core {cert.split(":")[0]}; '
                          f'converse blocked by unknowns)', file=out)
                    ok = False
                else:
                    print(f'- {core.name} [{tier}]: !! DISAGREEMENT: '
                          f'core certificate-refused '
                          f'({cert.split(":")[0]}) yet every '
                          f'obligatory context has a builder-SAT '
                          f'offer -- candidate masking-satisfiable '
                          f'specimen (masking class); '
                          f'characterize before trusting either tier',
                          file=out)
                    ok = False
    mn = min(offer_counts) if offer_counts else 0
    mx = max(offer_counts) if offer_counts else 0
    print(f'- {n_built} built cores: every obligatory context '
          f'offer-checked (per-context offers min {mn} max {mx}); '
          f'realized patterns confirmed {realized_ok} '
          f'(+{realized_gap} undecided-but-witnessed); '
          f'{n_refused} refused cores, {converse_ok} with an '
          f'all-refusing context confirmed; refusal mechanisms '
          f'{dict(sorted(refusal_mechs.items()))}; '
          f'{"0 alarms" if ok else "ALARMS ABOVE"}', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------

def run_battery(out, rounds: int, seed: int) -> bool:
    print('# cores: the graded-box constructive tier '
          '(builder + refusal classifier)', file=out)
    print(file=out)
    print('Ground truth is the evaluator: every emitted model is '
          'cross-checked with tdenot at the seed against the FULL '
          'graded formula (positives, exactness, avoid, graded '
          'boxes, escapes, locks), plus a germ-shadow spot check.  '
          'Refusals are classified three ways: screened (deduction-'
          'backed), semantic-certificate (derivability OPEN -- the '
          'harvest), alarm (loud).', file=out)
    print(file=out)
    ok = True
    ok &= check_roster(out)
    ok &= check_random(out, rounds, seed)
    ok &= check_offers(out, min(rounds, 200), seed)
    from masked import check_masked
    ok &= check_masked(out)
    from family import check_family
    ok &= check_family(out)
    print(f'cores overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


def main():
    ap = argparse.ArgumentParser(
        description='cores: graded-box constructive tier')
    ap.add_argument('cmd', nargs='?', default='battery',
                    choices=['battery', 'roster', 'random', 'offers',
                             'masked'])
    ap.add_argument('--rounds', type=int, default=200)
    ap.add_argument('--seed', type=int, default=20260720)
    args = ap.parse_args()
    out = sys.stdout
    if args.cmd == 'battery':
        ok = run_battery(out, args.rounds, args.seed)
    elif args.cmd == 'roster':
        ok = check_roster(out)
    elif args.cmd == 'offers':
        ok = check_offers(out, args.rounds, args.seed)
    elif args.cmd == 'masked':
        from masked import check_masked
        ok = check_masked(out)
    else:
        ok = check_random(out, args.rounds, args.seed)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
