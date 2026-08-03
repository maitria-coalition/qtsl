#!/usr/bin/env python3
"""QTSL timed validity oracle -- clocked models.

Extends the deadline-free oracle (oracle.py) to
the FULL fragment: deadline operators F<=T and U<=T join atoms,
Booleans, P>=1[G .], P>=1[Streett(...)], arbitrarily nested, evaluated
exactly (Fraction arithmetic) over finite CLOCKED models.

Model class:
a model is (Q, E, stay, u, val) -- finite locations, edges, stay flags,
per-location max-dwell u(q) in Q_{>0} u {oo} (stay implies u = oo),
clock-blind atom valuations. The state space is {(q, c) : 0 <= c <
u(q)} (c = time-in-location); trajectories dwell from clock c to any
c' in (c, u(q)], then jump along an edge and reset the clock to 0;
stay-forever is legal exactly at stay-flagged locations. Trajectories
are total on [0, oo) with locally finite jumps (cadlag; Zeno runs are
not trajectories -- same exclusion as v0's step-function class).

B1-B3 closure holds by locality of the dwell rule: a shift lands
mid-dwell at (q, c), a legal state, and the remaining dwell options
are again "any c' in (c, u(q)]"; fusion pastes legal local behavior.
Class membership: the state space is a disjoint union of half-open
segments (each clopen), trajectories are cadlag into it, and
atom denotations (unions of whole segments) are closed -- every
clocked model is a C_cd member, hence C_0. Verdict semantics inherit
v0's: a countermodel here refutes a law claimed over C_0 or C_cd; the
instrument is structurally blind to C_0 \\ C_cd separations (EQ-U8's
hand-built C_0 countermodel stays hand-built; its C_cd validity is
what this oracle confirms).

Denotations: atoms are clock-blind but WRAPPED formulas are not --
the truth of P>=1[F<=T phi] at (q, c) varies with c through the
remaining-dwell budget. Every denotation is, per location, a finite
union of rational clock intervals with open/closed endpoint flags
(the miniature zone construction the route doc names); the evaluator
computes them exactly.

Worst-case debut A(q,c) := sup over trajectories of the debut into a
target set E (so P>=1[F<=T E] = {A <= T}): within a target-free clock
piece A is linear of slope -1 in c, determined by the location
constants A_q := A(q, 0), which satisfy the longest-path fixpoint
    A_q = max( cbar_q + max{A_q' : q' live successor},
               [stay_q] g_q )
with g_q = inf of E-clocks at q (oo if none), cbar_q = min(g_q, u_q),
base case A_q = 0 when g_q = 0; oo on positive cycles of the non-base
subgraph and at stay locations with g = oo. (Adversary analysis: an
escape jump at clock exactly min(g, u) is always legal -- at the jump
time the trajectory occupies the successor, never the departure clock
-- so interval endpoint flags never enter A, only the inf values g.)

U<=T adds the safe clause: tau |= phi_s U<=T phi iff tau_E <= T and
tau_{~S} >= tau_E. A state fails iff A > T or some trajectory visits
an unsafe non-target clock point and then continues avoiding E for a
positive duration (bad1); bad1 is a reachability predicate R with the
same piece structure (here endpoint flags DO matter: an unsafe visit
exactly at an open-left target endpoint is not a violation, since the
debut equals the visit time and the safe clause quantifies strictly
below it).

G and Streett generalize v0 verbatim once "location p satisfies x"
becomes a clock-interval query: G = within-location suffix containment
+ full containment at every jump-reachable location; Streett violation
structures = SCCs (with internal walk) of the "phi-avoidable"
subgraph (avoidable iff the avoid-budget cbar^phi(0) > 0) containing a
rho-hittable-while-avoiding location, plus stay locations with
phi-clocks bounded above and rho-clocks unbounded; both are
clock-uniform (jump reachability ignores clocks). With u = oo
everywhere the clocked evaluator specializes to v0 exactly -- the
differential self-check below runs that correspondence on random
models and formulas.

Python as orchestration-class code, same warrant as oracle.py
(tiny exact search spaces, Fractions; graduates to Rust if it ever
becomes a grinder).

New formula constructors (extending oracle.py's tuple AST):
    ('pfle', T, f)        P>=1[F_{<=T} f],        T a Fraction >= 0
    ('pule', T, fs, f)    P>=1[fs U_{<=T} f],     T a Fraction >= 0
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction
from itertools import product
from typing import Iterator, Optional

from oracle import (TOP, BOT, atom, f_not, f_and, f_or, pg, pst,
                         impl, DEAD, Model, structure, denot,
                         _sccs_with_walk, random_formula)
import oracle as base_oracle

# ---------------------------------------------------------------------------
# extended rationals: Fraction plus the infinity sentinel INF
#
# INF is a dedicated singleton, NOT None: None doubles as "unset" in
# value-iteration arrays and running maxima, and conflating the two
# silently drops infinite values from sups (a first-run hazard --
# EQ-U7 "refuted" by an avoid-cycle whose A = oo read back as unset-0).


class _Inf:
    __slots__ = ()

    def __repr__(self):
        return 'INF'


INF = _Inf()


def e_lt(a, b) -> bool:
    if a is INF:
        return False
    if b is INF:
        return True
    return a < b


def e_le(a, b) -> bool:
    return not e_lt(b, a)


def e_min(a, b):
    return a if e_lt(a, b) else b


def e_add(a, b):
    if a is INF or b is INF:
        return INF
    return a + b


def e_max(a, b):
    return b if e_lt(a, b) else a


# ---------------------------------------------------------------------------
# interval sets: finite unions of rational intervals with endpoint flags
#
# An IntervalSet is a canonical tuple of (lo, lo_incl, hi, hi_incl)
# with lo a Fraction >= 0, hi a Fraction or INF (INF forces hi_incl
# False), lo < hi or (lo == hi and both inclusive: a point). Canonical:
# sorted, pairwise disjoint AND non-mergeable (adjacent intervals that
# would union to an interval are merged; a shared endpoint absent from
# both sides keeps them separate -- point-gaps are semantics here).

def _ivl_ok(lo, li, hi, hi_i):
    if hi is INF:
        return not hi_i
    if lo < hi:
        return True
    return lo == hi and li and hi_i


def _canon(ivls):
    xs = [iv for iv in ivls if _ivl_ok(*iv)]
    xs.sort(key=lambda iv: (iv[0], not iv[1]))
    out = []
    for lo, li, hi, hi_i in xs:
        if out:
            plo, pli, phi, phi_i = out[-1]
            # mergeable iff overlapping or touching with the touch point
            # covered by at least one side
            if e_lt(lo, phi) or (phi is not INF and lo == phi and (li or phi_i)):
                # extend previous
                if e_lt(phi, hi) or (hi is not INF and phi == hi
                                     and hi_i and not phi_i):
                    out[-1] = (plo, pli, hi, hi_i)
                elif phi is not INF and hi is not INF and phi == hi:
                    out[-1] = (plo, pli, phi, phi_i or hi_i)
                continue
        out.append((lo, li, hi, hi_i))
    return tuple(out)


class ISet:
    """Canonical finite union of rational intervals within [0, u)."""

    __slots__ = ('ivls',)

    def __init__(self, ivls=()):
        self.ivls = _canon(ivls)

    def __eq__(self, other):
        return self.ivls == other.ivls

    def __hash__(self):
        return hash(self.ivls)

    def __repr__(self):
        if not self.ivls:
            return '{}'
        bits = []
        for lo, li, hi, hi_i in self.ivls:
            l = '[' if li else '('
            r = ']' if hi_i else ')'
            h = 'oo' if hi is INF else str(hi)
            bits.append(f'{l}{lo},{h}{r}')
        return 'u'.join(bits)

    def is_empty(self) -> bool:
        return not self.ivls

    def contains(self, c: Fraction) -> bool:
        for lo, li, hi, hi_i in self.ivls:
            if e_lt(c, lo) or (c == lo and not li):
                return False
            if e_lt(c, hi) or (hi is not INF and c == hi and hi_i):
                return True
        return False

    def inf(self):
        """(value, attained) of the set's infimum; (INF, False) if empty."""
        if not self.ivls:
            return INF, False
        lo, li, _, _ = self.ivls[0]
        return lo, li

    def sup_last(self):
        """(value, attained) of the set's supremum; (INF, False) if the
        last interval is unbounded."""
        if not self.ivls:
            return None, False
        _, _, hi, hi_i = self.ivls[-1]
        return hi, hi_i

    def unbounded(self) -> bool:
        return bool(self.ivls) and self.ivls[-1][2] is INF

    def union(self, other: 'ISet') -> 'ISet':
        return ISet(self.ivls + other.ivls)

    def inter(self, other: 'ISet') -> 'ISet':
        out = []
        for a in self.ivls:
            for b in other.ivls:
                lo, li = (a[0], a[1])
                if e_lt(lo, b[0]) or (lo == b[0] and li and not b[1]):
                    lo, li = b[0], b[1]
                hi, hi_i = a[2], a[3]
                if e_lt(b[2], hi) or (b[2] is not INF and b[2] == hi
                                      and hi_i and not b[3]):
                    hi, hi_i = b[2], b[3]
                if _ivl_ok(lo, li, hi, hi_i):
                    out.append((lo, li, hi, hi_i))
        return ISet(out)

    def complement(self, u) -> 'ISet':
        """Complement within the domain [0, u)  (u Fraction or INF)."""
        out = []
        cur_lo, cur_li = Fraction(0), True
        for lo, li, hi, hi_i in self.ivls:
            # gap [cur_lo, lo) with flags
            out.append((cur_lo, cur_li, lo, not li))
            if hi is INF:
                cur_lo, cur_li = None, None
                break
            cur_lo, cur_li = hi, not hi_i
        if cur_lo is not None:
            out.append((cur_lo, cur_li, u, False))
        return ISet(out)

    def minus(self, other: 'ISet', u) -> 'ISet':
        return self.inter(other.complement(u))


def iv_full(u) -> ISet:
    return ISet([(Fraction(0), True, u, False)])


def iv_empty() -> ISet:
    return ISet()


def iv_suffix(c0, incl: bool, u) -> ISet:
    """{c : c >= c0} (or > c0) within [0, u)."""
    if c0 is INF:
        return iv_empty()
    lo = c0 if c0 > 0 else Fraction(0)
    li = incl if c0 > 0 else True
    if c0 < 0:
        lo, li = Fraction(0), True
    return ISet([(lo, li, u, False)])


# ---------------------------------------------------------------------------
# formulas: the two new constructors (+ display)

def pfle(T, f):
    return ('pfle', Fraction(T), f)


def pule(T, fs, f):
    return ('pule', Fraction(T), fs, f)


def tnatoms(f) -> int:
    k = f[0]
    if k == 'pfle':
        return tnatoms(f[2])
    if k == 'pule':
        return max(tnatoms(f[2]), tnatoms(f[3]))
    if k == 'atom':
        return f[1] + 1
    if k in ('top', 'bot'):
        return 0
    if k in ('not', 'pg'):
        return tnatoms(f[1])
    if k in ('and', 'or'):
        return max(tnatoms(f[1]), tnatoms(f[2]))
    if k == 'pst':
        return max((max(tnatoms(r), tnatoms(p)) for r, p in f[1]), default=0)
    raise ValueError(k)


def tshow(f) -> str:
    k = f[0]
    if k == 'pfle':
        return f'AF<={f[1]}[{tshow(f[2])}]'
    if k == 'pule':
        return f'A[{tshow(f[2])} U<={f[1]} {tshow(f[3])}]'
    if k == 'atom':
        return 'abcdefgh'[f[1]]
    if k == 'top':
        return 'T'
    if k == 'bot':
        return 'F'
    if k == 'not':
        return f'~{tshow(f[1])}'
    if k == 'and':
        return f'({tshow(f[1])}&{tshow(f[2])})'
    if k == 'or':
        return f'({tshow(f[1])}|{tshow(f[2])})'
    if k == 'pg':
        return f'AG[{tshow(f[1])}]'
    if k == 'pst':
        inner = ','.join(f'({tshow(r)},{tshow(p)})' for r, p in f[1])
        return f'ASt[{inner}]'
    raise ValueError(k)


def scale_formula(f, lam: Fraction):
    """Multiply every deadline by lam (the SCALE meta-theorem's syntax map)."""
    k = f[0]
    if k == 'pfle':
        return ('pfle', f[1] * lam, scale_formula(f[2], lam))
    if k == 'pule':
        return ('pule', f[1] * lam, scale_formula(f[2], lam),
                scale_formula(f[3], lam))
    if k in ('atom', 'top', 'bot'):
        return f
    if k in ('not', 'pg'):
        return (k, scale_formula(f[1], lam))
    if k in ('and', 'or'):
        return (k, scale_formula(f[1], lam), scale_formula(f[2], lam))
    if k == 'pst':
        return ('pst', tuple((scale_formula(r, lam), scale_formula(p, lam))
                             for r, p in f[1]))
    raise ValueError(k)


# ---------------------------------------------------------------------------
# clocked models

class TStructure:
    """Valuation-independent part: liveness + jump-reachability.

    Liveness is clock-independent: from any (q, c) with c < u(q) a
    positive dwell followed by a jump (or a stay) is available, so
    q is live iff stay(q) or some successor is live -- the same
    greatest fixpoint as v0."""

    __slots__ = ('n', 'adj', 'stay', 'u', 'live', 'reach', 'reach_after')

    def __init__(self, n: int, adj: tuple, stay: int, u: tuple):
        for q in range(n):
            if (stay >> q) & 1 and u[q] is not INF:
                raise ValueError('stay flag requires u = oo')
            if u[q] is not INF and u[q] <= 0:
                raise ValueError('u must be positive')
        self.n = n
        self.adj = adj
        self.stay = stay
        self.u = u
        live = (1 << n) - 1
        while True:
            new = 0
            for q in range(n):
                if (stay >> q) & 1 or (adj[q] & live):
                    new |= 1 << q
            new &= live
            if new == live:
                break
            live = new
        self.live = live
        reach = [0] * n
        for q in range(n):
            if not (live >> q) & 1:
                continue
            seen = 1 << q
            frontier = 1 << q
            while frontier:
                nxt = 0
                f = frontier
                while f:
                    v = (f & -f).bit_length() - 1
                    f &= f - 1
                    nxt |= self.adj[v] & live & ~seen
                seen |= nxt
                frontier = nxt
            reach[q] = seen
        self.reach = tuple(reach)
        # reach_after[q]: locations reachable after at least one jump
        ra = [0] * n
        for q in range(n):
            if not (live >> q) & 1:
                continue
            m = 0
            s = adj[q] & live
            while s:
                v = (s & -s).bit_length() - 1
                s &= s - 1
                m |= reach[v]
            ra[q] = m
        self.reach_after = tuple(ra)


_TSTRUCT_CACHE: dict = {}


def tstructure(n, adj, stay, u) -> TStructure:
    key = (n, adj, stay, u)
    s = _TSTRUCT_CACHE.get(key)
    if s is None:
        s = TStructure(n, adj, stay, u)
        _TSTRUCT_CACHE[key] = s
    return s


class TModel:
    __slots__ = ('s', 'val')

    def __init__(self, s: TStructure, val: tuple):
        self.s = s
        self.val = val

    def __repr__(self):
        s = self.s
        edges = [(i, j) for i in range(s.n) for j in range(s.n)
                 if (s.adj[i] >> j) & 1]
        stays = [q for q in range(s.n) if (s.stay >> q) & 1]
        us = ['oo' if x is INF else str(x) for x in s.u]
        vals = {chr(ord('a') + i): [q for q in range(s.n) if (m >> q) & 1]
                for i, m in enumerate(self.val)}
        live = [q for q in range(s.n) if (s.live >> q) & 1]
        return (f'TModel(n={s.n}, edges={edges}, stay={stays}, '
                f'u={us}, val={vals}, live={live})')


# A denotation is a tuple of ISet, one per location (subset of [0, u_q)).

def _full_den(tm: TModel):
    return tuple(iv_full(tm.s.u[q]) for q in range(tm.s.n))


def _mask_den(tm: TModel, mask: int):
    return tuple(iv_full(tm.s.u[q]) if (mask >> q) & 1 else iv_empty()
                 for q in range(tm.s.n))


# ---------------------------------------------------------------------------
# worst-case debut machinery (the pfle/pule engine)

def _debut_constants(tm: TModel, target):
    """A_q = A(q, 0) = sup over trajectories from fresh arrival at q of
    the debut into `target` (per-location ISet). Returns a list over
    locations: Fraction, INF, or None for dead locations (no
    trajectories; the wrapper is vacuously true there).

    Fixpoint: A_q = 0 if g_q = 0 (any positive dwell meets the target
    immediately, and no escape jump fits below it); otherwise
    A_q = max(cbar_q + max_{q' in live succ} A_{q'}, [stay_q] g_q)
    with g_q = inf(target_q), cbar_q = min(g_q, u_q). INF exactly on
    locations reaching (through non-base live locations) a non-base
    cycle or a stay location with g = oo."""
    s = tm.s
    n = s.n
    g = [None] * n
    base = [False] * n
    for q in range(n):
        if not (s.live >> q) & 1:
            continue
        gv, _attained = target[q].inf()
        g[q] = gv
        base[q] = (gv is not INF and gv == 0)
    # INF detection on the non-base live subgraph
    nonbase = 0
    for q in range(n):
        if (s.live >> q) & 1 and not base[q]:
            nonbase |= 1 << q
    inf_src = 0
    for q in range(n):
        if (nonbase >> q) & 1 and (s.stay >> q) & 1 and g[q] is INF:
            inf_src |= 1 << q
    # cycles within nonbase: q on a cycle iff q reaches q via >=1 step
    # inside nonbase
    for q in range(n):
        if not (nonbase >> q) & 1:
            continue
        seen = 0
        frontier = s.adj[q] & nonbase
        while frontier & ~seen:
            seen |= frontier
            nxt = 0
            f = frontier
            while f:
                v = (f & -f).bit_length() - 1
                f &= f - 1
                nxt |= s.adj[v] & nonbase
            frontier = nxt & ~seen
        if (seen >> q) & 1:
            inf_src |= 1 << q
    # backward closure of inf_src through nonbase edges
    inf_set = inf_src
    changed = True
    while changed:
        changed = False
        for q in range(n):
            if (nonbase >> q) & 1 and not (inf_set >> q) & 1 \
                    and (s.adj[q] & s.live & inf_set):
                inf_set |= 1 << q
                changed = True
    A = [None] * n
    for q in range(n):
        if not (s.live >> q) & 1:
            continue
        if base[q]:
            A[q] = Fraction(0)
        elif (inf_set >> q) & 1:
            A[q] = INF
    # value iteration on the remaining (acyclic-on-nonbase) part
    for _ in range(n + 1):
        changed = False
        for q in range(n):
            if not (s.live >> q) & 1 or base[q] or (inf_set >> q) & 1:
                continue
            best = None  # max over options; None = no option yet
            succ = s.adj[q] & s.live
            if succ:
                cbar = e_min(g[q], s.u[q])
                j = None
                sm = succ
                ok = True
                while sm:
                    v = (sm & -sm).bit_length() - 1
                    sm &= sm - 1
                    if A[v] is None and not base[v]:
                        ok = False  # successor value not yet computed
                        break
                    av = A[v] if A[v] is not None else Fraction(0)
                    j = av if j is None else e_max(j, av)
                if ok and j is not None:
                    best = e_add(cbar, j)
            if (s.stay >> q) & 1:
                stayv = g[q]  # g is finite here (else inf_src)
                best = stayv if best is None else e_max(best, stayv)
            if best is not None and best != A[q]:
                A[q] = best
                changed = True
        if not changed:
            break
    else:
        raise AssertionError('debut value iteration failed to stabilize')
    return A


def _pieces(target_q: ISet, u):
    """Maximal target-free clock intervals of [0, u), each with the inf
    of the next target interval (or INF): yields (piece_ivl, g).

    In the canonical complement, pieces and target intervals alternate,
    so a piece's next-target inf is its own sup -- unless the piece runs
    to the domain boundary (sup = u, or unbounded), where no target
    follows. A right-CLOSED piece end at g (target open-left there) is
    the degenerate boundary point c = g: no escape jump fits below the
    target and any positive dwell meets it immediately, so A(q, g) = 0
    and bad1 is unachievable from it; callers handle that point."""
    for lo, li, hi, hi_i in target_q.complement(u).ivls:
        if hi is INF or (u is not INF and hi == u):
            g = INF
        else:
            g = hi
        yield (lo, li, hi, hi_i), g


def _forall_debut_le(tm: TModel, target, T: Fraction):
    """Denotation of P>=1[F<=T target]: dead states + live (q,c) with
    A(q,c) <= T."""
    s = tm.s
    A = _debut_constants(tm, target)
    out = []
    for q in range(s.n):
        u = s.u[q]
        if not (s.live >> q) & 1:
            out.append(iv_full(u))
            continue
        acc = target[q]  # A = 0 <= T on the target itself
        succ = s.adj[q] & s.live
        j = None
        if succ:
            sm = succ
            while sm:
                v = (sm & -sm).bit_length() - 1
                sm &= sm - 1
                av = A[v]
                j = av if j is None else e_max(j, av)
        for (lo, li, hi, hi_i), g in _pieces(target[q], u):
            piece = ISet([(lo, li, hi, hi_i)])
            # degenerate boundary point c = g (right-closed piece end at
            # an open-left target): A = 0 there, unconditionally
            boundary_pt = None
            if g is not INF and hi_i and hi == g:
                boundary_pt = ISet([(g, True, g, True)])
                acc = acc.union(boundary_pt)
                piece = piece.minus(boundary_pt, u)
            # on the piece's interior-toward-g part: options are
            #   jump:  min(g, u) - c + j      (if succ nonempty)
            #   stay:  g - c                  (if stay flag)
            # A(c) = max(options);  A(c) <= T  iff  c >= theta with
            # theta = max over options of (option value at c = 0 minus
            # T); an INF option kills the piece.
            theta = Fraction(0)
            dead_piece = False
            if succ:
                cbar = e_min(g, u)
                if j is INF or cbar is INF:
                    dead_piece = True
                else:
                    theta = max(theta, cbar + j - T)
            if (s.stay >> q) & 1:
                if g is INF:
                    dead_piece = True
                else:
                    theta = max(theta, g - T)
            if dead_piece:
                continue
            acc = acc.union(piece.inter(iv_suffix(theta, True, u)))
        out.append(acc)
    return tuple(out)


def _bad1_reach(tm: TModel, target, unsafe):
    """R_q (fresh arrival): some trajectory from (q, 0) visits an
    unsafe non-target clock point strictly before its own target debut
    (with positive continued avoidance). unsafe = per-location ISet of
    NON-TARGET unsafe clocks (caller intersects with the target
    complement)."""
    s = tm.s
    n = s.n
    R = [False] * n
    # per-location: exists unsafe gamma in [0, cbar) -- cbar = min(g, u)
    loc_hit = [False] * n
    cbar0 = [None] * n
    for q in range(n):
        if not (s.live >> q) & 1:
            continue
        g, _ = target[q].inf()
        cb = e_min(g, s.u[q])
        cbar0[q] = cb
        if cb is INF or cb > 0:
            window = ISet([(Fraction(0), True, cb, False)]) if cb is not INF \
                else ISet([(Fraction(0), True, INF, False)])
            loc_hit[q] = not unsafe[q].inter(window).is_empty()
    changed = True
    while changed:
        changed = False
        for q in range(n):
            if not (s.live >> q) & 1 or R[q]:
                continue
            if loc_hit[q]:
                R[q] = True
                changed = True
                continue
            cb = cbar0[q]
            if cb is INF or cb > 0:
                sm = s.adj[q] & s.live
                while sm:
                    v = (sm & -sm).bit_length() - 1
                    sm &= sm - 1
                    if R[v]:
                        R[q] = True
                        changed = True
                        break
    return R


def _forall_until_le(tm: TModel, safe, target, T: Fraction):
    """Denotation of P>=1[safe U<=T target]."""
    s = tm.s
    fden = _forall_debut_le(tm, target, T)
    unsafe = tuple(safe[q].complement(s.u[q]).minus(target[q], s.u[q])
                   for q in range(s.n))
    R = _bad1_reach(tm, target, unsafe)
    out = []
    for q in range(s.n):
        u = s.u[q]
        if not (s.live >> q) & 1:
            out.append(iv_full(u))
            continue
        # R(q, c): FALSE on the target; per target-free piece:
        #   TRUE on the whole piece if some live successor has R
        #   (a jump below cbar is available throughout the piece);
        #   plus the prefix {c : [c, cbar) meets unsafe}.
        jumpR = False
        sm = s.adj[q] & s.live
        while sm:
            v = (sm & -sm).bit_length() - 1
            sm &= sm - 1
            if R[v]:
                jumpR = True
                break
        rset = iv_empty()
        for (lo, li, hi, hi_i), g in _pieces(target[q], u):
            piece = ISet([(lo, li, hi, hi_i)])
            # degenerate boundary point c = g: no positive avoidance is
            # possible there -- bad1 unachievable, drop it from the piece
            if g is not INF and hi_i and hi == g:
                piece = piece.minus(ISet([(g, True, g, True)]), u)
            if jumpR and (s.adj[q] & s.live):
                rset = rset.union(piece)
                continue
            cb = e_min(g, u)
            window = ISet([(Fraction(0), True, cb, False)]) if cb is not INF \
                else ISet([(Fraction(0), True, INF, False)])
            uw = unsafe[q].inter(window)
            if uw.is_empty():
                continue
            h, h_att = uw.sup_last()
            # [c, cbar) meets unsafe iff c <= h (last unsafe point
            # attained) or c < h (approached)
            if h is INF:
                rset = rset.union(piece)
            else:
                pref = ISet([(Fraction(0), True, h, h_att)])
                rset = rset.union(piece.inter(pref))
        ok = fden[q].minus(rset, u)
        out.append(ok)
    return tuple(out)


# ---------------------------------------------------------------------------
# the evaluator

def tdenot(f, tm: TModel):
    """Denotation of state formula f in clocked model tm: tuple of ISet."""
    s = tm.s
    k = f[0]
    if k == 'atom':
        mask = tm.val[f[1]] if f[1] < len(tm.val) else 0
        return _mask_den(tm, mask)
    if k == 'top':
        return _full_den(tm)
    if k == 'bot':
        return tuple(iv_empty() for _ in range(s.n))
    if k == 'not':
        d = tdenot(f[1], tm)
        return tuple(d[q].complement(s.u[q]) for q in range(s.n))
    if k == 'and':
        a, b = tdenot(f[1], tm), tdenot(f[2], tm)
        return tuple(a[q].inter(b[q]) for q in range(s.n))
    if k == 'or':
        a, b = tdenot(f[1], tm), tdenot(f[2], tm)
        return tuple(a[q].union(b[q]) for q in range(s.n))
    if k == 'pg':
        phi = tdenot(f[1], tm)
        full = [phi[q] == iv_full(s.u[q]) for q in range(s.n)]
        out = []
        for q in range(s.n):
            u = s.u[q]
            if not (s.live >> q) & 1:
                out.append(iv_full(u))
                continue
            ra = s.reach_after[q]
            ok = True
            m = ra
            while m:
                v = (m & -m).bit_length() - 1
                m &= m - 1
                if not full[v]:
                    ok = False
                    break
            if not ok:
                out.append(iv_empty())
                continue
            # within-location: {c : [c, u) subseteq phi_q} -- the suffix
            # condition; phi_q's last interval must run to u
            ivls = phi[q].ivls
            if ivls and ivls[-1][2] is INF and u is INF:
                lo, li, _, _ = ivls[-1]
                out.append(iv_suffix(lo, li, u))
            elif ivls and u is not INF and ivls[-1][2] == u:
                lo, li, _, _ = ivls[-1]
                out.append(iv_suffix(lo, li, u))
            else:
                out.append(iv_empty())
        return tuple(out)
    if k == 'pst':
        pair_dens = [(tdenot(r, tm), tdenot(p, tm)) for r, p in f[1]]
        bad = 0
        for pden, phiden in pair_dens:
            # avoid-capability and rho-hittability per location
            avoid = 0
            rho_hit = 0
            for q in range(s.n):
                if not (s.live >> q) & 1:
                    continue
                g, _ = phiden[q].inf()
                cb = e_min(g, s.u[q])
                if cb is INF or cb > 0:
                    avoid |= 1 << q
                    window = ISet([(Fraction(0), True, cb, False)]) \
                        if cb is not INF \
                        else ISet([(Fraction(0), True, INF, False)])
                    if not pden[q].inter(window).is_empty():
                        rho_hit |= 1 << q
            w = 0
            for scc in _sccs_with_walk(s.n, s.adj, avoid):
                if scc & rho_hit:
                    w |= scc
            # stay violations: phi-clocks bounded above, rho-clocks
            # unbounded (entry past sup(phi) then dwell forever)
            for q in range(s.n):
                if (s.stay >> q) & 1 and (s.live >> q) & 1:
                    if not phiden[q].unbounded() and pden[q].unbounded():
                        w |= 1 << q
            if w:
                for q in range(s.n):
                    if (s.live >> q) & 1 and (s.reach[q] & w):
                        bad |= 1 << q
        out = []
        for q in range(s.n):
            if not (s.live >> q) & 1:
                out.append(iv_full(s.u[q]))
            elif (bad >> q) & 1:
                out.append(iv_empty())
            else:
                out.append(iv_full(s.u[q]))
        return tuple(out)
    if k == 'pfle':
        return _forall_debut_le(tm, tdenot(f[2], tm), f[1])
    if k == 'pule':
        return _forall_until_le(tm, tdenot(f[2], tm), tdenot(f[3], tm), f[1])
    raise ValueError(k)


# ---------------------------------------------------------------------------
# model enumeration / sampling / checking

U_MENU_EXH = (Fraction(1), Fraction(2), INF)
U_MENU_RAND = (Fraction(1, 2), Fraction(1), Fraction(3, 2), Fraction(2),
               Fraction(3), INF)


def exhaustive_tmodels(n: int, k: int, umenu=U_MENU_EXH) -> Iterator[TModel]:
    masks = range(1 << n)
    for adj in product(masks, repeat=n):
        for u in product(umenu, repeat=n):
            inf_mask = 0
            for q in range(n):
                if u[q] is INF:
                    inf_mask |= 1 << q
            stay_opts = [m for m in masks if m & ~inf_mask == 0]
            for stay in stay_opts:
                s = tstructure(n, tuple(adj), stay, tuple(u))
                for val in product(masks, repeat=k):
                    yield TModel(s, tuple(val))


def random_tmodel(n: int, k: int, rng: random.Random,
                  umenu=U_MENU_RAND) -> TModel:
    full = (1 << n) - 1
    adj = []
    for _ in range(n):
        mask = 0
        for j in range(n):
            if rng.random() < 0.3:
                mask |= 1 << j
        adj.append(mask)
    u = tuple(rng.choice(umenu) for _ in range(n))
    stay = 0
    for q in range(n):
        if u[q] is INF and rng.random() < 0.35:
            stay |= 1 << q
    s = tstructure(n, tuple(adj), stay, tuple(u))
    val = tuple(rng.randint(0, full) for _ in range(k))
    return TModel(s, val)


class TCounterexample:
    def __init__(self, model: TModel, q: int, c: Fraction, side: str):
        self.model = model
        self.q = q
        self.c = c
        self.side = side

    def __repr__(self):
        return f'TCX(q={self.q}, c={self.c}, {self.side}, {self.model!r})'


def _witness_point(iset: ISet):
    """A rational clock value inside a nonempty ISet."""
    lo, li, hi, hi_i = iset.ivls[0]
    if li:
        return lo
    if hi is INF:
        return lo + Fraction(1, 2)
    return (lo + hi) / 2


def _fails(lhs_d, rhs_d, tm: TModel):
    for q in range(tm.s.n):
        diff = lhs_d[q].minus(rhs_d[q], tm.s.u[q])
        if not diff.is_empty():
            return q, _witness_point(diff)
    return None


def find_t_countermodel(lhs, rhs, *, direction: str = 'impl',
                        max_exhaustive_n: int = 2,
                        exhaustive_k_cap: int = 2,
                        random_rounds: int = 3000,
                        random_n: int = 4,
                        seed: int = 0) -> Optional[TCounterexample]:
    """Search clocked models for a countermodel to lhs <= rhs (or ==).
    None = no countermodel within budget (NOT a validity proof; the
    clocked class is C_cd, so silence says nothing about C_0 \\ C_cd)."""
    k = max(tnatoms(lhs), tnatoms(rhs), 1)

    def test(tm: TModel) -> Optional[TCounterexample]:
        ld, rd = tdenot(lhs, tm), tdenot(rhs, tm)
        w = _fails(ld, rd, tm)
        if w:
            return TCounterexample(tm, w[0], w[1], 'lhs>rhs')
        if direction == 'equiv':
            w = _fails(rd, ld, tm)
            if w:
                return TCounterexample(tm, w[0], w[1], 'rhs>lhs')
        return None

    kk = min(k, exhaustive_k_cap)
    for n in range(1, max_exhaustive_n + 1):
        for tm in exhaustive_tmodels(n, kk):
            cx = test(tm)
            if cx:
                return cx
    rng = random.Random(seed)
    for _ in range(random_rounds):
        n = rng.randint(2, random_n)
        cx = test(random_tmodel(n, k, rng))
        if cx:
            return cx
    return None


# ---------------------------------------------------------------------------
# the timed battery: the EQ-U rows, their tightness controls, and the
# cell-C down payments

A, B, C = atom(0), atom(1), atom(2)
H = Fraction(1, 2)
ONE = Fraction(1)
TWO = Fraction(2)


def timed_battery_rows():
    """(row id, lhs, rhs, direction, expectation, note). Expectations
    for the two converse rows follow the fusion proofs in the
    development record, CONTRADICTING an earlier hand remark on EQ-U7;
    the battery is the adjudicator."""
    return [
        ('EQ-U1', pule(ONE, TOP, A), pfle(ONE, A), 'equiv', 'valid',
         'F from U: trivial safe clause'),
        ('EQ-U3', pfle(H, A), pfle(ONE, A), 'impl', 'valid',
         'deadline weakening T <= T\''),
        ('EQ-U3-U', pule(H, B, A), pule(ONE, B, A), 'impl', 'valid',
         'deadline weakening, U form'),
        ('EQ-U3-strict', pfle(ONE, A), pfle(H, A), 'impl', 'refutable',
         'weakening direction is strict: T\' < T refutable'),
        ('EQ-U4', A, pule(ONE, BOT, A), 'impl', 'valid',
         'reflexivity, even with bot safe argument'),
        ('EQ-U4-conv', pule(ONE, B, A), A, 'impl', 'refutable',
         'reflexivity converse control'),
        ('EQ-U5', pule(Fraction(0), B, A), pfle(Fraction(0), A), 'equiv',
         'valid', 'zero-deadline collapse (boundary case)'),
        ('EQ-U6', f_and(pg(B), pfle(ONE, A)), pule(ONE, B, A), 'impl',
         'valid', 'invariant + deadline strengthen to until'),
        ('EQ-U6-conv', pule(ONE, B, A), f_and(pg(B), pfle(ONE, A)),
         'impl', 'refutable',
         'until does not give invariance past the debut'),
        ('EQ-U7', pfle(ONE, pfle(ONE, A)), pfle(TWO, A), 'impl', 'valid',
         'deadline composition'),
        ('EQ-U7-conv', pfle(TWO, A), pfle(ONE, pfle(ONE, A)), 'impl',
         'valid',
         'FINDING: the converse is C_0-VALID (B3-fusion proof; '
         'the once-conjectured hand-countermodel does not exist) '
         '-- EQ-U7 upgrades to an equivalence'),
        ('EQ-U7-conv-asym', pfle(TWO, A), pfle(H, pfle(Fraction(3, 2), A)),
         'impl', 'valid',
         'asymmetric split of the same equivalence'),
        ('EQ-U8-cd', pule(ONE, B, pule(ONE, B, A)), pule(TWO, B, A),
         'impl', 'valid',
         'until pasting: valid over C_cd = this whole model class '
         '(the C_0 countermodel lives outside it)'),
        ('EQ-U8-conv', pule(TWO, B, A), pule(ONE, B, pule(ONE, B, A)),
         'impl', 'valid',
         'FINDING: U-pasting converse is C_0-valid '
         '(fusion proof, a subseteq Y + safe-clause bookkeeping)'),
        ('EQ-C2', pfle(Fraction(0), A), f_or(A, DEAD), 'equiv', 'valid',
         'zero-deadline closure collapse (atoms are clopen here)'),
        ('S10-F', pfle(ONE, pst([(A, B)])), pst([(A, B)]), 'impl',
         'valid',
         'deadline variant of EQ-S10: one visit to a Streett-'
         'guaranteeing region suffices (tail property)'),
        ('S9-F-tight', pfle(ONE, A), A, 'impl', 'refutable',
         'one visit is not now: control'),
        ('U-safety-necessity', pfle(ONE, A), pule(ONE, B, A), 'impl',
         'refutable', 'F does not carry the safe clause: control'),
        ('U-nesting-G', pg(pfle(ONE, A)), pfle(ONE, A), 'impl', 'valid',
         'EQ-G4 shadow at a timed operand (quasi-reflexivity + vacuity)'),
        # --- deadline-tier harvest (found via the timed corpus's
        # apparently-valid bucket; proofs in the development record) ---
        ('EQ-U9', pfle(ONE, BOT), DEAD, 'equiv', 'valid',
         'deadline vacuity converse: AF<=T[F] == D (the F-wrapper '
         'sibling of EQ-S12; live states cannot reach bot)'),
        ('EQ-U10s', f_and(pg(C), pule(ONE, f_and(B, C), A)),
         f_and(pg(C), pule(ONE, B, A)), 'equiv', 'valid',
         'invariant relativization of the U safe position '
         '(the graded EQ-S7)'),
        ('EQ-U10t', f_and(pg(C), pule(ONE, B, f_and(A, C))),
         f_and(pg(C), pule(ONE, B, A)), 'equiv', 'valid',
         'invariant relativization of the U target position'),
        ('EQ-U10-noinv', pule(ONE, B, A), pule(ONE, f_and(B, C), A),
         'impl', 'refutable',
         'relativization without the certified invariant: control'),
    ]


def run_timed_battery(out, quick: bool):
    max_n = 2
    rounds = 800 if quick else 3000
    print('# timed oracle battery -- EQ-U rows + controls, '
          f'exhaustive n<={max_n} (u menu {U_MENU_EXH}) '
          f'+ {rounds} random rounds', file=out)
    print(file=out)
    ok = True
    for row_id, lhs, rhs, direction, expect, note in timed_battery_rows():
        cx = find_t_countermodel(lhs, rhs, direction=direction,
                                 max_exhaustive_n=max_n,
                                 random_rounds=rounds, seed=42)
        if expect == 'valid':
            verdict = 'CONFIRMED (no countermodel)' if cx is None \
                else f'!! REFUTED: {cx!r}'
            if cx is not None:
                ok = False
        else:
            verdict = f'countermodel found as expected: {cx!r}' \
                if cx is not None else '!! NO countermodel found (expected one)'
            if cx is None:
                ok = False
        print(f'- **{row_id}** ({note}): {verdict}', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# self-checks: interval algebra, v0 differential, SCALE metamorphic

_SAMPLE_GRID = [Fraction(k, 4) for k in range(0, 17)] + [Fraction(100)]


def _random_iset(rng: random.Random, u) -> ISet:
    ivls = []
    for _ in range(rng.randint(0, 3)):
        lo = Fraction(rng.randint(0, 12), 4)
        span = Fraction(rng.randint(0, 8), 4)
        hi = lo + span
        li = rng.random() < 0.5
        hi_i = rng.random() < 0.5 and span > 0 or (span == 0)
        if u is not INF:
            if lo >= u:
                continue
            if hi is not INF and hi > u:
                hi, hi_i = u, False
        if rng.random() < 0.1:
            hi, hi_i = INF, False
        ivls.append((lo, li or span == 0, hi, hi_i if hi is not INF else False))
    return ISet(ivls)


def selfcheck_intervals(rounds: int, seed: int) -> list:
    """Interval ops vs pointwise truth on a sample grid."""
    rng = random.Random(seed)
    failures = []
    for _ in range(rounds):
        u = rng.choice((Fraction(4), INF))
        a = _random_iset(rng, u)
        b = _random_iset(rng, u)
        uni, itr = a.union(b), a.inter(b)
        cmp_a = a.complement(u)
        for c in _SAMPLE_GRID:
            if u is not INF and c >= u:
                continue
            ac, bc = a.contains(c), b.contains(c)
            if uni.contains(c) != (ac or bc):
                failures.append(('union', a, b, c))
            if itr.contains(c) != (ac and bc):
                failures.append(('inter', a, b, c))
            if cmp_a.contains(c) != (not ac):
                failures.append(('compl', a, u, c))
    return failures


def diff_v0(rounds: int, seed: int) -> list:
    """u = oo everywhere: the clocked evaluator must agree with v0 on
    every deadline-free formula (denotations are then full-or-empty per
    location)."""
    rng = random.Random(seed)
    failures = []
    for _ in range(rounds):
        n = rng.randint(1, 5)
        m = base_oracle.random_model(n, 2, rng)
        s = m.s
        ts = tstructure(s.n, s.adj, s.stay, tuple([INF] * s.n))
        tm = TModel(ts, m.val)
        f = random_formula(rng, rng.randint(1, 3))
        want = denot(f, m)
        got = tdenot(f, tm)
        for q in range(s.n):
            w = bool((want >> q) & 1)
            g_full = got[q] == iv_full(INF)
            g_empty = got[q].is_empty()
            if not (g_full or g_empty) or g_full != w:
                failures.append((f, m, q, want, got[q]))
                break
    return failures


def random_timed_formula(rng: random.Random, depth: int, k: int = 2):
    if depth == 0:
        r = rng.random()
        if r < 0.7:
            return atom(rng.randrange(k))
        return TOP if r < 0.85 else BOT
    r = rng.random()
    T_menu = (H, ONE, TWO)
    if r < 0.15:
        return f_not(random_timed_formula(rng, depth - 1, k))
    if r < 0.3:
        return f_and(random_timed_formula(rng, depth - 1, k),
                     random_timed_formula(rng, depth - 1, k))
    if r < 0.45:
        return f_or(random_timed_formula(rng, depth - 1, k),
                    random_timed_formula(rng, depth - 1, k))
    if r < 0.6:
        return pg(random_timed_formula(rng, depth - 1, k))
    if r < 0.75:
        return pfle(rng.choice(T_menu),
                    random_timed_formula(rng, depth - 1, k))
    if r < 0.9:
        return pule(rng.choice(T_menu),
                    random_timed_formula(rng, depth - 1, k),
                    random_timed_formula(rng, depth - 1, k))
    pairs = [(random_timed_formula(rng, depth - 1, k),
              random_timed_formula(rng, depth - 1, k))
             for _ in range(rng.randint(1, 2))]
    return pst(pairs)


def _scale_iset(x: ISet, lam: Fraction) -> ISet:
    return ISet([(lo * lam, li, INF if hi is INF else hi * lam, hi_i)
                 for lo, li, hi, hi_i in x.ivls])


def metamorphic_scale(rounds: int, seed: int) -> list:
    """SCALE meta-theorem: scaling all dwell bounds and deadlines by
    lam > 0 maps denotations by c -> lam*c."""
    rng = random.Random(seed)
    failures = []
    for _ in range(rounds):
        n = rng.randint(1, 4)
        tm = random_tmodel(n, 2, rng)
        f = random_timed_formula(rng, rng.randint(1, 3))
        for lam in (Fraction(2), Fraction(1, 3)):
            u2 = tuple(INF if x is INF else x * lam for x in tm.s.u)
            ts2 = tstructure(tm.s.n, tm.s.adj, tm.s.stay, u2)
            tm2 = TModel(ts2, tm.val)
            f2 = scale_formula(f, lam)
            d1 = tdenot(f, tm)
            d2 = tdenot(f2, tm2)
            for q in range(n):
                if _scale_iset(d1[q], lam) != d2[q]:
                    failures.append((f, tm, lam, q, d1[q], d2[q]))
                    break
    return failures


def run_selfchecks(out, quick: bool):
    ok = True
    r = 200 if quick else 600
    fails = selfcheck_intervals(r, seed=11)
    print(f'- interval algebra vs point sampling ({r} rounds): '
          + ('CONFIRMED' if not fails else f'!! {len(fails)} failures; '
             f'first: {fails[0]!r}'), file=out)
    ok &= not fails
    r = 300 if quick else 1200
    fails = diff_v0(r, seed=13)
    print(f'- v0 differential, u=oo embedding ({r} rounds): '
          + ('CONFIRMED' if not fails else f'!! {len(fails)} failures; '
             f'first: {fails[0]!r}'), file=out)
    ok &= not fails
    r = 100 if quick else 400
    fails = metamorphic_scale(r, seed=17)
    print(f'- SCALE metamorphic (lam = 2, 1/3; {r} rounds): '
          + ('CONFIRMED' if not fails else f'!! {len(fails)} failures; '
             f'first: {fails[0]!r}'), file=out)
    ok &= not fails
    return ok


# ---------------------------------------------------------------------------
# timed corpus (cell C's measure-then-grow loop)

def timed_corpus(pairs: int, seed: int):
    rng = random.Random(seed)
    seen = set()
    refuted, apparent = [], []
    attempts = 0
    while len(refuted) + len(apparent) < pairs and attempts < pairs * 60:
        attempts += 1
        f = random_timed_formula(rng, 2)
        g = random_timed_formula(rng, 2)
        if f == g or (f, g) in seen:
            continue
        seen.add((f, g))
        cx = find_t_countermodel(f, g, direction='equiv',
                                 max_exhaustive_n=2, random_rounds=600,
                                 seed=seed ^ attempts)
        if cx:
            refuted.append((f, g, cx))
        else:
            apparent.append((f, g))
    return refuted, apparent


# ---------------------------------------------------------------------------
# main

def main():
    ap = argparse.ArgumentParser(
        description='timed validity oracle (clocked models)')
    sub = ap.add_subparsers(dest='cmd', required=True)
    b = sub.add_parser('battery', help='EQ-U rows + controls')
    b.add_argument('--quick', action='store_true')
    b.add_argument('--out', default='-')
    sc = sub.add_parser('selfcheck',
                        help='interval algebra + v0 differential + SCALE')
    sc.add_argument('--quick', action='store_true')
    sc.add_argument('--out', default='-')
    c = sub.add_parser('corpus', help='timed derivability corpus')
    c.add_argument('--pairs', type=int, default=30)
    c.add_argument('--seed', type=int, default=2026)
    c.add_argument('--out', default='-')
    args = ap.parse_args()
    out = sys.stdout if args.out == '-' else open(args.out, 'w')
    try:
        if args.cmd == 'battery':
            ok1 = run_selfchecks(out, args.quick)
            print(file=out)
            ok2 = run_timed_battery(out, args.quick)
            print(f'timed battery overall: {"PASS" if ok1 and ok2 else "FAIL"}',
                  file=out)
            sys.exit(0 if ok1 and ok2 else 1)
        elif args.cmd == 'selfcheck':
            ok = run_selfchecks(out, args.quick)
            print(f'selfcheck overall: {"PASS" if ok else "FAIL"}', file=out)
            sys.exit(0 if ok else 1)
        else:
            refuted, apparent = timed_corpus(args.pairs, args.seed)
            print(f'# timed corpus -- {len(refuted)} refuted, '
                  f'{len(apparent)} apparently-valid (seed={args.seed})',
                  file=out)
            print(file=out)
            print('## apparently-valid candidate equivalences', file=out)
            for f, g in apparent:
                print(f'- `{tshow(f)}`  ==  `{tshow(g)}`', file=out)
            print(file=out)
            print('## sample refuted candidates (first 10)', file=out)
            for f, g, cx in refuted[:10]:
                print(f'- `{tshow(f)}`  vs  `{tshow(g)}` -- {cx!r}', file=out)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == '__main__':
    main()
