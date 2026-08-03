#!/usr/bin/env python3
"""QTSL validity oracle v0 -- the deadline-free qualitative fragment.

Decides truth of QTSL-1 state formulas built from
atoms, Booleans, P>=1[G .], and P>=1[Streett(...)] over finite
behavioral graph models, and searches for countermodels to candidate
implications/equivalences.

Semantics and class-legitimacy (why a verdict here is a verdict about
the dense-time behavioral class): see README.md beside this file.
Models are C_cd members (right-continuous step trajectories); the
instrument is structurally blind to C_0 \\ C_cd separations (EQ-U8's
countermodel is hand-built for exactly that reason) and must not be
pointed at C_cont-only laws except to demonstrate class-flag
necessity.

Deadline operators (F<=T, U<=T) are deliberately rejected in v0; the
clocked-model oracle (timed.py) carries them.

Python is used as orchestration-class code: the search
spaces here are tiny and exact (bitmask sets, no numerics). If corpus
generation ever becomes a grinder, the successor graduates it to Rust.

Formulas are nested tuples:
    ('atom', i)            atom index i
    ('top',) | ('bot',)
    ('not', f) | ('and', f, g) | ('or', f, g)
    ('pg', f)              P>=1[G f]
    ('pst', ((rho, phi), ...))   P>=1[Streett((rho1,phi1),...)]
"""

from __future__ import annotations

import argparse
import random
import sys
from itertools import product
from typing import Iterator, Optional

# ---------------------------------------------------------------------------
# formulas

TOP = ('top',)
BOT = ('bot',)


def atom(i: int):
    return ('atom', i)


def f_not(f):
    return ('not', f)


def f_and(f, g):
    return ('and', f, g)


def f_or(f, g):
    return ('or', f, g)


def pg(f):
    return ('pg', f)


def pst(pairs):
    return ('pst', tuple(pairs))


def impl(f, g):
    return f_or(f_not(f), g)


DEAD = pg(BOT)  # the deadness formula D


def natoms(f) -> int:
    """1 + highest atom index used (0 if none)."""
    k = f[0]
    if k == 'atom':
        return f[1] + 1
    if k in ('top', 'bot'):
        return 0
    if k == 'not' or k == 'pg':
        return natoms(f[1])
    if k in ('and', 'or'):
        return max(natoms(f[1]), natoms(f[2]))
    if k == 'pst':
        return max((max(natoms(r), natoms(p)) for r, p in f[1]), default=0)
    raise ValueError(k)


def show(f) -> str:
    k = f[0]
    if k == 'atom':
        return 'abcdefgh'[f[1]]
    if k == 'top':
        return 'T'
    if k == 'bot':
        return 'F'
    if k == 'not':
        return f'~{show(f[1])}'
    if k == 'and':
        return f'({show(f[1])}&{show(f[2])})'
    if k == 'or':
        return f'({show(f[1])}|{show(f[2])})'
    if k == 'pg':
        return f'AG[{show(f[1])}]'
    if k == 'pst':
        inner = ','.join(f'({show(r)},{show(p)})' for r, p in f[1])
        return f'ASt[{inner}]'
    raise ValueError(k)


# ---------------------------------------------------------------------------
# models: finite behavioral graphs
#
# A model is (n, adj, stay, val):
#   n     -- number of locations, states are 0..n-1
#   adj   -- tuple of n successor bitmasks
#   stay  -- bitmask of locations where trajectories may remain forever
#   val   -- tuple of bitmasks, val[i] = denotation of atom i
#
# Trajectories: right-continuous step functions that follow edges with
# arbitrary positive dwells, with terminal-forever dwell allowed
# exactly at stay-locations.  B1-B3 closure and cadlag membership are
# argued in README.md.  Dead locations (no edges, no stay, or only
# escapes into dead ends) have empty trajectory sets: vacuity.


class Structure:
    """Valuation-independent part: liveness + reachability."""

    __slots__ = ('n', 'adj', 'stay', 'live', 'reach')

    def __init__(self, n: int, adj: tuple, stay: int):
        self.n = n
        self.adj = adj
        self.stay = stay
        # live = greatest fixpoint of  L = { q : stay(q) or adj[q] & L }
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
        # reach[q] = locations reachable from q via edges within live
        # (q included), for live q; 0 for dead q (unused).
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


_STRUCT_CACHE: dict = {}


def structure(n: int, adj: tuple, stay: int) -> Structure:
    key = (n, adj, stay)
    s = _STRUCT_CACHE.get(key)
    if s is None:
        s = Structure(n, adj, stay)
        _STRUCT_CACHE[key] = s
    return s


class Model:
    __slots__ = ('s', 'val', 'full')

    def __init__(self, s: Structure, val: tuple):
        self.s = s
        self.val = val
        self.full = (1 << s.n) - 1

    def __repr__(self):
        s = self.s
        edges = [(i, j) for i in range(s.n) for j in range(s.n)
                 if (s.adj[i] >> j) & 1]
        stays = [q for q in range(s.n) if (s.stay >> q) & 1]
        vals = {chr(ord('a') + i): [q for q in range(s.n) if (m >> q) & 1]
                for i, m in enumerate(self.val)}
        return (f'Model(n={s.n}, edges={edges}, stay={stays}, '
                f'val={vals}, live={[q for q in range(s.n) if (s.live >> q) & 1]})')


def _sccs_with_walk(n: int, adj: tuple, sub: int) -> Iterator[int]:
    """SCCs (as bitmasks) of the subgraph induced on `sub` that contain
    at least one internal edge (nontrivial SCC or self-loop)."""
    if not sub:
        return
    # forward reachability within sub
    fwd = {}
    q = sub
    while q:
        v = (q & -q).bit_length() - 1
        q &= q - 1
        seen = 0
        frontier = adj[v] & sub
        while frontier & ~seen:
            seen |= frontier
            nxt = 0
            f = frontier
            while f:
                u = (f & -f).bit_length() - 1
                f &= f - 1
                nxt |= adj[u] & sub
            frontier = nxt & ~seen
        fwd[v] = seen  # strictly-forward closure (>= 1 step)
    done = 0
    q = sub
    while q:
        v = (q & -q).bit_length() - 1
        q &= q - 1
        if (done >> v) & 1:
            continue
        # SCC of v: mutual >=1-step reachability, v itself included if
        # it lies on a cycle
        scc = 1 << v
        rest = fwd[v] & sub & ~(1 << v)
        r = rest
        while r:
            u = (r & -r).bit_length() - 1
            r &= r - 1
            if (fwd[u] >> v) & 1:
                scc |= 1 << u
        has_walk = bool((fwd[v] >> v) & 1) or scc != (1 << v)
        # scc != singleton implies mutual reachability -> internal walk
        done |= scc
        if has_walk:
            yield scc


def denot(f, m: Model) -> int:
    """Denotation of state formula f in model m, as a bitmask."""
    k = f[0]
    if k == 'atom':
        return m.val[f[1]] if f[1] < len(m.val) else 0
    if k == 'top':
        return m.full
    if k == 'bot':
        return 0
    if k == 'not':
        return m.full & ~denot(f[1], m)
    if k == 'and':
        return denot(f[1], m) & denot(f[2], m)
    if k == 'or':
        return denot(f[1], m) | denot(f[2], m)
    s = m.s
    dead = m.full & ~s.live
    if k == 'pg':
        target = denot(f[1], m)
        out = dead
        for q in range(s.n):
            if (s.live >> q) & 1 and (s.reach[q] & ~target) == 0:
                out |= 1 << q
        return out
    if k == 'pst':
        # violation locations, per pair; a live q fails iff it reaches one
        bad = 0
        for rho, phi in f[1]:
            drho = denot(rho, m)
            dphi = denot(phi, m)
            sub = s.live & ~dphi
            w = 0
            for scc in _sccs_with_walk(s.n, s.adj, sub):
                if scc & drho:
                    w |= scc
            w |= sub & s.stay & drho
            if w:
                bad_i = 0
                for q in range(s.n):
                    if (s.live >> q) & 1 and (s.reach[q] & w):
                        bad_i |= 1 << q
                bad |= bad_i
        out = dead
        for q in range(s.n):
            if (s.live >> q) & 1 and not (bad >> q) & 1:
                out |= 1 << q
        return out
    raise ValueError(k)


# ---------------------------------------------------------------------------
# model enumeration / sampling

def exhaustive_models(n: int, k: int) -> Iterator[Model]:
    """All models with n locations and k atoms."""
    masks = range(1 << n)
    for adj in product(masks, repeat=n):
        for stay in masks:
            s = structure(n, tuple(adj), stay)
            for val in product(masks, repeat=k):
                yield Model(s, tuple(val))


def count_exhaustive(n: int, k: int) -> int:
    return (1 << n * n) * (1 << n) * (1 << n * k)


def random_model(n: int, k: int, rng: random.Random) -> Model:
    full = (1 << n) - 1
    # bias toward sparse-ish graphs: each edge present w.p. ~0.3
    adj = []
    for _ in range(n):
        mask = 0
        for j in range(n):
            if rng.random() < 0.3:
                mask |= 1 << j
        adj.append(mask)
    stay = 0
    for q in range(n):
        if rng.random() < 0.3:
            stay |= 1 << q
    s = structure(n, tuple(adj), stay)
    val = tuple(rng.randint(0, full) for _ in range(k))
    return Model(s, val)


# ---------------------------------------------------------------------------
# checking

class Counterexample:
    def __init__(self, model: Model, state: int, side: str):
        self.model = model
        self.state = state
        self.side = side  # 'lhs>rhs' or 'rhs>lhs'

    def __repr__(self):
        return f'CX(state={self.state}, {self.side}, {self.model!r})'


def _impl_fails(lhs, rhs, m: Model) -> int:
    return denot(lhs, m) & ~denot(rhs, m)


GammaFilter = list  # e.g. [('disjoint', 0, 1)]


def _gamma_ok(m: Model, gamma: Optional[GammaFilter]) -> bool:
    if not gamma:
        return True
    for g in gamma:
        if g[0] == 'disjoint':
            if m.val[g[1]] & m.val[g[2]]:
                return False
        elif g[0] == 'subset':
            if m.val[g[1]] & ~m.val[g[2]]:
                return False
        else:
            raise ValueError(g)
    return True


def find_countermodel(lhs, rhs, *, direction: str = 'impl',
                      gamma: Optional[GammaFilter] = None,
                      max_exhaustive_n: int = 3,
                      exhaustive_val_budget: int = 300_000,
                      random_rounds: int = 4000,
                      random_n: int = 6,
                      seed: int = 0) -> Optional[Counterexample]:
    """Search for a countermodel to  lhs <= rhs  (direction='impl') or to
    lhs == rhs (direction='equiv').  Returns None if none found within
    budget (NOT a proof of validity -- see README scope note)."""
    k = max(natoms(lhs), natoms(rhs), 1)

    def test(m: Model) -> Optional[Counterexample]:
        if not _gamma_ok(m, gamma):
            return None
        bad = _impl_fails(lhs, rhs, m)
        if bad:
            return Counterexample(m, (bad & -bad).bit_length() - 1, 'lhs>rhs')
        if direction == 'equiv':
            bad = _impl_fails(rhs, lhs, m)
            if bad:
                return Counterexample(m, (bad & -bad).bit_length() - 1,
                                      'rhs>lhs')
        return None

    # exhaustive phase
    for n in range(1, max_exhaustive_n + 1):
        if count_exhaustive(n, k) > exhaustive_val_budget:
            # graph-exhaustive, valuation-sampled fallback
            rng = random.Random(seed ^ (n << 16))
            full = (1 << n) - 1
            masks = range(1 << n)
            for adj in product(masks, repeat=n):
                for stay in masks:
                    s = structure(n, tuple(adj), stay)
                    for _ in range(8):
                        val = tuple(rng.randint(0, full) for _ in range(k))
                        cx = test(Model(s, val))
                        if cx:
                            return _shrink(cx, lhs, rhs, direction, gamma)
            continue
        for m in exhaustive_models(n, k):
            cx = test(m)
            if cx:
                return _shrink(cx, lhs, rhs, direction, gamma)
    # random phase
    rng = random.Random(seed)
    for _ in range(random_rounds):
        n = rng.randint(2, random_n)
        m = random_model(n, k, rng)
        cx = test(m)
        if cx:
            return _shrink(cx, lhs, rhs, direction, gamma)
    return None


def _still_fails(m: Model, state: int, lhs, rhs, side, gamma) -> bool:
    if not _gamma_ok(m, gamma):
        return False
    a, b = (lhs, rhs) if side == 'lhs>rhs' else (rhs, lhs)
    return bool(_impl_fails(a, b, m) >> state & 1)


def _shrink(cx: Counterexample, lhs, rhs, direction, gamma) -> Counterexample:
    """Greedy minimization: clear edge/stay/val bits while the same state
    still witnesses the same failure direction."""
    m, state, side = cx.model, cx.state, cx.side
    changed = True
    while changed:
        changed = False
        s = m.s
        # edges
        for i in range(s.n):
            a = s.adj[i]
            while a:
                bit = a & -a
                a &= a - 1
                adj2 = list(s.adj)
                adj2[i] = s.adj[i] & ~bit
                m2 = Model(structure(s.n, tuple(adj2), s.stay), m.val)
                if _still_fails(m2, state, lhs, rhs, side, gamma):
                    m = m2
                    s = m.s
                    changed = True
        # stay bits
        st = s.stay
        while st:
            bit = st & -st
            st &= st - 1
            m2 = Model(structure(s.n, s.adj, s.stay & ~bit), m.val)
            if _still_fails(m2, state, lhs, rhs, side, gamma):
                m = m2
                s = m.s
                changed = True
        # valuation bits
        for i in range(len(m.val)):
            v = m.val[i]
            while v:
                bit = v & -v
                v &= v - 1
                val2 = list(m.val)
                val2[i] = m.val[i] & ~bit
                m2 = Model(s, tuple(val2))
                if _still_fails(m2, state, lhs, rhs, side, gamma):
                    m = m2
                    changed = True
    return Counterexample(m, state, side)


# ---------------------------------------------------------------------------
# the battery: machine-check the recorded deadline-free rows

A, B, C = atom(0), atom(1), atom(2)


def battery_rows():
    """(row id, lhs, rhs, direction, expectation, note)
    expectation 'valid'      -> no countermodel should exist
    expectation 'refutable'  -> a countermodel SHOULD be found
    """
    rows = [
        ('EQ-G2', pg(f_and(A, B)), f_and(pg(A), pg(B)), 'equiv', 'valid',
         'G-conjunction split, both directions'),
        ('EQ-G3', pg(A), pg(pg(A)), 'equiv', 'valid',
         'idempotence, both directions'),
        ('EQ-G4', pg(A), f_or(A, DEAD), 'impl', 'valid',
         'quasi-reflexivity with the D disjunct'),
        ('EQ-G4-noD', pg(A), A, 'impl', 'refutable',
         'T without D: dead-state witness proves the disjunct necessary'),
        ('EQ-G5a', DEAD, pg(A), 'impl', 'valid', 'vacuity: D below any AG'),
        ('EQ-G5b', DEAD, pst([(A, BOT)]), 'impl', 'valid',
         'vacuity: D below any ASt'),
        ('EQ-G6', f_not(DEAD), pg(f_not(DEAD)), 'impl', 'valid',
         'liveness invariance'),
        ('EQ-G6-conv', pg(f_not(DEAD)), f_not(DEAD), 'impl', 'refutable',
         'converse fails at dead states'),
        ('EQ-G7', f_or(pg(A), pg(B)), pg(f_or(A, B)), 'impl', 'valid',
         'disjunction half'),
        ('EQ-G7-conv', pg(f_or(A, B)), f_or(pg(A), pg(B)), 'impl',
         'refutable', 'two-trajectory split witness'),
        ('EQ-S1', pst([(A, B), (B, C)]), pst([(B, C), (A, B), (A, B)]),
         'equiv', 'valid', 'pair multiset invariance (permute+dup)'),
        ('EQ-S2', pst([(A, B), (B, C)]),
         f_and(pst([(A, B)]), pst([(B, C)])), 'equiv', 'valid',
         'bundle split, both directions'),
        ('EQ-S3', pst([(f_or(A, B), C)]), pst([(A, C), (B, C)]),
         'equiv', 'valid', 'request-disjunction split, both directions'),
        ('EQ-S4', pst([(A, f_and(C, B))]), pst([(f_and(A, B), C)]),
         'impl', 'valid',
         'pair monotonicity instance: request shrink + response grow'),
        ('EQ-S5a', pst([(BOT, A), (B, C)]), pst([(B, C)]), 'equiv',
         'valid', 'bot-request pair drops'),
        ('EQ-S5b', pst([(A, TOP), (B, C)]), pst([(B, C)]), 'equiv',
         'valid', 'top-response pair drops'),
        ('EQ-S5c', pst([]), TOP, 'equiv', 'valid', 'empty bundle is top'),
        ('EQ-S6', pst([(A, f_and(B, C))]), pst([(A, B), (A, C)]),
         'impl', 'valid', 'response-conjunction half'),
        ('EQ-S6-conv', pst([(A, B), (A, C)]), pst([(A, f_and(B, C))]),
         'impl', 'refutable', 'alternation witness'),
        ('EQ-S7', f_and(pg(A), pst([(B, f_and(C, A))])),
         f_and(pg(A), pst([(B, C)])), 'equiv', 'valid',
         'invariant relativization of responses, both directions'),
        ('EQ-S7r', f_and(pg(A), pst([(f_and(B, A), C)])),
         f_and(pg(A), pst([(B, C)])), 'equiv', 'valid',
         'invariant relativization of requests, both directions'),
        ('EQ-S8', pst([(pst([(TOP, A)]), A), (B, C)]), pst([(B, C)]),
         'equiv', 'valid',
         'self-fulfilling request drops (oracle-corpus discovery)'),
        ('EQ-S8-tight', pst([(pst([(TOP, A)]), f_and(A, B))]), TOP,
         'equiv', 'refutable',
         'the response must be the request-recurred one: (AGFa, a&b) '
         'pair is NOT free'),
        # --- canonical-lens harvest (found by asking which frame
        # conditions the canonical model will need; proofs in the
        # development record) ---
        ('EQ-S9', pst([(A, B)]), pg(pst([(A, B)])), 'equiv', 'valid',
         'Streett obligations are reachability-invariant: '
         'ASt(P) == AG[ASt(P)] (fusion ->; B1+vacuity <-)'),
        ('EQ-S9-tight', pst([(TOP, A)]), pg(A), 'impl', 'refutable',
         'recurrence is not invariance: cycle witness expected'),
        ('EQ-S10', pst([(TOP, pst([(A, B)]))]), pst([(A, B)]), 'equiv',
         'valid',
         'fixpoint collapse: recurrently visiting a St-guaranteeing '
         'region == St (tail ->; S9+S11 chain <-)'),
        ('EQ-S11', pg(B), pst([(A, B)]), 'impl', 'valid',
         'G-to-Streett bridge: invariant response satisfies any pair '
         '(derivable from EQ-S7+EQ-S5; confirmed semantically here)'),
        ('EQ-S11-conv', pst([(A, B)]), pg(B), 'impl', 'refutable',
         'bridge converse fails: satisfying a pair without invariance'),
        # --- GF-rung harvest (proofs in the development record; both
        # are basis material for the GF-rung completeness proof) ---
        ('EQ-S12', pst([(TOP, BOT), (A, B)]), DEAD, 'equiv', 'valid',
         'falsum pair collapses the whole bundle to deadness: '
         'ASt[(T,F)::R] == D (tail never votes)'),
        ('EQ-S13', pst([(TOP, f_or(A, pst([(TOP, A)])))]), pst([(TOP, A)]),
         'equiv', 'valid',
         'eventuality absorption: AGF(a | AGF a) == AGF a '
         '(Park-induction shadow; B2 tail argument)'),
        # --- general-bundle harvest (proofs in the development
        # record; basis material for the full deadline-free
        # completeness proof) ---
        ('EQ-S14', pst([(A, A), (B, C)]), pst([(B, C)]), 'equiv', 'valid',
         'pair reflexivity: a reflexive pair drops from any bundle '
         '(pathwise Cof tautology; NEW basis material)'),
        ('EQ-S15', f_and(pst([(A, f_or(C, B))]), pst([(B, C)])),
         pst([(A, C)]), 'impl', 'valid',
         'the Streett cut: (a,c|b) and (b,c) yield (a,c) '
         '(pathwise pigeonhole + second pair; NEW basis material)'),
        ('EQ-S15-conv', pst([(A, C)]),
         f_and(pst([(A, f_or(C, B))]), pst([(B, C)])), 'impl', 'refutable',
         'cut converse control: (a,c) does not yield the (b,c) premise'),
        ('EQ-S13r', pst([(A, f_or(B, pst([(A, B)])))]), pst([(A, B)]),
         'equiv', 'valid',
         'relativized eventuality absorption: (a, b|ASt[(a,b)]) == '
         '(a,b); rho=T instance is EQ-S13'),
        ('EQ-S13r-wrongreq', TOP, pst([(pst([(A, B)]), B)]), 'impl',
         'refutable',
         'request ASt[(a,b)] with response b is NOT free (contrast '
         'EQ-S8): conditional pairs need not self-deliver'),
        ('GATE', pg(impl(A, B)), pst([(A, B)]), 'impl', 'valid',
         'request gating AG[a->b] <= ASt[(a,b)] (derived: '
         'S14 + S4 + S7req; the canonical constructions lean on it)'),
    ]
    return rows


def gamma_rows():
    """Class-flag necessity demos: laws valid over C_cont, hunted here
    over C_cd models (jumps allowed) with their Gamma side conditions
    enforced -- a countermodel is the EXPECTED outcome and is the
    machine-checked witness that the continuity flag is load-bearing."""
    return [
        ('EQ-C1-cd', f_and(pg(f_or(A, B)), A), pg(A), 'impl',
         [('disjoint', 0, 1)], 'refutable',
         'component invariance needs continuity: jump witness expected'),
    ]


# ---------------------------------------------------------------------------
# metamorphic self-checks

def random_formula(rng: random.Random, depth: int, k: int = 2):
    if depth == 0:
        r = rng.random()
        if r < 0.7:
            return atom(rng.randrange(k))
        return TOP if r < 0.85 else BOT
    r = rng.random()
    if r < 0.2:
        return f_not(random_formula(rng, depth - 1, k))
    if r < 0.4:
        return f_and(random_formula(rng, depth - 1, k),
                     random_formula(rng, depth - 1, k))
    if r < 0.6:
        return f_or(random_formula(rng, depth - 1, k),
                    random_formula(rng, depth - 1, k))
    if r < 0.8:
        return pg(random_formula(rng, depth - 1, k))
    pairs = [(random_formula(rng, depth - 1, k),
              random_formula(rng, depth - 1, k))
             for _ in range(rng.randint(1, 2))]
    return pst(pairs)


def _permute_pst(f, rng: random.Random):
    k = f[0]
    if k in ('atom', 'top', 'bot'):
        return f
    if k == 'not':
        return ('not', _permute_pst(f[1], rng))
    if k in ('and', 'or'):
        return (k, _permute_pst(f[1], rng), _permute_pst(f[2], rng))
    if k == 'pg':
        return ('pg', _permute_pst(f[1], rng))
    if k == 'pst':
        pairs = [( _permute_pst(r, rng), _permute_pst(p, rng))
                 for r, p in f[1]]
        rng.shuffle(pairs)
        if pairs and rng.random() < 0.5:
            pairs.append(pairs[rng.randrange(len(pairs))])  # duplicate
        return pst(pairs)
    raise ValueError(k)


def metamorphic_check(rounds: int, seed: int) -> list:
    """Pair permutation + duplication must never change any denotation."""
    rng = random.Random(seed)
    failures = []
    for _ in range(rounds):
        n = rng.randint(1, 5)
        m = random_model(n, 2, rng)
        f = random_formula(rng, rng.randint(1, 3))
        g = _permute_pst(f, rng)
        if denot(f, m) != denot(g, m):
            failures.append((f, g, m))
    return failures


# ---------------------------------------------------------------------------
# corpus generation (for derivability measurements)

def corpus(pairs: int, seed: int):
    """Random candidate equivalences bucketed refuted / apparently-valid.
    Apparently-valid pairs are the successor's derivability corpus."""
    rng = random.Random(seed)
    seen = set()
    refuted, apparent = [], []
    attempts = 0
    while len(refuted) + len(apparent) < pairs and attempts < pairs * 60:
        attempts += 1
        f = random_formula(rng, 2)
        g = random_formula(rng, 2)
        if f == g:
            continue
        key = (f, g)
        if key in seen:
            continue
        seen.add(key)
        # skip pairs trivially separated at the propositional level by a
        # 1-state live model probe (cheap prefilter)
        cx = find_countermodel(f, g, direction='equiv',
                               max_exhaustive_n=2,
                               random_rounds=400, seed=seed ^ attempts)
        if cx:
            refuted.append((f, g, cx))
        else:
            cx = find_countermodel(f, g, direction='equiv',
                                   max_exhaustive_n=3,
                                   random_rounds=1500,
                                   seed=seed ^ attempts ^ 0xBEEF)
            if cx:
                refuted.append((f, g, cx))
            else:
                apparent.append((f, g))
    return refuted, apparent


# ---------------------------------------------------------------------------
# main

def run_battery(out, quick: bool):
    max_n = 2 if quick else 3
    print('# oracle battery -- deadline-free rows, '
          f'exhaustive n<={max_n} + random phase', file=out)
    print(file=out)
    ok = True
    for row_id, lhs, rhs, direction, expect, note in battery_rows():
        cx = find_countermodel(lhs, rhs, direction=direction,
                               max_exhaustive_n=max_n, seed=42)
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
    print('## class-flag necessity demos (Gamma-filtered)', file=out)
    for row_id, lhs, rhs, direction, gamma, expect, note in gamma_rows():
        cx = find_countermodel(lhs, rhs, direction=direction, gamma=gamma,
                               max_exhaustive_n=max_n, seed=42)
        got = cx is not None
        want = expect == 'refutable'
        verdict = (f'countermodel found as expected: {cx!r}' if got and want
                   else 'CONFIRMED (no countermodel)' if not got and not want
                   else f'!! unexpected outcome: cx={cx!r}')
        if got != want:
            ok = False
        print(f'- **{row_id}** ({note}): {verdict}', file=out)
    print(file=out)
    print('## metamorphic self-checks', file=out)
    fails = metamorphic_check(rounds=100 if quick else 400, seed=7)
    if fails:
        ok = False
        print(f'- !! pair-permutation invariance FAILED {len(fails)} times; '
              f'first: {fails[0]!r}', file=out)
    else:
        print('- pair permutation/duplication invariance: '
              'CONFIRMED on all rounds', file=out)
    print(file=out)
    print(f'battery overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


def run_corpus(out, pairs: int, seed: int):
    refuted, apparent = corpus(pairs, seed)
    print(f'# oracle corpus -- {len(refuted)} refuted, '
          f'{len(apparent)} apparently-valid (seed={seed})', file=out)
    print(file=out)
    print('## apparently-valid candidate equivalences '
          '(the derivability corpus for the successor)', file=out)
    for f, g, in apparent:
        print(f'- `{show(f)}`  ==  `{show(g)}`', file=out)
    print(file=out)
    print('## sample refuted candidates (first 10, shrunk)', file=out)
    for f, g, cx in refuted[:10]:
        print(f'- `{show(f)}`  vs  `{show(g)}` -- {cx!r}', file=out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest='cmd', required=True)
    b = sub.add_parser('battery', help='machine-check the recorded rows')
    b.add_argument('--quick', action='store_true')
    b.add_argument('--out', default='-')
    c = sub.add_parser('corpus', help='generate a validity corpus')
    c.add_argument('--pairs', type=int, default=40)
    c.add_argument('--seed', type=int, default=2026)
    c.add_argument('--out', default='-')
    args = ap.parse_args()
    out = sys.stdout if args.out == '-' else open(args.out, 'w')
    try:
        if args.cmd == 'battery':
            ok = run_battery(out, args.quick)
            sys.exit(0 if ok else 1)
        else:
            run_corpus(out, args.pairs, args.seed)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == '__main__':
    main()
