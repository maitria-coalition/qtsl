#!/usr/bin/env python3
r"""F-fragment small-model sweep.

The empirical phase, run BEFORE the canonical-model proof: test the
small-model conjecture for the F-fragment (atoms,
Booleans, P>=1[G .], P>=1[F<=T .]) over clocked models.

Seed conjecture: countermodels with O(|Sigma|)
locations and dwell denominators dividing the formula's deadline lcm.

What this instrument measures, per refuted corpus pair:
  - n_min: minimal location count (exact for n <= 2 via exhaustive
    search; lower-bounded otherwise);
  - gran: the coarsest dwell granularity (as a multiple of the pair's
    deadline-denominator lcm base) at which a countermodel exists,
    searched along a refinement ladder at each n;
  - the witness clock's denominator.

`forced` subcommand: the DISJOINTNESS-FORCED grain family

    S_k: [ /\_i (~a_i & AF<=1[a_i]) & PG[ /\_{i<j} ~(a_i & a_j) ] ] -> D

kills the corrected small-model conjecture (both branches). The
box closes the bipartition escape (G3 lived on valuation overlap),
so every trajectory must service k pairwise-disjoint obligations
SEQUENTIALLY inside one unit window: with min finite dwell 1/m the
k-th service happens at time > (k-1)/m, so k > m is unsatisfiable
at live states (Lemma SEQ, development record -- covers
ALL location counts and all menus; the searches below are
falsification-armed corroboration, not the certificate), while the
1/k-chain (and, for k = 3, the dyadic (1/4,1/4,1/2)-chain) refutes
S_k whenever the grid admits k positive dwells summing <= 1, i.e.
m >= k. Consequences, proved in the development record: countermodel
granularity is NOT bounded by c*G for any constant c (S_k has G = 1,
nesting depth 1, and needs denominator >= k) -- both live hypotheses
(c = 2, c = 2^depth) fall, and the grid must scale with the number
of graded subformulas.

`grain` subcommand: the hand-built separation specimen

    L_grain: (~a & ~b & AF<=1[a] & AF<=1[b]) -> AF<=1[(a&b)]

is VALID over clocked models with integer dwells (anchor-integrality:
with clock-blind atom targets, worst-case-debut anchors A(q, 0) are
sums of dwell bounds, hence integers-or-oo; the refutation shape
forces a successor anchor strictly between 0 and 1 -- proof in
the development record) yet REFUTED by a half-dwell chain
(u = 1/2, 1/2, oo). Its only deadline is 1 (lcm base 1), so the seed
conjecture's granularity half is false: deadline-lcm dwells do not
suffice. The width-k generalization does NOT escalate the denominator
past 2, though -- a mid-flight self-catch: k = 3 falls at
denominator 2 once valuations overlap (the (iv) bipartition witness),
so the proved facts are exactly [m = 1 insufficient, every k >= 2]
and [m = 2 sufficient for this family at small k]; the sharp
granularity law for the whole fragment is open and belongs to the
canonical-model construction. The subcommand asserts the explicit
1/k-chain witnesses, integer-menu silence, and the k = 3
denominator-2 bipartition witness.

Python as orchestration/check-scale code (oracle.py module
docstring).
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction
from itertools import product
from math import gcd, ceil

from oracle import TOP, BOT, atom, f_not, f_and, f_or, pg, impl, DEAD
from timed import (INF, TModel, tstructure, tdenot, pfle, tshow,
                        tnatoms, exhaustive_tmodels, random_tmodel,
                        _fails, _witness_point)

ONE = Fraction(1)


# ---------------------------------------------------------------------------
# F-fragment formula generation

F_T_MENU = (Fraction(1, 2), ONE, Fraction(3, 2), Fraction(2))


def random_f_formula(rng: random.Random, depth: int, k: int = 2,
                     tmenu=F_T_MENU):
    if depth == 0:
        r = rng.random()
        if r < 0.75:
            return atom(rng.randrange(k))
        return TOP if r < 0.9 else BOT
    r = rng.random()
    if r < 0.18:
        return f_not(random_f_formula(rng, depth - 1, k, tmenu))
    if r < 0.36:
        return f_and(random_f_formula(rng, depth - 1, k, tmenu),
                     random_f_formula(rng, depth - 1, k, tmenu))
    if r < 0.54:
        return f_or(random_f_formula(rng, depth - 1, k, tmenu),
                    random_f_formula(rng, depth - 1, k, tmenu))
    if r < 0.72:
        return pg(random_f_formula(rng, depth - 1, k, tmenu))
    return pfle(rng.choice(tmenu), random_f_formula(rng, depth - 1, k, tmenu))


def deadlines(f) -> list:
    k = f[0]
    if k == 'pfle':
        return [f[1]] + deadlines(f[2])
    if k in ('atom', 'top', 'bot'):
        return []
    if k in ('not', 'pg'):
        return deadlines(f[1])
    if k in ('and', 'or'):
        return deadlines(f[1]) + deadlines(f[2])
    raise ValueError(k)


def horizon(f) -> Fraction:
    """Nested deadline sum -- the formula's relevant time window."""
    k = f[0]
    if k == 'pfle':
        return f[1] + horizon(f[2])
    if k in ('atom', 'top', 'bot'):
        return Fraction(0)
    if k in ('not', 'pg'):
        return horizon(f[1])
    if k in ('and', 'or'):
        return max(horizon(f[1]), horizon(f[2]))
    raise ValueError(k)


def fsize(f) -> int:
    k = f[0]
    if k in ('atom', 'top', 'bot'):
        return 1
    if k in ('not', 'pg'):
        return 1 + fsize(f[1])
    if k == 'pfle':
        return 1 + fsize(f[2])
    if k in ('and', 'or'):
        return 1 + fsize(f[1]) + fsize(f[2])
    raise ValueError(k)


def lcm_base(pair_deadlines) -> int:
    """lcm of deadline denominators: the seed conjecture's granularity."""
    g = 1
    for t in pair_deadlines:
        g = g * t.denominator // gcd(g, t.denominator)
    return g


# ---------------------------------------------------------------------------
# propositional-skeleton tautology filter (obligation R6, first tooth)

def _skeleton(f, table: dict):
    """Replace maximal modal subformulas by fresh propositional vars."""
    k = f[0]
    if k in ('pg', 'pfle'):
        key = f
        if key not in table:
            table[key] = len(table)
        return ('var', table[key])
    if k == 'atom':
        key = ('atom', f[1])
        if key not in table:
            table[key] = len(table)
        return ('var', table[key])
    if k in ('top', 'bot'):
        return f
    if k == 'not':
        return ('not', _skeleton(f[1], table))
    if k in ('and', 'or'):
        return (k, _skeleton(f[1], table), _skeleton(f[2], table))
    raise ValueError(k)


def _eval_skel(f, bits: int) -> bool:
    k = f[0]
    if k == 'var':
        return bool((bits >> f[1]) & 1)
    if k == 'top':
        return True
    if k == 'bot':
        return False
    if k == 'not':
        return not _eval_skel(f[1], bits)
    if k == 'and':
        return _eval_skel(f[1], bits) and _eval_skel(f[2], bits)
    if k == 'or':
        return _eval_skel(f[1], bits) or _eval_skel(f[2], bits)
    raise ValueError(k)


def skeleton_equivalent(f, g) -> bool:
    """True if f == g holds already at the propositional skeleton level
    (the tautology-in-costume class an early corpus let through)."""
    table: dict = {}
    sf, sg = _skeleton(f, table), _skeleton(g, table)
    nv = len(table)
    if nv > 16:
        return False  # cap; treat as non-trivial
    for bits in range(1 << nv):
        if _eval_skel(sf, bits) != _eval_skel(sg, bits):
            return False
    return True


# ---------------------------------------------------------------------------
# menu-parametrized countermodel search (sweep-local; qtsl_timed's
# find_t_countermodel hardcodes its menus, and the sweep's whole point
# is menu control)

def menu_for(gran: int, cap: Fraction):
    """Dwell menu: multiples of 1/gran up to cap, plus INF."""
    top = max(1, ceil(cap))
    vals = [Fraction(i, gran) for i in range(1, top * gran + 1)]
    return tuple(vals) + (INF,)


def search_menu(lhs, rhs, direction, n_lo, n_hi, menu, k,
                exhaustive_max_n=2, random_rounds=1200, seed=7):
    """Countermodel search restricted to location counts [n_lo, n_hi]
    and the given dwell menu. Exhaustive for n <= exhaustive_max_n
    (menu permitting), random beyond. Returns (n, TModel, q, c) or
    None. The exhaustive tier is a real minimality certificate at its
    sizes; the random tier is evidence only."""

    def test(tm):
        ld, rd = tdenot(lhs, tm), tdenot(rhs, tm)
        w = _fails(ld, rd, tm)
        if w:
            return w
        if direction == 'equiv':
            w = _fails(rd, ld, tm)
            if w:
                return w
        return None

    for n in range(n_lo, min(n_hi, exhaustive_max_n) + 1):
        for tm in exhaustive_tmodels(n, k, umenu=menu):
            w = test(tm)
            if w:
                return (n, tm, w[0], w[1])
    if n_hi > exhaustive_max_n:
        rng = random.Random(seed)
        for _ in range(random_rounds):
            n = rng.randint(max(n_lo, exhaustive_max_n + 1), n_hi)
            tm = random_tmodel(n, k, rng, umenu=menu)
            w = test(tm)
            if w:
                return (n, tm, w[0], w[1])
    return None


GRAN_LADDER = (1, 2, 3, 4, 6)


def minimize(lhs, rhs, direction, base: int, cap: Fraction, k: int):
    """Minimality profile of a refuted pair: smallest n, and at that n
    the coarsest granularity on the ladder (multiples of the deadline
    lcm base). Returns dict or None if even the finest ladder rung at
    n <= 4 misses (itself cargo: the pair needed the wild random menu)."""
    for n in (1, 2, 3, 4):
        for mult in GRAN_LADDER:
            gran = base * mult
            menu = menu_for(gran, cap + 1)
            hit = search_menu(lhs, rhs, direction, n, n, menu, k,
                              exhaustive_max_n=2,
                              random_rounds=900, seed=101 * n + mult)
            if hit:
                nn, tm, q, c = hit
                return {'n': nn, 'exact_n': nn <= 2, 'mult': mult,
                        'gran': gran, 'clock_den': c.denominator,
                        'model': tm, 'q': q, 'c': c}
    return None


# ---------------------------------------------------------------------------
# the sweep

def sweep(pairs: int, seed: int, out):
    rng = random.Random(seed)
    seen = set()
    rows = []
    apparent = []
    skel_filtered = 0
    attempts = 0
    while len(rows) + len(apparent) < pairs and attempts < pairs * 80:
        attempts += 1
        f = random_f_formula(rng, rng.randint(1, 3))
        g = random_f_formula(rng, rng.randint(1, 3))
        if f == g or (f, g) in seen:
            continue
        seen.add((f, g))
        if not deadlines(f) and not deadlines(g):
            continue  # the sweep is about the timed layer
        if skeleton_equivalent(f, g):
            skel_filtered += 1
            continue
        cx = search_menu(f, g, 'equiv', 1, 4,
                         menu_for(6, horizon(f) + horizon(g) + 1),
                         max(tnatoms(f), tnatoms(g), 1),
                         exhaustive_max_n=2, random_rounds=900,
                         seed=seed ^ attempts)
        base = lcm_base(deadlines(f) + deadlines(g))
        cap = max(horizon(f), horizon(g), ONE)
        if cx is None:
            apparent.append((f, g))
            continue
        prof = minimize(f, g, 'equiv', base,
                        cap, max(tnatoms(f), tnatoms(g), 1))
        rows.append((f, g, base, cap, prof))

    print(f'# F-fragment small-model sweep (seed={seed})',
          file=out)
    print(file=out)
    print(f'- corpus: {len(rows)} refuted pairs profiled, '
          f'{len(apparent)} apparently-valid, '
          f'{skel_filtered} filtered as propositional-skeleton '
          'tautologies (the R6 filter, first tooth)', file=out)
    print(file=out)
    print('## minimality profiles of refuted pairs', file=out)
    print(file=out)
    print('| pair | size | lcm base | n_min | n exact? | gran mult | '
          'clock den |', file=out)
    print('|---|---|---|---|---|---|---|', file=out)
    over_base = 0
    for f, g, base, cap, prof in rows:
        sz = fsize(f) + fsize(g)
        if prof is None:
            print(f'| `{tshow(f)}` vs `{tshow(g)}` | {sz} | {base} | '
                  '>4 or finer-than-ladder | -- | MISS | -- |', file=out)
            continue
        if prof['mult'] > 1:
            over_base += 1
        print(f'| `{tshow(f)}` vs `{tshow(g)}` | {sz} | {base} | '
              f"{prof['n']} | {'yes' if prof['exact_n'] else 'no (random)'} | "
              f"x{prof['mult']} | {prof['clock_den']} |", file=out)
    print(file=out)
    print(f'- pairs needing granularity strictly finer than the '
          f'deadline lcm: **{over_base}** of {len(rows)}', file=out)
    print('- (the hand specimen L_grain, `grain` subcommand, shows the '
          'finer-than-lcm class is nonempty by construction; the sweep '
          'measures how often random pairs land in it)', file=out)
    print(file=out)
    print('## apparently-valid candidates (post-filter)', file=out)
    for f, g in apparent:
        print(f'- `{tshow(f)}`  ==  `{tshow(g)}`', file=out)
    return rows, apparent


# ---------------------------------------------------------------------------
# the grain specimen: seed-conjecture refutation, both directions armed

A, B = atom(0), atom(1)


def l_grain_lhs(k: int):
    """~a1 & ... & ~ak & AF<=1[a1] & ... & AF<=1[ak] for atoms a1..ak."""
    f = None
    for i in range(k):
        c = f_and(f_not(atom(i)), pfle(ONE, atom(i)))
        f = c if f is None else f_and(f, c)
    return f


def l_grain_rhs(k: int):
    """OR over pairs i<j of AF<=1[ai & aj]."""
    f = None
    for i in range(k):
        for j in range(i + 1, k):
            c = pfle(ONE, f_and(atom(i), atom(j)))
            f = c if f is None else f_or(f, c)
    return f


def grain_chain(k: int) -> TModel:
    """The 1/k-dwell chain: v0 -> w1 -> ... -> wk, u = 1/k on
    v0..w_{k-1}, wk stays; atom ai holds exactly at wi."""
    n = k + 1
    adj = tuple((1 << (q + 1)) if q < k else 0 for q in range(n))
    stay = 1 << k
    u = tuple(Fraction(1, k) if q < k else INF for q in range(n))
    s = tstructure(n, adj, stay, u)
    val = tuple(1 << (i + 1) for i in range(k))
    return TModel(s, val)


def run_grain(out) -> bool:
    ok = True
    print('# L_grain: the seed granularity conjecture, adjudicated',
          file=out)
    print(file=out)
    for k in (2, 3):
        lhs, rhs = l_grain_lhs(k), l_grain_rhs(k)
        print(f'## width k = {k}: `{tshow(lhs)} -> {tshow(rhs)}`',
              file=out)
        # (i) the explicit 1/k chain refutes it at (v0, 0)
        tm = grain_chain(k)
        ld, rd = tdenot(lhs, tm), tdenot(rhs, tm)
        w = _fails(ld, rd, tm)
        witness_ok = w is not None and w[0] == 0
        ok &= witness_ok
        print(f'- explicit 1/{k}-dwell chain refutes: '
              + ('CONFIRMED at (v0, '
                 f'{w[1]})' if witness_ok else '!! FAILED') + f' [{tm!r}]',
              file=out)
        # (ii) integer-menu silence -- the ONLY granularity with a
        # validity proof behind it (anchor-integrality covers m = 1;
        # a mid-flight self-catch removed the earlier overclaim
        # that silence at 1 < m < k was proof-backed: the k = 3
        # specimen IS refutable at m = 2 -- see (iv))
        hit = search_menu(lhs, rhs, 'impl', 1, k + 2,
                          menu_for(1, Fraction(k + 2)), k,
                          exhaustive_max_n=2, random_rounds=4000,
                          seed=500 + 10 * k + 1)
        silent = hit is None
        ok &= silent
        print(f'- integer (denominator-1) menu (exhaustive n<=2 + 4000 '
              f'random rounds n<={k + 2}): '
              + ('SILENT as the anchor-integrality proof predicts'
                 if silent else f'!! COUNTERMODEL {hit!r} -- '
                 'the hand proof is WRONG, investigate'), file=out)
        # informational: intermediate granularities (no proof either
        # way; search evidence only)
        for m in range(2, k):
            hit = search_menu(lhs, rhs, 'impl', 1, k + 2,
                              menu_for(m, Fraction(k + 2)), k,
                              exhaustive_max_n=2, random_rounds=4000,
                              seed=500 + 10 * k + m)
            print(f'- denominator-{m} menu (informational): '
                  + ('no countermodel in budget (NOT a validity claim; '
                     'the k=3 case has a hand-built m=2 witness the '
                     'random tier misses -- see (iv))' if hit is None
                     else f'countermodel found (n = {hit[0]})'), file=out)
        # (iii) informational: does generic search at denominator k
        # rediscover the witness class? (The explicit chain in (i) is
        # the certificate; a random-tier miss here is variance, not
        # evidence -- the chain shape is a measure-zero corner of the
        # random model distribution at n = k + 1.)
        hit = search_menu(lhs, rhs, 'impl', 1, k + 2,
                          menu_for(k, Fraction(k + 2)), k,
                          exhaustive_max_n=2, random_rounds=6000,
                          seed=700 + k)
        print(f'- denominator-{k} menu search (informational): '
              + (f'countermodel rediscovered (n = {hit[0]})'
                 if hit is not None
                 else 'random tier missed the chain shape; certificate '
                 'is the explicit witness in (i)'), file=out)
        print(file=out)
    # (iv) the bipartition witness: width does NOT force granularity
    # 1/k -- k = 3 falls at denominator 2 with 5 locations and
    # OVERLAPPING valuations (routes = bipartitions of the atom set;
    # each pairwise intersection avoided by the route that splits it).
    # Self-catch: this refutes the natural "denominator grows
    # linearly with width" reading; the proved facts are only
    # m = 1 insufficient (anchor-integrality) and m = 2 sufficient for
    # the L_grain family at k <= 4 (constructions); sharp granularity
    # for the full fragment is the canonical-model question.
    print('## (iv) bipartition witness: k = 3 at denominator 2', file=out)
    H2 = Fraction(1, 2)
    adj = (0b00110, 0b10000, 0b01000, 0, 0)
    stay = 0b11000
    u = (H2, H2, H2, INF, INF)
    s = tstructure(5, adj, stay, u)
    val = (0b00110, 0b01010, 0b11000)  # a={w1,wa} b={w1,w3} c={w3,wc}
    tm = TModel(s, val)
    lhs3, rhs3 = l_grain_lhs(3), l_grain_rhs(3)
    diff = tdenot(lhs3, tm)[0].minus(tdenot(rhs3, tm)[0], u[0])
    got = not diff.is_empty()
    ok &= got
    print(f'- explicit 5-location half-dwell model [{tm!r}]: '
          + (f'REFUTES k=3 L_grain at (v, c) for c in {diff} -- '
             'width pressure collapses under valuation overlap'
             if got else '!! failed to refute -- construction wrong'),
          file=out)
    print(file=out)
    print(f'grain overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


# ---------------------------------------------------------------------------
# the disjointness-forced family (the `forced` subcommand)

def pairwise_disjoint_box(k: int):
    r"""PG[ /\_{i<j} ~(a_i & a_j) ]."""
    dis = None
    for i in range(k):
        for j in range(i + 1, k):
            d = f_not(f_and(atom(i), atom(j)))
            dis = d if dis is None else f_and(dis, d)
    return pg(dis)


def s_forced_ante(k: int):
    r"""/\_i (~a_i & AF<=1[a_i])  &  PG[pairwise disjointness]."""
    return f_and(l_grain_lhs(k), pairwise_disjoint_box(k))


def forced_chain(k: int, us) -> TModel:
    """v0 -> w1 -> ... -> wk; dwell bounds us[q] on v0..w_{k-1} (len k),
    wk stays; atom a_i exactly at w_i (pairwise disjoint by shape)."""
    n = k + 1
    adj = tuple((1 << (q + 1)) if q < k else 0 for q in range(n))
    stay = 1 << k
    u = tuple(us[q] if q < k else INF for q in range(n))
    s = tstructure(n, adj, stay, u)
    val = tuple(1 << (i + 1) for i in range(k))
    return TModel(s, val)


def _refutes_at_v0(ante, tm: TModel):
    """(True, c) if the model has a live state at location 0 satisfying
    `ante` (i.e. refuting ante -> D there); else (False, None)."""
    ld, dd = tdenot(ante, tm), tdenot(DEAD, tm)
    diff = ld[0].minus(dd[0], tm.s.u[0])
    if diff.is_empty():
        return False, None
    return True, _witness_point(diff)


def _silent(ante, k, m, *, exhaustive, rounds, seed, n_hi=6):
    """Countermodel search for ante -> D over the denominator-m menu.
    Returns None if silent, else the hit tuple."""
    return search_menu(ante, DEAD, 'impl', 1, n_hi, menu_for(m, Fraction(2)),
                       k, exhaustive_max_n=(2 if exhaustive else 0),
                       random_rounds=rounds, seed=seed)


TOWER_PROBES = ()  # filled below, after the constructors exist


def _tower_probes():
    a, b, c = atom(0), atom(1), atom(2)
    neg_abc = f_and(f_and(f_not(a), f_not(b)), f_not(c))
    box3 = pairwise_disjoint_box(3)
    # T2 -- cascade: outer service a (with inner service c), parallel b
    t2 = f_and(f_and(neg_abc, box3),
               f_and(pfle(ONE, f_and(a, pfle(ONE, c))), pfle(ONE, b)))
    # T3 -- width-2 inside the cascaded window
    inner3 = f_and(f_and(f_not(b), f_not(c)),
                   f_and(pfle(ONE, b), pfle(ONE, c)))
    t3 = f_and(f_and(neg_abc, box3), pfle(ONE, f_and(a, inner3)))
    # T4 -- shared outer window (2 services) + cascaded inner service
    t4 = f_and(f_and(neg_abc, box3),
               f_and(f_and(pfle(ONE, f_and(a, pfle(ONE, c))),
                           pfle(ONE, b)),
                     pfle(ONE, a)))
    return (('T2 cascade a>(c) || b', 'projected (alpha)', t2),
            ('T3 width-2 inside cascade', 'descent (beta)', t3),
            ('T4 shared window + cascade', 'projected (alpha)', t4))


def run_forced(out) -> bool:
    ok = True
    print('# S_k: the disjointness-forced grain family '
          '(the corrected conjecture, adjudicated)', file=out)
    print(file=out)
    print('Certificate structure: refutations are explicit witness models '
          '(machine-checked here); silences are hand-proved for ALL '
          'location counts and menus (Lemma SEQ, development record) -- the '
          'searches corroborate and would FALSIFY the proof if they hit.',
          file=out)
    print(file=out)

    # -- k = 2 (control: the mechanism starts at k = m + 1)
    ante2 = s_forced_ante(2)
    print(f'## k = 2: `{tshow(ante2)} -> D`', file=out)
    got, c = _refutes_at_v0(ante2, forced_chain(2, (Fraction(1, 2),) * 2))
    ok &= got
    print(f'- (1/2,1/2)-chain refutes at denominator 2: '
          + (f'CONFIRMED at (v0, {c})' if got else '!! FAILED'), file=out)
    hit = _silent(ante2, 2, 1, exhaustive=True, rounds=2500, seed=801)
    ok &= hit is None
    print('- denominator-1 menu (exhaustive n<=2 + 2500 random n<=6): '
          + ('SILENT as Lemma SEQ proves (k=2 needs m>=2)'
             if hit is None else f'!! COUNTERMODEL {hit!r} -- SEQ WRONG'),
          file=out)
    print(file=out)

    # -- k = 3 (the conjecture-killer)
    ante3 = s_forced_ante(3)
    print(f'## k = 3: `{tshow(ante3)} -> D`', file=out)
    got, c = _refutes_at_v0(ante3, forced_chain(3, (Fraction(1, 3),) * 3))
    ok &= got
    print(f'- (1/3,1/3,1/3)-chain refutes at denominator 3: '
          + (f'CONFIRMED at (v0, {c})' if got else '!! FAILED'), file=out)
    got, c = _refutes_at_v0(
        ante3, forced_chain(3, (Fraction(1, 4), Fraction(1, 4),
                                Fraction(1, 2))))
    ok &= got
    print(f'- DYADIC (1/4,1/4,1/2)-chain refutes at denominator 4: '
          + (f'CONFIRMED at (v0, {c})' if got else '!! FAILED')
          + ' -- the obstruction is min-dwell <= 1/3-ish room, not parity',
          file=out)
    for m in (1, 2):
        hit = _silent(ante3, 3, m, exhaustive=True, rounds=2500,
                      seed=810 + m)
        ok &= hit is None
        print(f'- denominator-{m} menu (exhaustive n<=2 + 2500 random '
              'n<=6): '
              + ('SILENT as Lemma SEQ proves (k=3 needs m>=3)'
                 if hit is None
                 else f'!! COUNTERMODEL {hit!r} -- SEQ WRONG'), file=out)
    # the box-off contrast: G3's bipartition model refutes the BOXLESS
    # width-3 grain at denominator 2, but does not touch S_3
    H2 = Fraction(1, 2)
    adj = (0b00110, 0b10000, 0b01000, 0, 0)
    s = tstructure(5, adj, 0b11000, (H2, H2, H2, INF, INF))
    g3 = TModel(s, (0b00110, 0b01010, 0b11000))
    boxless = l_grain_lhs(3)
    ld, dd = tdenot(f_and(boxless, f_not(l_grain_rhs(3))), g3), \
        tdenot(DEAD, g3)
    boxless_refutes = any(
        not ld[q].minus(dd[q], g3.s.u[q]).is_empty() for q in range(5))
    ld3 = tdenot(ante3, g3)
    boxed_empty = all(
        ld3[q].minus(dd[q], g3.s.u[q]).is_empty() for q in range(5))
    ok &= boxless_refutes and boxed_empty
    print('- box-off contrast (G3 bipartition model, denominator 2): '
          + ('boxless width-3 grain REFUTED there; S_3 antecedent '
             'satisfied NOWHERE live (the box is exactly what the '
             'bipartition escape violates)'
             if boxless_refutes and boxed_empty
             else '!! contrast failed -- investigate'), file=out)
    print(file=out)

    # -- k = 4 (unboundedness continues; random-only corroboration)
    ante4 = s_forced_ante(4)
    print(f'## k = 4: `{tshow(ante4)} -> D`', file=out)
    got, c = _refutes_at_v0(ante4, forced_chain(4, (Fraction(1, 4),) * 4))
    ok &= got
    print(f'- (1/4 x4)-chain refutes at denominator 4: '
          + (f'CONFIRMED at (v0, {c})' if got else '!! FAILED'), file=out)
    for m in (2, 3):
        hit = _silent(ante4, 4, m, exhaustive=False, rounds=2500,
                      seed=840 + m)
        ok &= hit is None
        print(f'- denominator-{m} menu (random-only, 2500 rounds n<=6; '
              'the certificate is Lemma SEQ, which covers all n): '
              + ('SILENT' if hit is None
                 else f'!! COUNTERMODEL {hit!r} -- SEQ WRONG'), file=out)
    print(file=out)

    print('## verdict on the corrected small-model conjecture', file=out)
    print('- S_3: G = 1, A-nesting depth 1, NO countermodel at '
          'denominators 1-2 (SEQ), countermodels at 3 and 4. '
          'Hypothesis c = 2: REFUTED. Hypothesis c = 2^depth (= 2 '
          'here): REFUTED.', file=out)
    print('- S_k needs some dwell bound < 1/(k-1) (denominator >= k): '
          'countermodel granularity is UNBOUNDED in formula width at '
          'fixed G and fixed nesting depth. The grid must scale with '
          'the number of graded subformulas (k of them in S_k -- the '
          '1/k-chain shows this count is tight for the family).',
          file=out)
    print(file=out)

    # -- tower probes: the depth mechanism. Certificates both
    # ways: each tower is refuted at
    # denominator 2 by an explicit half-dwell chain (the random tier
    # misses chain shapes -- a documented lesson, hit again here
    # on the first draft of this block), and is NOT refutable at
    # denominator 1 by reduction to Lemma SEQ, via one of two
    # mechanisms: (alpha) PROJECTION -- MONO_F
    # projects same-window composite obligations to their atom
    # obligations (A_1(a & X) -> A_1 a); (beta) DESCENT -- every
    # trajectory from a live A_1(a & X)-state is forced through an
    # (a & X)-state, the box's disjointness descends to it, and SEQ
    # prices X's own window there. Depth adds nothing beyond the
    # width these reductions expose.
    print('## depth-2 tower probes (m = 2 witnesses asserted; '
          'm = 1 impossibility = SEQ via projection/descent)', file=out)
    tower_chain = forced_chain(3, (Fraction(1, 2),) * 3)
    for name, mech, t in _tower_probes():
        got, c = _refutes_at_v0(t, tower_chain)
        ok &= got
        hit1 = _silent(t, 3, 1, exhaustive=True, rounds=1500,
                       seed=871, n_hi=5)
        ok &= hit1 is None
        print(f'- {name}: half-dwell chain witness at denominator 2: '
              + (f'CONFIRMED at (v0, {c})' if got else '!! FAILED')
              + '; denominator-1 '
              + (f'SILENT ({mech} SEQ proves all n)' if hit1 is None
                 else f'!! COUNTERMODEL {hit1!r}'), file=out)
    print('- verdict: no depth-driven grid refinement in these shapes; '
          'each tower grid demand equals what projection/descent '
          'expose to SEQ', file=out)
    print(file=out)
    print(f'forced overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


# ---------------------------------------------------------------------------
# FS corroboration + the curfew (anchor-pinch) family
# (the `curfew` subcommand)
#
# EQ-FS (first-service), a basis correction:
#     A_T[a] & A_T[b]  <=  A_T[ (a & A_T[b]) v (b & A_T[a]) ]
# Hand proof over clocked models (first-hit +
# fusion) covers ALL location counts and menus; the searches below are
# falsification-armed corroboration. Also checked: the two-deadline
# min-form and the n = 3 schema instance.
#
# The curfew specimen (k = 2): atoms b1, b2 (curfewed), c (avoided):
#     Phi := ~b1 & ~b2 & ~c & AF<=1[b1] & AF<=1[b2] & ~AF<=5/4[c]
#            & PG[ pairwise-disjoint(b1,b2,c)
#                  & (b1 -> AF<=1/2[c]) & (b2 -> AF<=1/2[c]) ]
# Phi -> D is refutable, and the PINCH argument
# proves every countermodel needs a dwell bound < 1/4 AND a c-anchor
# in (1/4, 3/10] at some b-location -- forcing denominator >= 6, with
# an explicit chain witness at 6. This is a THIRD granularity
# mechanism (anchor arithmetic, not service-slot room: slot-counting
# alone would allow m = 5) and the first specimen where the sharp
# denominator sits strictly between the width count and the
# grid-function bound N_chi * G = 3 * 4 = 12. Silences at m <= 5 are
# proof-covered (all n); searches corroborate.

H2, Q54, S56, S16 = (Fraction(1, 2), Fraction(5, 4), Fraction(5, 6),
                     Fraction(1, 6))


def fs_pair(T1, T2, k3=False):
    """(lhs, rhs) of EQ-FS; same-T if T1 == T2, min-form otherwise;
    k3 adds the third obligation (n-ary schema instance)."""
    a, b, c = atom(0), atom(1), atom(2)
    if not k3:
        lhs = f_and(pfle(T1, a), pfle(T2, b))
        rhs = pfle(min(T1, T2),
                   f_or(f_and(a, pfle(T2, b)), f_and(b, pfle(T1, a))))
        return lhs, rhs
    lhs = f_and(f_and(pfle(T1, a), pfle(T1, b)), pfle(T1, c))
    d1 = f_and(a, f_and(pfle(T1, b), pfle(T1, c)))
    d2 = f_and(b, f_and(pfle(T1, a), pfle(T1, c)))
    d3 = f_and(c, f_and(pfle(T1, a), pfle(T1, b)))
    return lhs, pfle(T1, f_or(f_or(d1, d2), d3))


def curfew_ante(with_rows=True):
    b1, b2, c = atom(0), atom(1), atom(2)
    neg = f_and(f_and(f_not(b1), f_not(b2)), f_not(c))
    obl = f_and(pfle(ONE, b1), pfle(ONE, b2))
    avoid = f_not(pfle(Q54, c))
    dis = f_and(f_and(f_not(f_and(b1, b2)), f_not(f_and(b1, c))),
                f_not(f_and(b2, c)))
    rows = f_and(impl(b1, pfle(H2, c)), impl(b2, pfle(H2, c)))
    box = pg(f_and(dis, rows) if with_rows else dis)
    return f_and(f_and(f_and(neg, obl), avoid), box)


def curfew_witness_m6() -> TModel:
    """v0(5/6) -> X(b1, 1/6) -> Y(b2, 1/6) -> Z(1/6) -> W(c, stay).
    c-anchors: W=0, Z=1/6, Y=1/3, X=1/2, v0=4/3. All curfew
    constraints tight: A[b2](v0) = 1, A_c(X) = 1/2, avoid-capacity
    4/3 > 5/4."""
    adj = (0b00010, 0b00100, 0b01000, 0b10000, 0)
    stay = 0b10000
    u = (S56, S16, S16, S16, INF)
    s = tstructure(5, adj, stay, u)
    val = (0b00010, 0b00100, 0b10000)  # b1@X, b2@Y, c@W
    return TModel(s, val)


def curfew_control_m2() -> TModel:
    """box-off control: without the curfew rows the S_2 grid suffices:
    v0(1/2) -> X(b1, 1/2) -> Y(b2, stay); c nowhere."""
    adj = (0b010, 0b100, 0)
    stay = 0b100
    u = (H2, H2, INF)
    s = tstructure(3, adj, stay, u)
    val = (0b010, 0b100, 0)
    return TModel(s, val)


def run_curfew(out) -> bool:
    ok = True
    print('# EQ-FS corroboration + the curfew (anchor-pinch) '
          'specimen', file=out)
    print(file=out)
    print('Certificate structure: FS validity and the curfew silences '
          'are hand proofs covering ALL location counts and menus '
          '(development record); every search below is '
          'falsification-armed corroboration that would indict the '
          'proof if it hit. Witnesses are explicit models, '
          'machine-checked here.', file=out)
    print(file=out)

    # -- EQ-FS: countermodel searches (expect silence, all variants)
    print('## EQ-FS over clocked models (searches armed against the '
          'first-hit proof)', file=out)
    variants = [('same-T (T = 1)', fs_pair(ONE, ONE)),
                ('same-T (T = 1/2)', fs_pair(H2, H2)),
                ('min-form (T1 = 1/2, T2 = 3/2)',
                 fs_pair(H2, Fraction(3, 2))),
                ('min-form (T1 = 2, T2 = 1)', fs_pair(Fraction(2), ONE)),
                ('n = 3 schema instance (T = 1)',
                 fs_pair(ONE, ONE, k3=True))]
    for name, (lhs, rhs) in variants:
        hit = search_menu(lhs, rhs, 'impl', 1, 6,
                          menu_for(4, Fraction(3)), 3,
                          exhaustive_max_n=2, random_rounds=3000,
                          seed=hash(name) % 99991)
        silent = hit is None
        ok &= silent
        print(f'- {name} (exhaustive n<=2 at denominator 4, cap 3, + '
              '3000 random rounds n<=6): '
              + ('SILENT as the first-hit proof predicts'
                 if silent else f'!! COUNTERMODEL {hit!r} -- FS proof '
                 'WRONG, halt and investigate'), file=out)
    print(file=out)

    # -- curfew: the m = 6 witness
    ante = curfew_ante()
    print('## curfew specimen: `Phi -> D` (deadlines 1, 1/2, 5/4; '
          'G = 4; bases {b1, b2, c}: N_chi = 3)', file=out)
    tm = curfew_witness_m6()
    got, c = _refutes_at_v0(ante, tm)
    ok &= got
    print('- explicit denominator-6 chain witness '
          '(5/6, 1/6, 1/6, 1/6, stay): '
          + (f'REFUTES at (v0, {c})' if got else '!! FAILED')
          + f' [{tm!r}]', file=out)
    # -- silences at m <= 5 (PINCH-covered)
    for m in (1, 2, 3, 4, 5):
        hit = search_menu(ante, DEAD, 'impl', 1, 6,
                          menu_for(m, Fraction(2)), 3,
                          exhaustive_max_n=2, random_rounds=2500,
                          seed=900 + m)
        silent = hit is None
        ok &= silent
        print(f'- denominator-{m} menu (exhaustive n<=2 + 2500 random '
              'n<=6): '
              + ('SILENT as Lemma PINCH proves (any countermodel '
                 'needs a dwell bound < 1/4 at the first-serviced '
                 'b-location and, at m = 5, a c-anchor in the '
                 'fifth-free interval (1/4, 3/10] at the second)'
                 if silent
                 else f'!! COUNTERMODEL {hit!r} -- PINCH WRONG'),
              file=out)
    # -- box-off control: rows removed, coarse grid returns
    ante_off = curfew_ante(with_rows=False)
    tm2 = curfew_control_m2()
    got2, c2 = _refutes_at_v0(ante_off, tm2)
    ok &= got2
    print('- control (curfew rows OFF, disjointness kept): '
          'denominator-2 witness '
          + (f'REFUTES at (v0, {c2})' if got2 else '!! FAILED')
          + ' -- the S_2 grid suffices without the rows; the 2 -> 6 '
          'escalation is the anchor-pinch mechanism itself', file=out)
    print(file=out)
    print('## verdict for the grid-function conjecture', file=out)
    print('- forced denominator 6 vs bound N_chi * G = 12: the '
          'conjecture SURVIVES its third designed mechanism '
          '(room/SEQ, alignment, anchor-pinch), at ratio 1/2.',
          file=out)
    print('- mechanism note: slot-room alone allows m = 5 (two grid '
          'points in (3/4, 1]); the pinch excludes it by anchor '
          'arithmetic -- A_c(second-service loc) must lie in '
          '(1/4, 3/10], which contains no fifth. The good set is '
          '{m >= 6}: order-shaped again.', file=out)
    print(file=out)
    print(f'curfew overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


# ---------------------------------------------------------------------------
# the loose-seed probe (the schedulable-type lemma's empirical
# prelude)
#
# THE LEMMA (construction section): if |-/- chi-hat then some
# SCHEDULABLE Sigma+-type contains ~chi-hat -- i.e. ~chi-hat is
# consistent with a blocker-loose residual profile. The semantic
# shadow, probed here over clocked models: whenever gamma (a
# unit-language seed with pending bases psi_1..psi_m at stages
# s_1..s_m) is satisfiable, it should also be satisfiable LOOSELY --
# conjoined with the tightest blocker negation ~AF<=(s_i - 1/N)[psi_i]
# per pending base (which implies all the coarser blocker negations
# by deadline monotonicity). A specimen where gamma is satisfiable in
# the search bounds but its loose strengthening is exhaustively
# refuted at STRICTLY SUPERIOR bounds is a TIGHT-FORCING candidate:
# the place a further basis correction would live (the record:
# three corrections, each at a consistency-demand-meets-missing-
# interaction-law seam). The armed expectation, from the seed-anchor
# arithmetic analysis: all specimens LOOSE -- upper bounds
# on seed anchors of pending bases derivable from unit facts compose
# from unit deadlines and are therefore never sub-unit; the tight
# devices (curfew rows, avoid horizons) bind downstream locations and
# run-side quantities, not seed residuals.
#
# Specimens: the known families (S_2, S_3, curfew Phi), a modal-base
# cascade (the base itself contains a graded subformula, so its
# cell-truth can flip mid-cell in non-uniform models -- the one shape
# where "atoms are clock-blind" does not directly protect the seed),
# three designed adversaries that try to force tightness (row
# composition at the seed, a seed-true row antecedent, the
# almost-service configuration), and a random unit tier.

def _blocker(psi, stage: int, N: int):
    """~AF<=(stage - 1/N)[psi]: the tightest loose-profile conjunct
    for a base pending at integer stage `stage` under grid 1/N."""
    return f_not(pfle(Fraction(stage * N - 1, N), psi))


def _residual_profile(tm: TModel, q: int, c, pend, N: int, cap: int):
    """Per pending base: the minimal j (in 1/N units, up to cap*N)
    with (q, c) in [[AF<=j/N psi]], or None if none <= cap."""
    prof = []
    for name, psi, stage in pend:
        got = None
        for j in range(1, cap * N + 1):
            d = tdenot(pfle(Fraction(j, N), psi), tm)
            if d[q].contains(c):
                got = Fraction(j, N)
                break
        prof.append((name, got))
    return prof


def loose_edf_tree(k: int) -> TModel:
    """The FRESH-SEED witness for S_k: v0 (u = 1/k) branching into the
    k rotation chains; rotation j services a_j, a_{j+1}, ..., a_{j-1}
    in k locations of dwell 1/k (last stays). Every pending anchor at
    v0 is EXACTLY 1 (the worst branch services each base last), so the
    seed satisfies every blocker ~AF<=(k-1)/k[a_i] while every A_1
    obligation holds tight at 1 -- looseness at the canonical grid
    1/k itself, the semantic image of the construction's fresh seed."""
    n = 1 + k * k
    loc = lambda j, s: 1 + j * k + s  # rotation j, step s (0-based)
    adj = [0] * n
    stay = 0
    u = [None] * n
    u[0] = Fraction(1, k)
    for j in range(k):
        adj[0] |= 1 << loc(j, 0)
        for s in range(k):
            q = loc(j, s)
            if s < k - 1:
                adj[q] = 1 << loc(j, s + 1)
                u[q] = Fraction(1, k)
            else:
                adj[q] = 0
                stay |= 1 << q
                u[q] = INF
    val = [0] * k
    for j in range(k):
        for s in range(k):
            val[(j + s) % k] |= 1 << loc(j, s)
    return TModel(tstructure(n, tuple(adj), stay, tuple(u)), tuple(val))


def _loose_specimens():
    """(name, gamma, pending, N, natoms, explicit_witness_or_None).
    A witness is (tm, q, c) claimed to satisfy the LOOSE formula."""
    a, b, e = atom(0), atom(1), atom(3)
    theta = f_and(a, pfle(ONE, b))
    specs = []

    # S_2 / S_3: explicit fresh-seed EDF trees at the canonical grid.
    for k in (2, 3):
        pend = [(f'a{i}', atom(i), 1) for i in range(k)]
        specs.append((f'S_{k} antecedent', s_forced_ante(k), pend, k, k,
                      (loose_edf_tree(k), 0, Fraction(0))))

    # curfew Phi: pending b1, b2 at stage 1; c is avoid-only (no
    # positive stage => no blocker). N = N_chi = 3. The m = 6 witness
    # itself should be loose: b-anchors at v0 are 5/6 and 1 > 2/3.
    pend = [('b1', atom(0), 1), ('b2', atom(1), 1)]
    specs.append(('curfew Phi (m6 witness)', curfew_ante(), pend, 3, 3,
                  (curfew_witness_m6(), 0, Fraction(0))))

    # modal-base cascade: theta := a & AF<=1[b] pending at stage 1;
    # b's tower base pending at stage 2. N = 2 bases. Search tier.
    casc = f_and(f_and(f_and(f_not(a), f_not(b)), f_not(theta)),
                 f_and(pfle(ONE, theta), pfle(Fraction(2), b)))
    specs.append(('modal-base cascade', casc,
                  [('theta=a&AF1[b]', theta, 1), ('b', b, 2)], 2, 2,
                  None))

    # adversary 1 -- row composition: A_1[a] + box(a -> A_1[b]) forces
    # AF<=2[b]; does anything force b TIGHT at the seed?
    adv1 = f_and(f_and(f_and(f_not(a), f_not(b)), pfle(ONE, a)),
                 f_and(pg(impl(a, pfle(ONE, b))), pfle(Fraction(2), b)))
    specs.append(('adv1 row-composed', adv1,
                  [('a', a, 1), ('b', b, 2)], 2, 2, None))

    # adversary 2 -- seed-true row antecedent: e holds at the seed and
    # box(e -> A_1[b]) fires THERE; plus a parallel obligation on a.
    adv2 = f_and(f_and(f_and(e, f_not(a)), f_and(f_not(b), pfle(ONE, a))),
                 f_and(pg(impl(e, pfle(ONE, b))), pfle(ONE, b)))
    specs.append(('adv2 seed-true row', adv2,
                  [('a', a, 1), ('b', b, 1)], 2, 4, None))

    # adversary 3 -- almost-service: a permanent, b owed by 2, not by
    # 1; theta = a & AF<=1[b] owed by 1 (derivable via U7-decompose +
    # U10F), not now. The sharpest known pressure toward a forced-
    # early modal-base service.
    adv3 = f_and(f_and(f_and(a, pg(a)), f_not(pfle(ONE, b))),
                 f_and(pfle(Fraction(2), b), pfle(ONE, theta)))
    specs.append(('adv3 almost-service', adv3,
                  [('theta=a&AF1[b]', theta, 1), ('b', b, 2)], 2, 2,
                  None))
    return specs


def _sat_at(f, tm):
    """(q, c) with (q, c) live and satisfying f, or None."""
    d, dd = tdenot(f, tm), tdenot(DEAD, tm)
    for q in range(tm.s.n):
        diff = d[q].minus(dd[q], tm.s.u[q])
        if not diff.is_empty():
            return (q, _witness_point(diff))
    return None


def _find_state(f, n_hi, menu, k, rounds, seed, exhaustive_max_n=1):
    """First (tm, q, c) whose live part satisfies f somewhere.
    Exhaustive tier kept tiny (n = 1); the random tier carries the
    search -- witness-hunting, not minimality certification."""
    for n in range(1, min(n_hi, exhaustive_max_n) + 1):
        for tm in exhaustive_tmodels(n, k, umenu=menu):
            w = _sat_at(f, tm)
            if w:
                return tm, w[0], w[1]
    rng = random.Random(seed)
    for _ in range(rounds):
        n = rng.randint(min(n_hi, exhaustive_max_n + 1), n_hi)
        tm = random_tmodel(n, k, rng, umenu=menu)
        w = _sat_at(f, tm)
        if w:
            return tm, w[0], w[1]
    return None


def _probe_loose(name, gamma, pend, N, natoms, out, *, witness=None,
                 spec=None, cap=None, n_hi=5, rounds=1200, seed=11):
    """Probe one specimen; returns (verdict, is_tight_candidate)."""
    cap = cap or max(int(horizon(gamma)) + 1, 2)
    loose = gamma
    for _, psi, stage in pend:
        loose = f_and(loose, _blocker(psi, stage, N))

    if witness is not None:
        tm, q, c = witness
        w = _sat_at(loose, tm)
        if w is not None and w[0] == q:
            prof = _residual_profile(tm, w[0], w[1], pend, N, cap)
            prof_s = ', '.join(f'{nm}: {v if v is not None else ">cap"}'
                               for nm, v in prof)
            print(f'- {name}: LOOSE by explicit witness (n = {tm.s.n}, '
                  f'seed ({w[0]}, {w[1]}), residual profile [{prof_s}] '
                  '-- machine-checked)', file=out)
            return 'loose', False
        print(f'- {name}: !! explicit loose witness FAILED its check '
              f'(sat at {w}) -- construction wrong, investigate',
              file=out)
        return 'witness-broken', True

    grans = [N, 2 * N]
    hit = None
    for g in grans:
        hit = _find_state(gamma, n_hi, menu_for(g, Fraction(cap)),
                          natoms, rounds, seed)
        if hit:
            gamma_gran = g
            break
    if hit is None:
        print(f'- {name}: seed formula NOT satisfied in bounds '
              f'(grans {grans}, n<={n_hi}) -- vacuous for E2, skipped',
              file=out)
        return 'unsat-in-bounds', False
    tm, q, c = hit
    prof = _residual_profile(tm, q, c, pend, N, cap)
    prof_s = ', '.join(f'{nm}: {v if v is not None else ">cap"}'
                       for nm, v in prof)
    lhit = None
    for g in grans + [4 * N]:
        lhit = _find_state(loose, n_hi + 1, menu_for(g, Fraction(cap)),
                           natoms, rounds * 2, seed + 1)
        if lhit:
            loose_gran = g
            break
    if lhit is None:
        if spec is not None:
            verdict, detail = _constructive_loose(spec)
            if verdict:
                print(f'- {name}: LOOSE by canon construction after '
                      f'random-tier miss ({detail}; seed profile was '
                      f'[{prof_s}]) -- the documented lesson again: random '
                      'tiers miss structured witnesses; the canonical '
                      'model IS the structured witness', file=out)
                return 'loose', False
            print(f'- {name}: !! TIGHT-FORCING CANDIDATE, constructive '
                  f'tier concurs ({detail}) -- seed satisfied (gran '
                  f'{gamma_gran}, profile {prof_s}), loose refused by '
                  'search AND construction. This is the fourth-'
                  'correction signal; escalate by hand.', file=out)
            return 'TIGHT-CANDIDATE', True
        print(f'- {name}: !! TIGHT-FORCING CANDIDATE -- seed satisfied '
              f'(gran {gamma_gran}, profile {prof_s}) but the '
              f'blocker-loose strengthening missed at superior bounds '
              f'(grans {grans + [4 * N]}, n<={n_hi + 1}, '
              f'{rounds * 2} rounds). Escalate by hand before '
              'believing: this is where a FOURTH basis correction '
              'would live.', file=out)
        return 'TIGHT-CANDIDATE', True
    ltm, lq, lc = lhit
    lprof = _residual_profile(ltm, lq, lc, pend, N, cap)
    lprof_s = ', '.join(f'{nm}: {v if v is not None else ">cap"}'
                        for nm, v in lprof)
    print(f'- {name}: LOOSE (seed found at gran {gamma_gran}, residual '
          f'profile [{prof_s}]; loose witness at gran {loose_gran}, '
          f'n = {ltm.s.n}, profile [{lprof_s}])', file=out)
    return 'loose', False


def _random_unit_gamma(rng: random.Random, k: int):
    """A random unit-language seed: a conjunction of pending
    declarations (~psi & AF<=s[psi], s in {1, 2}) over atom bases,
    an optional box row, an optional avoid conjunct. Returns
    (gamma, pend, canon.Spec) -- the Spec mirrors gamma exactly, so
    the constructive tier (canon's elimination pipeline) can
    adjudicate search misses."""
    import canon as _canon
    m = rng.randint(2, 3)
    bases = rng.sample(range(k), m)
    g = None
    pend = []
    sp_pend = []
    sp_rows = ()
    sp_disj = ()
    sp_avoid = ()
    for i in bases:
        s = rng.choice((1, 1, 2))
        cj = f_and(f_not(atom(i)),
                   pfle(Fraction(s), atom(i)))
        pend.append((f'a{i}', atom(i), s))
        sp_pend.append((i, s))
        g = cj if g is None else f_and(g, cj)
    if rng.random() < 0.6:
        i, j = rng.sample(bases, 2)
        g = f_and(g, pg(impl(atom(i), pfle(ONE, atom(j)))))
        sp_rows = ((i, j, 1),)
    nonbases = [x for x in range(k) if x not in bases]
    avoid_atom = None
    if nonbases and rng.random() < 0.4:
        i = rng.choice(nonbases)
        h = rng.choice((1, 2))
        g = f_and(g, f_not(pfle(Fraction(h), atom(i))))
        sp_avoid = ((i, h),)
        avoid_atom = i
    if rng.random() < 0.5:
        top = max(bases) + 1
        g = f_and(g, pairwise_disjoint_box(top))
        sp_disj = tuple((x, y) for x in range(top)
                        for y in range(x + 1, top))
    atoms = sorted(set(bases)
                   | set(range(max(bases) + 1) if sp_disj else ())
                   | ({avoid_atom} if avoid_atom is not None else set()))
    spec = _canon.Spec(name='rand', atoms=tuple(atoms),
                       pend=tuple(sp_pend), rows=sp_rows,
                       disj=sp_disj, avoid=sp_avoid,
                       N=len(sp_pend))
    return g, pend, spec


def _constructive_loose(spec):
    """canon's pipeline as the constructive tier: build, eliminate,
    check the fresh seed survives, emit, evaluate the loose formula
    there. Returns (verdict_bool_or_None, detail). None = the
    constructive tier could not decide (seed eliminated)."""
    import canon as _canon
    types = _canon.build_types(spec)
    alive, _ = _canon.eliminate(spec, types)
    seed = _canon.fresh_seed(spec)
    if seed.key() not in alive:
        return None, 'fresh seed eliminated'
    tm, idx = _canon.emit_tmodel(spec, alive)
    si = idx[seed.key()]
    f = _canon.spec_formula(spec, loose=True)
    d, dd = tdenot(f, tm), tdenot(_canon.DEAD, tm)
    diff = d[si].minus(dd[si], tm.s.u[si])
    if diff.is_empty():
        return False, f'canonical model (n = {tm.s.n}) refuses at seed'
    return True, (f'canonical model n = {tm.s.n}, seed loc {si}, '
                  f'clock {_witness_point(diff)}')


def run_looseseed(out, random_specs: int = 12, seed: int = 2026) -> bool:
    ok = True
    print('# the loose-seed probe (schedulable-type prelude)', file=out)
    print(file=out)
    print('Armed expectation: every satisfiable unit seed is LOOSELY '
          'satisfiable (blockers `~AF<=(s-1/N)[psi]` co-satisfiable, '
          'one per pending base). A TIGHT-FORCING hit would be the '
          'fourth-correction signal and exits 1. Verdicts are '
          'search-bounded evidence, not certificates; the proof-side '
          'status lives in the development record.', file=out)
    print(file=out)
    print('## designed specimens (explicit witnesses where the family '
          'is understood; search elsewhere)', file=out)
    tight = 0
    for name, gamma, pend, N, natoms, wit in _loose_specimens():
        v, t = _probe_loose(name, gamma, pend, N, natoms, out,
                            witness=wit)
        tight += int(t)
    print(file=out)
    print(f'## random unit tier ({random_specs} seeds)', file=out)
    rng = random.Random(seed)
    stats = {'loose': 0, 'TIGHT-CANDIDATE': 0, 'unsat-in-bounds': 0,
             'witness-broken': 0}
    for i in range(random_specs):
        gamma, pend, spec = _random_unit_gamma(rng, 3)
        N = len(pend)
        v, t = _probe_loose(f'rand{i}', gamma, pend, N, 3, out,
                            spec=spec, rounds=900, seed=seed + 7 * i)
        stats[v] += 1
        tight += int(t)
    print(file=out)
    print(f'- random tier: {stats["loose"]} loose, '
          f'{stats["TIGHT-CANDIDATE"]} tight-candidates, '
          f'{stats["unsat-in-bounds"]} unsat-in-bounds', file=out)
    ok = tight == 0
    print(file=out)
    print(f'looseseed overall: {"PASS" if ok else "FAIL"} '
          f'({tight} tight-forcing candidate(s))', file=out)
    return ok


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(
        description='F-fragment small-model sweep')
    sub = ap.add_subparsers(dest='cmd', required=True)
    sw = sub.add_parser('sweep', help='corpus + minimality profiles')
    sw.add_argument('--pairs', type=int, default=30)
    sw.add_argument('--seed', type=int, default=2026)
    sw.add_argument('--out', default='-')
    gr = sub.add_parser('grain', help='the L_grain separation specimen')
    gr.add_argument('--out', default='-')
    fo = sub.add_parser('forced', help='the disjointness-forced family '
                        '(conjecture adjudication)')
    fo.add_argument('--out', default='-')
    cu = sub.add_parser('curfew', help='EQ-FS corroboration + the '
                        'anchor-pinch specimen')
    cu.add_argument('--out', default='-')
    ls = sub.add_parser('looseseed', help='blocker-loose seed '
                        'satisfiability probe')
    ls.add_argument('--random', type=int, default=12)
    ls.add_argument('--seed', type=int, default=2026)
    ls.add_argument('--out', default='-')
    args = ap.parse_args()
    out = sys.stdout if args.out == '-' else open(args.out, 'w')
    try:
        if args.cmd == 'sweep':
            sweep(args.pairs, args.seed, out)
        elif args.cmd == 'grain':
            ok = run_grain(out)
            sys.exit(0 if ok else 1)
        elif args.cmd == 'curfew':
            ok = run_curfew(out)
            sys.exit(0 if ok else 1)
        elif args.cmd == 'looseseed':
            ok = run_looseseed(out, args.random, args.seed)
            sys.exit(0 if ok else 1)
        else:
            ok = run_forced(out)
            sys.exit(0 if ok else 1)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == '__main__':
    main()
