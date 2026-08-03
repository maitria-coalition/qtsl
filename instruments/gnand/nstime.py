#!/usr/bin/env python3
"""QTSL nonstandard-time layer: infinitesimal-dwell models.

Time values live in NSQ := the lex-ordered plane Q + Q*eps (eps a
positive infinitesimal: 0 < eps < q for every standard rational q > 0).
NSQ is a linearly ordered Q-vector space; the timed engine
(timed.py) only ever adds, subtracts, scalar-multiplies, compares,
mins and maxes time values, so it runs over NSQ unchanged -- this file
supplies the numeric type and NEVER touches the engine.

THE GERM READING (Lemma T's semantics). The lex order on pairs (a, b)
is exactly the order of germs at 0+ of affine functions a + b*t: for
standard rationals, a1 + b1*t < a2 + b2*t holds for all sufficiently
small t > 0 iff (a1, b1) < (a2, b2) lexicographically. Every quantity
the evaluator computes on a finite model with NSQ dwells is Q-affine in
eps with coefficients determined by the model and formula; every branch
the evaluator takes is decided by finitely many lex comparisons. Hence
substituting a sufficiently small standard delta > 0 for eps preserves
every branch and every membership verdict: an NSQ-model refutation of a
formula yields standard clocked refutations at all small delta (Lemma
T, the germ transfer), so every standard-clocked-valid formula is valid
over the NSQ class as well (Corollary S -- soundness of the whole basis
over C_eps for free, robust under future basis corrections). The
`germ` check below is the machine shadow: NSQ verdicts vs verdicts at
delta in a decreasing standard ladder.

THE CLASS C_eps. Finite clocked models whose dwell bounds are NSQ
values (positive in the lex order; INF allowed as before), restricted
by: the INFINITESIMAL-DWELL SUBGRAPH IS ACYCLIC -- among live non-stay
locations with u finite and standard part 0, no directed cycle. Reason
(the Zeno boundary): trajectories must be total on time with locally
finite jumps; a cycle of infinitesimal total dwell can be traversed
forever while its elapsed time m*eps stays below every standard bound,
so such a "run" never becomes total -- it is a Zeno pseudo-trajectory,
and a location whose every continuation is of that shape has NO
trajectories at all, while the engine's clock-blind liveness fixpoint
would still call it live (the engine assumes positive cycles diverge,
an Archimedean fact). The acyclicity restriction is exactly what makes
the engine's liveness, INF-detection, and debut fixpoints agree with
the honest NSQ semantics: every cycle then contains a location of
non-infinitesimal dwell, so following any infinite walk accumulates
unbounded standard time. Standard clocked models are the eps-free
members. The `zeno` check documents the excluded shape.

WHY THIS EXISTS (E2a). The rung's one open crux is per-base
looseness: a unit-maximal consistent theory u never derives
A_{s-1/N}[psi] for a pending base psi. Over
C_eps, lazy scheduling realizes looseness geometrically: services can
be placed at times 1 - k*eps, ..., 1 - eps, 1 -- inside the deadline,
past EVERY standard sub-stage threshold 1 - 1/N simultaneously, and an
eps-burst serves any finite width of pairwise-disjoint obligations in
infinitesimal elapsed time, so the SEQ/room mechanism, the
alignment mechanism, and the anchor-pinch mechanism all
dissolve: none of the three granularity drivers can price an eps-model.
The `witness` check machine-verifies exactly this on the looseseed
roster (S_2, S_3, curfew Phi, the modal-base cascade, the three
designed tightness-adversaries, canon's rand5): an explicit eps-model
whose seed satisfies gamma AND every blocker ~A_{s-1/N}[psi] jointly,
for a sweep of N -- the semantic content of E2 (not just E2a: the
conjunction over pending bases holds in one model), machine-checked
per specimen. Lemma T then converts each eps-witness into standard
witnesses at small delta -- which is how the eps-freedom coexists with
the standard grid bounds: delta is chosen AFTER the model, while the
canonical construction's grid 1/N is fixed BEFORE.

Checks (all run by `battery`; each prints a section, exit-coded):
  algebra   -- NSQ is what it claims: ordered-vector-space laws on
               samples, mixed-type comparisons/arithmetic against
               Fraction/int (the engine's internal Fraction(0)
               literals meet NSQ values constantly), hash-equality
               consistency (NSQ(a,0) == Fraction(a) and hashes agree),
               sorting of mixed lists, interval canonicalization and
               witness-point extraction over NSQ endpoints.
  diff-std  -- the standard-part differential: on random STANDARD
               models and formulas, the engine over Fraction and the
               engine over NSQ(b=0) images produce identical
               denotations (endpoint-normalized). Validates the
               duck-typing path end to end; the NSQ layer's analogue
               of timed.py's diff_v0.
  germ      -- Lemma T's machine shadow: for every eps-witness model
               and its formula bundle, membership verdicts at every
               live entry state (q, 0) under NSQ equal the standard
               verdicts under eps := delta for all sufficiently small
               delta in the ladder {1/8, 1/64, 1/512}. The criterion
               is STABILIZATION (the smallest rung agrees; agreement
               never reverts as delta shrinks), not all-rung
               agreement: Lemma T's delta_0 is the branch-preservation
               threshold, finer than dwell positivity -- an N = 12
               blocker compares against 1 - 1/12, so delta = 1/8 >
               1/12 legitimately differs while every delta < 1/12
               agrees (observed: exactly that, first run).
  soundness -- the eps-battery: every row of timed.py's battery with
               expectation 'valid', plus NS-side rows for the exact
               rung-1 basis schemata (U4-pfle, U7 both halves, U9,
               U10F, FS 2-ary same-T and min-form and 3-ary, cell-A
               G2/G3/G4/G6, SCALE'd spot instances), swept over C_eps
               models: exhaustive n <= 2 over an eps-menu + a random
               tier n <= 4 (eps-cycle violators skipped as
               class-external, counted). Expectation: ZERO hits, per
               Corollary S. Any hit auto-adjudicates by delta
               substitution: if the substituted standard model also
               refutes the row, the row was never standard-valid
               (indicts the inherited battery -- not expected); if it
               does not, the NSQ layer itself is buggy. Either way a
               hit is loud cargo, never silent.
  witness   -- the E2 semantic realizations described above, plus
               class membership (is_ceps) and per-model germ
               stabilization of the full gamma+blockers conjunction.
  zeno      -- the excluded shape: an all-eps cycle, refused by
               is_ceps, with the engine-vs-semantics divergence it
               would cause documented in the output.

Regenerate the receipt with `python3 nstime.py battery > ...`.

Python as orchestration-class code, same warrant as its siblings
(tiny exact search spaces, Fractions; graduates if it grinds).
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction
from itertools import product

from oracle import TOP, BOT, atom, f_not, f_and, f_or, pg, impl, DEAD
from timed import (INF, ISet, TModel, tstructure, tdenot, tshow,
                        pfle, pule, scale_formula, timed_battery_rows,
                        random_tmodel, tnatoms, _fails, _witness_point)
from fsweep import (s_forced_ante, forced_chain, curfew_ante,
                    _loose_specimens, _blocker)

ZERO = Fraction(0)
ONE = Fraction(1)


# ---------------------------------------------------------------------------
# NSQ: the lex-ordered plane Q + Q*eps

class NSQ:
    """a + b*eps with a, b rational; lex order (eps infinitesimal)."""

    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = a if isinstance(a, Fraction) else Fraction(a)
        self.b = b if isinstance(b, Fraction) else Fraction(b)

    # -- coercion: int/Fraction embed as (x, 0); everything else refuses
    @staticmethod
    def _co(x):
        if isinstance(x, NSQ):
            return x
        if isinstance(x, (int, Fraction)):
            return NSQ(x)
        return None

    # -- lex order
    def __lt__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return (self.a, self.b) < (o.a, o.b)

    def __le__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return (self.a, self.b) <= (o.a, o.b)

    def __gt__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return (self.a, self.b) > (o.a, o.b)

    def __ge__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return (self.a, self.b) >= (o.a, o.b)

    def __eq__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        # numeric-tower consistency: NSQ(a, 0) == Fraction(a) must
        # hash equal (mixed-endpoint intervals rely on it)
        if self.b == 0:
            return hash(self.a)
        return hash(('NSQ', self.a, self.b))

    # -- vector-space operations
    def __add__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return NSQ(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __sub__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return NSQ(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        return NSQ(o.a - self.a, o.b - self.b)

    def __neg__(self):
        return NSQ(-self.a, -self.b)

    # -- scalar multiplication only: time * time is meaningless in the
    # engine, and eps^2 would break the order (positive * positive = 0
    # in a truncation). A product where both factors have nonzero
    # eps-part raises -- the artifact-pair on "the engine never
    # multiplies two durations".
    def __mul__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        if o.b == 0:
            return NSQ(self.a * o.a, self.b * o.a)
        if self.b == 0:
            return NSQ(self.a * o.a, self.a * o.b)
        raise TypeError('NSQ * NSQ with both eps-parts nonzero: '
                        'no time-by-time products in the engine')

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = NSQ._co(o)
        if o is None:
            return NotImplemented
        if o.b != 0:
            raise TypeError('division by a non-scalar NSQ')
        return NSQ(self.a / o.a, self.b / o.a)

    def __bool__(self):
        return bool(self.a) or bool(self.b)

    def __repr__(self):
        if self.b == 0:
            return f'{self.a}'
        core = '' if self.a == 0 else f'{self.a}'
        if self.b == 1:
            eps = 'e'
        elif self.b == -1:
            eps = '-e'
        else:
            eps = f'{self.b}e' if self.b > 0 or not core else f'{self.b}e'
        if core and self.b > 0:
            return f'{core}+{eps}'
        return f'{core}{eps}'


EPS = NSQ(0, 1)


def std_part(x):
    if x is INF:
        return INF
    if isinstance(x, NSQ):
        return x.a
    return x


def is_infinitesimal_dwell(x) -> bool:
    """Positive dwell with standard part zero."""
    if x is INF:
        return False
    return std_part(x) == 0 and x > 0


def subst_num(x, delta: Fraction):
    """eps := delta (standard); Fractions pass through."""
    if x is INF:
        return INF
    if isinstance(x, NSQ):
        return x.a + x.b * delta
    return x


# ---------------------------------------------------------------------------
# models over NSQ time and the class C_eps

def ns_model(tm: TModel) -> TModel:
    """NSQ-embed a standard model (b = 0 everywhere)."""
    s = tm.s
    u = tuple(INF if x is INF else NSQ(x) for x in s.u)
    return TModel(tstructure(s.n, s.adj, s.stay, u), tm.val)


def subst_model(tm: TModel, delta: Fraction) -> TModel:
    """eps := delta. Refuses non-positive substituted dwells (caller
    keeps delta below the model's positivity threshold)."""
    s = tm.s
    u = []
    for x in s.u:
        y = subst_num(x, delta)
        if y is not INF and y <= 0:
            raise ValueError(f'delta {delta} kills dwell {x}')
        u.append(y)
    return TModel(tstructure(s.n, s.adj, s.stay, tuple(u)), tm.val)


def delta_threshold(tm: TModel) -> Fraction:
    """A positive standard bound: every delta strictly below it keeps
    all substituted dwells positive. (Positivity only -- Lemma T's full
    branch-preservation threshold is finer; the germ check uses the
    ladder's tail instead of computing it.)"""
    thr = None
    for x in tm.s.u:
        if x is INF or not isinstance(x, NSQ):
            continue
        if x.a > 0 and x.b < 0:
            t = x.a / (-x.b)
            thr = t if thr is None else min(thr, t)
    return thr if thr is not None else Fraction(1)


def is_ceps(tm: TModel) -> bool:
    """C_eps membership: the infinitesimal-dwell subgraph (live,
    non-stay, u finite and infinitesimal) is acyclic."""
    s = tm.s
    eps_locs = [q for q in range(s.n)
                if (s.live >> q) & 1 and not (s.stay >> q) & 1
                and s.u[q] is not INF and is_infinitesimal_dwell(s.u[q])]
    eset = set(eps_locs)
    # DFS cycle detection on adj restricted to eset
    WHITE, GREY, BLACK = 0, 1, 2
    color = {q: WHITE for q in eps_locs}

    def dfs(q) -> bool:
        color[q] = GREY
        m = s.adj[q]
        while m:
            v = (m & -m).bit_length() - 1
            m &= m - 1
            if v in eset:
                if color[v] == GREY:
                    return False
                if color[v] == WHITE and not dfs(v):
                    return False
        color[q] = BLACK
        return True

    for q in eps_locs:
        if color[q] == WHITE and not dfs(q):
            return False
    return True


def norm_endpoint(x):
    if x is INF:
        return INF
    if isinstance(x, NSQ):
        return (x.a, x.b)
    return (x, ZERO)


def norm_iset(s: ISet):
    return tuple((norm_endpoint(lo), li, norm_endpoint(hi), hi_i)
                 for lo, li, hi, hi_i in s.ivls)


# ---------------------------------------------------------------------------
# check: algebra

def check_algebra(out) -> bool:
    ok = True

    def chk(cond, label):
        nonlocal ok
        ok &= bool(cond)
        if not cond:
            print(f'  !! FAIL: {label}', file=out)

    h = Fraction(1, 2)
    x, y, z = NSQ(1, -2), NSQ(h, 3), NSQ(0, 1)
    # order: total, lex, eps infinitesimal
    chk(EPS > 0 and EPS < Fraction(1, 10 ** 9), 'eps strictly between 0 '
        'and every standard positive')
    chk(NSQ(1, -1) < 1 and NSQ(1, -1) > h, '1-e sits between 1/2 and 1')
    chk(sorted([NSQ(1), EPS, ZERO, NSQ(1, -1), h])
        == [ZERO, EPS, h, NSQ(1, -1), NSQ(1)], 'mixed-type sort is lex')
    # vector laws on samples
    chk((x + y) - y == x, 'additive group')
    chk(3 * (x + y) == 3 * x + 3 * y, 'scalar distributes')
    chk(x + y == y + x and (x + y) + z == x + (y + z), 'commutative, '
        'associative')
    # order compatibility
    chk(x < x + EPS and x + y < x + y + EPS, 'translation-invariant order')
    chk(2 * EPS > EPS and -EPS < 0, 'scalar order compatibility')
    # mixed arithmetic against the engine's literals
    chk(Fraction(0) + EPS == EPS and Fraction(1) - EPS == NSQ(1, -1),
        'Fraction op NSQ routes through reflected dunders')
    chk(max(Fraction(0), NSQ(1, -1) + EPS - ONE) == 0,
        'max(Fraction, NSQ) with equality lands')
    chk(min(Fraction(1), NSQ(1, -1)) == NSQ(1, -1), 'min mixed')
    # equality + hash consistency (interval merging relies on this)
    chk(NSQ(h) == h and hash(NSQ(h)) == hash(h),
        'NSQ(a,0) == Fraction(a) with equal hashes')
    chk(not (NSQ(h, 1) == h), 'NSQ(a,b!=0) never equals a Fraction')
    # time*time guard
    try:
        _ = EPS * EPS
        chk(False, 'eps*eps should raise')
    except TypeError:
        pass
    # scalar division
    chk((NSQ(1, -2) / 2) == NSQ(h, -1), 'scalar division')
    # ISet machinery over NSQ endpoints
    s1 = ISet([(ZERO, True, NSQ(1, -1), False), (NSQ(1, -1), True,
                NSQ(1), True)])
    chk(s1.ivls == ISet([(ZERO, True, NSQ(1), True)]).ivls,
        'adjacent NSQ intervals merge canonically')
    s2 = ISet([(EPS, False, NSQ(0, 2), False)])
    chk(not s2.is_empty() and s2.contains(NSQ(0, Fraction(3, 2))),
        'eps-length interval is nonempty and locates its points')
    chk(not s2.contains(EPS) and not s2.contains(NSQ(0, 2)),
        'open eps-interval endpoints excluded')
    w = _witness_point(s2)
    chk(s2.contains(w), 'witness point lands inside an eps-interval')
    comp = s2.complement(NSQ(1))
    chk(comp.contains(ZERO) and comp.contains(NSQ(0, 2))
        and not comp.contains(w), 'complement over NSQ domain')
    print(f'- algebra: NSQ order/vector/mixed-type/hash/interval laws '
          f'on samples: {"PASS" if ok else "FAIL"}', file=out)
    return ok


# ---------------------------------------------------------------------------
# check: diff-std (the standard-part differential)

def check_diff_std(out, rounds: int, seed: int) -> bool:
    from timed import random_timed_formula
    rng = random.Random(seed)
    bad = 0
    for i in range(rounds):
        n = rng.randint(1, 4)
        k = rng.randint(1, 3)
        tm = random_tmodel(n, k, rng)
        f = random_timed_formula(rng, rng.randint(1, 3), k)
        d_std = tdenot(f, tm)
        d_ns = tdenot(f, ns_model(tm))
        if tuple(norm_iset(a) for a in d_std) != \
                tuple(norm_iset(a) for a in d_ns):
            bad += 1
            if bad <= 3:
                print(f'  !! mismatch at round {i}: {tshow(f)} on {tm!r}',
                      file=out)
    ok = bad == 0
    print(f'- diff-std: {rounds} random standard models/formulas, '
          f'Fraction engine vs NSQ(b=0) engine: '
          f'{bad} mismatches: {"PASS" if ok else "FAIL"}', file=out)
    return ok


# ---------------------------------------------------------------------------
# the eps-witness roster (E2 semantic realizations, hand-designed,
# machine-adjudicated here)

def _chain(spec):
    """Build a chain model from [(dwell_or_INF, stay?, atom_mask), ...]
    (single successor each; last entries may stay)."""
    n = len(spec)
    adj, stay, u, masks = [], 0, [], []
    for i, (dw, st, mask) in enumerate(spec):
        adj.append((1 << (i + 1)) if i + 1 < n else 0)
        if st:
            stay |= 1 << i
        u.append(dw)
        masks.append(mask)
    k = max((m.bit_length() for m in masks), default=0)
    val = []
    for a in range(max(k, 1)):
        va = 0
        for i, m in enumerate(masks):
            if (m >> a) & 1:
                va |= 1 << i
        val.append(va)
    return TModel(tstructure(n, tuple(adj), stay, tuple(u)), tuple(val))


def _rand5_gamma():
    """canon's rand5: bases c@2, b@1, a@1; row b -> A_1[c]; no
    disjointness (a and b batch)."""
    a, b, c = atom(0), atom(1), atom(2)
    neg = f_and(f_and(f_not(a), f_not(b)), f_not(c))
    obl = f_and(f_and(pfle(Fraction(2), c), pfle(ONE, b)), pfle(ONE, a))
    return f_and(f_and(neg, obl), pg(impl(b, pfle(ONE, c))))


def eps_witnesses():
    """(name, gamma, pending=[(label, psi, stage)], model). Models are
    the LAZY eps-schedules: every pending base served past every
    standard sub-stage threshold, all deadlines still met. Six of the
    seven ride the looseseed specimen list verbatim; rand5 is canon's."""
    A_, B_, E_ = atom(0), atom(1), atom(3)
    TH = f_and(A_, pfle(ONE, B_))
    out = []
    specs = {name: (gamma, pend)
             for name, gamma, pend, _N, _k, _w in _loose_specimens()}

    # S_2 / S_3: one eps-burst at the deadline; width costs eps, not 1/k
    g, p = specs['S_2 antecedent']
    out.append(('S_2 lazy', g, p,
                forced_chain(2, [NSQ(1, -1), EPS])))
    g, p = specs['S_3 antecedent']
    out.append(('S_3 lazy', g, p,
                forced_chain(3, [NSQ(1, -2), EPS, EPS])))

    # curfew Phi: b-services at 1-eps and 1; the row-pinned c lands at
    # 1/2 from the FIRST b-service -- no denominator anywhere; the
    # avoid horizon keeps 3/2 - eps > 5/4 of c-free prefix
    g, p = specs['curfew Phi (m6 witness)']
    out.append(('curfew lazy', g, p, _chain([
        (NSQ(1, -1), False, 0b000),   # v0: all false, dwell 1-e
        (EPS, False, 0b001),          # X: b1, dwell e
        (EPS, False, 0b010),          # Y: b2, dwell e
        (NSQ(Fraction(1, 2), -2), False, 0b000),  # Z: dwell 1/2-2e
        (INF, True, 0b100),           # W: c, stay
    ])))

    # modal-base cascade: theta = a & A_1[b] pending at 1, b at 2
    g, p = specs['modal-base cascade']
    out.append(('cascade lazy', g, p, _chain([
        (NSQ(1, -1), False, 0b00),    # v0
        (EPS, False, 0b01),           # s_theta: a (theta true: b due 1)
        (NSQ(1, -1), False, 0b00),    # z
        (INF, True, 0b10),            # s_b: b, stay
    ])))

    # adv1 row-composed: a at 1-eps fires the row; b tight at 2-eps
    g, p = specs['adv1 row-composed']
    out.append(('adv1 lazy', g, p, _chain([
        (NSQ(1, -1), False, 0b00),
        (EPS, False, 0b01),           # s_a
        (NSQ(1, -1), False, 0b00),
        (INF, True, 0b10),            # s_b
    ])))

    # adv2 seed-true row: the row fires AT the seed; burst at the end
    g, p = specs['adv2 seed-true row']
    out.append(('adv2 lazy', g, p, _chain([
        (NSQ(1, -2), False, 0b1000),  # v0: e true, dwell 1-2e
        (EPS, False, 0b0001),         # s_a
        (EPS, False, 0b0010),         # s_b
        (INF, True, 0b0000),          # rest
    ])))

    # adv3 almost-service: theta's truth flips MID-CELL at clock 1-eps
    # on v0 (a modal-base flip the development record flagged; the zone
    # machinery must place the flip exactly)
    g, p = specs['adv3 almost-service']
    out.append(('adv3 lazy', g, p, _chain([
        (NSQ(1), False, 0b01),        # v0: a, dwell 1
        (NSQ(1, -1), False, 0b01),    # x1: a, dwell 1-e
        (INF, True, 0b11),            # s_b: a & b, stay
    ])))

    # rand5 (canon): a,b batched at 1 (no disjointness), row-pinned c
    # tight at 2
    out.append(('rand5 lazy', _rand5_gamma(),
                [('a', atom(0), 1), ('b', atom(1), 1), ('c', atom(2), 2)],
                _chain([
                    (NSQ(1), False, 0b000),
                    (EPS, False, 0b011),          # s_ab: a & b
                    (NSQ(1, -1), False, 0b000),
                    (INF, True, 0b100),           # s_c
                ])))
    return out


N_SWEEP = (2, 3, 4, 6, 12)
DELTA_LADDER = (Fraction(1, 8), Fraction(1, 64), Fraction(1, 512))


def check_witnesses(out) -> bool:
    ok = True
    print('## witness: lazy eps-models realizing E2 semantically '
          '(gamma + ALL blockers jointly at the seed)', file=out)
    for name, gamma, pend, tm in eps_witnesses():
        if not is_ceps(tm):
            ok = False
            print(f'- {name}: !! model outside C_eps (eps-cycle)',
                  file=out)
            continue
        dd = tdenot(DEAD, tm)
        live_seed = not dd[0].contains(ZERO)
        gd = tdenot(gamma, tm)
        g_ok = gd[0].contains(ZERO) and live_seed
        blk_ok = True
        blk_bits = []
        for label, psi, stage in pend:
            for N in N_SWEEP:
                b = _blocker(psi, stage, N)
                hit = tdenot(b, tm)[0].contains(ZERO)
                blk_ok &= hit
                if not hit:
                    blk_bits.append(f'{label}@N={N} FAILS')
        ok &= g_ok and blk_ok
        stages = ', '.join(f'{lb}@{st}' for lb, st, in
                           [(lb, st) for lb, _p, st in pend])
        print(f'- {name}: gamma at seed: '
              f'{"yes" if g_ok else "!! NO"}; blockers '
              f'({stages}; N in {N_SWEEP}): '
              + ('ALL HOLD -- loose past every tested sub-stage'
                 if blk_ok else "!! " + "; ".join(blk_bits))
              + f' [{tm!r}]', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# check: germ (Lemma T's machine shadow)

def _verdicts(f, tm: TModel):
    """Membership of clock-0 entry states, per live location."""
    d = tdenot(f, tm)
    return tuple(d[q].contains(ZERO) if (tm.s.live >> q) & 1 else None
                 for q in range(tm.s.n))


def check_germ(out) -> bool:
    ok = True
    print('## germ: NSQ verdicts vs eps := delta ladder '
          f'{tuple(str(d) for d in DELTA_LADDER)} (Lemma T shadow)',
          file=out)
    for name, gamma, pend, tm in eps_witnesses():
        blocks = [_blocker(psi, stage, 12) for _l, psi, stage in pend]
        bundle = gamma
        for b in blocks:
            bundle = f_and(bundle, b)
        thr = delta_threshold(tm)
        v_ns = _verdicts(bundle, tm)
        detail = []
        agreements = []
        for delta in DELTA_LADDER:
            if delta >= thr:
                detail.append(f'{delta}: skipped (>= positivity '
                              f'threshold {thr})')
                continue
            v_d = _verdicts(bundle, subst_model(tm, delta))
            agree = v_d == v_ns
            agreements.append(agree)
            detail.append(f'{delta}: {"agree" if agree else "differs"}')
        # Lemma T claims agreement for all delta below SOME threshold
        # delta_0 (branch preservation -- finer than the positivity
        # threshold: e.g. an N=12 blocker needs delta < 1/12, so 1/8
        # legitimately differs). The stabilization criterion: the
        # smallest rung agrees, and agreement is monotone once begun
        # (agree -> differ as delta shrinks would CONTRADICT the lemma).
        stab = bool(agreements) and agreements[-1] and all(
            b for a, b in zip(agreements, agreements[1:]) if a)
        ok &= stab
        print(f'- {name}: {"; ".join(detail)}: '
              f'{"stabilized -- PASS" if stab else "!! FAIL (no "
              "stabilization: contradicts Lemma T, investigate)"}',
              file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# check: soundness (the eps-battery)

def _basis_rows():
    """NS-side rows: the exact rung-1 basis schemata at spot instances
    (the inherited battery covers most; these pin the F-forms and the
    cell-A four explicitly, plus SCALE'd spots)."""
    A_, B_, C_ = atom(0), atom(1), atom(2)
    H = Fraction(1, 2)
    TQ = Fraction(3, 2)
    rows = [
        ('NS-U4-pfle', A_, pfle(ONE, A_), 'impl'),
        ('NS-U7-comp', pfle(ONE, pfle(H, A_)), pfle(TQ, A_), 'equiv'),
        ('NS-U9', pfle(H, BOT), DEAD, 'impl'),
        ('NS-U10F', f_and(pg(C_), pfle(ONE, A_)),
         f_and(pg(C_), pfle(ONE, f_and(A_, C_))), 'equiv'),
        ('NS-FS-sameT', f_and(pfle(ONE, A_), pfle(ONE, B_)),
         pfle(ONE, f_or(f_and(A_, pfle(ONE, B_)),
                        f_and(B_, pfle(ONE, A_)))), 'impl'),
        ('NS-FS-min', f_and(pfle(H, A_), pfle(TQ, B_)),
         pfle(H, f_or(f_and(A_, pfle(TQ, B_)),
                      f_and(B_, pfle(H, A_)))), 'impl'),
        ('NS-G2', f_and(pg(A_), pg(B_)), pg(f_and(A_, B_)), 'impl'),
        ('NS-G3', pg(A_), pg(pg(A_)), 'impl'),
        ('NS-G4', pg(A_), f_or(A_, DEAD), 'impl'),
        ('NS-G6', f_not(DEAD), pg(f_not(DEAD)), 'impl'),
    ]
    fs3_l = f_and(f_and(pfle(ONE, A_), pfle(ONE, B_)), pfle(ONE, C_))
    d1 = f_and(A_, f_and(pfle(ONE, B_), pfle(ONE, C_)))
    d2 = f_and(B_, f_and(pfle(ONE, A_), pfle(ONE, C_)))
    d3 = f_and(C_, f_and(pfle(ONE, A_), pfle(ONE, B_)))
    rows.append(('NS-FS-3ary', fs3_l, pfle(ONE, f_or(f_or(d1, d2), d3)),
                 'impl'))
    # SCALE spots: lambda = 3 images of two graded rows
    rows.append(('NS-U7-x3', scale_formula(pfle(ONE, pfle(H, A_)),
                                           Fraction(3)),
                 scale_formula(pfle(TQ, A_), Fraction(3)), 'equiv'))
    rows.append(('NS-FS-x3', scale_formula(rows[4][1], Fraction(3)),
                 scale_formula(rows[4][2], Fraction(3)), 'impl'))
    return rows


EXH_EPS_MENU = (EPS, NSQ(1, -1), NSQ(1), NSQ(2), INF)
RAND_EPS_MENU = (EPS, NSQ(0, 2), NSQ(1, -1), NSQ(1, -2), NSQ(Fraction(1, 2)),
                 NSQ(1), NSQ(1, 1), NSQ(Fraction(3, 2)), NSQ(2), INF)


def _eps_exhaustive(n: int, k: int, umenu):
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


def _adjudicate_hit(row_id, lhs, rhs, tm, q, c, out):
    """A valid row refuted on an eps-model: substitute and re-check.
    Returns True iff the hit indicts the NSQ layer / battery loudly
    (always False in the expected world: no hits at all)."""
    thr = delta_threshold(tm)
    for delta in DELTA_LADDER:
        if delta >= thr:
            continue
        std = subst_model(tm, delta)
        ld, rd = tdenot(lhs, std), tdenot(rhs, std)
        w = _fails(ld, rd, std)
        if w is not None:
            print(f'  !! {row_id}: eps-hit TRANSFERS to standard at '
                  f'delta={delta} -- the row was never clocked-valid; '
                  f'the INHERITED battery is indicted: {std!r}',
                  file=out)
            return True
    print(f'  !! {row_id}: eps-hit does NOT transfer (delta ladder '
          f'clean) -- NSQ layer bug OR a genuine Archimedean step in '
          f'this row\'s soundness: INVESTIGATE. model={tm!r} '
          f'q={q} c={c}', file=out)
    return True


def check_soundness(out, quick: bool, seed: int) -> bool:
    rows = [(rid, lhs, rhs, direction)
            for rid, lhs, rhs, direction, expect, _note
            in timed_battery_rows() if expect == 'valid']
    rows += _basis_rows()
    rounds = 400 if quick else 1500
    print(f'## soundness: {len(rows)} valid rows over C_eps '
          f'(exhaustive n<=2, menu {EXH_EPS_MENU}; +{rounds} random '
          f'rounds n<=4, menu of {len(RAND_EPS_MENU)}); expectation '
          'ZERO hits (Corollary S)', file=out)
    ok = True
    skipped = 0
    hits = 0
    for rid, lhs, rhs, direction in rows:
        k = min(max(tnatoms(lhs), tnatoms(rhs), 1), 2)
        found = None
        for n in (1, 2):
            if found:
                break
            for tm in _eps_exhaustive(n, k, EXH_EPS_MENU):
                if not is_ceps(tm):
                    skipped += 1
                    continue
                ld, rd = tdenot(lhs, tm), tdenot(rhs, tm)
                w = _fails(ld, rd, tm)
                if w is None and direction == 'equiv':
                    w = _fails(rd, ld, tm)
                if w is not None:
                    found = (tm, w)
                    break
        if not found:
            rng = random.Random(seed + hash(rid) % 100000)
            kk = max(tnatoms(lhs), tnatoms(rhs), 1)
            for _ in range(rounds):
                n = rng.randint(2, 4)
                tm = random_tmodel(n, kk, rng, umenu=RAND_EPS_MENU)
                if not is_ceps(tm):
                    skipped += 1
                    continue
                ld, rd = tdenot(lhs, tm), tdenot(rhs, tm)
                w = _fails(ld, rd, tm)
                if w is None and direction == 'equiv':
                    w = _fails(rd, ld, tm)
                if w is not None:
                    found = (tm, w)
                    break
        if found:
            hits += 1
            tm, (q, c) = found
            _adjudicate_hit(rid, lhs, rhs, tm, q, c, out)
            ok = False
    print(f'- swept: {len(rows)} rows; eps-cycle models skipped as '
          f'class-external: {skipped}; hits: {hits}: '
          f'{"PASS" if ok else "FAIL"}', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# check: zeno (the excluded shape, documented)

def check_zeno(out) -> bool:
    # one location, self-loop, dwell eps, no stay: the engine's
    # clock-blind liveness calls it live and its debut analysis treats
    # the cycle as an escape; the NSQ semantics has NO total
    # trajectory there (elapsed time m*eps never reaches 1). C_eps
    # excludes it; this check pins the exclusion.
    s = tstructure(1, (0b1,), 0, (EPS,))
    tm = TModel(s, (0b1,))
    excluded = not is_ceps(tm)
    live_per_engine = bool(s.live & 1)
    ok = excluded and live_per_engine
    print('## zeno: the all-eps cycle (1 location, self-loop, dwell '
          'eps)', file=out)
    print(f'- engine liveness fixpoint calls it live: '
          f'{live_per_engine} (clock-blind, Archimedean assumption); '
          f'is_ceps refuses it: {excluded}: '
          f'{"PASS" if ok else "FAIL"} -- the acyclicity restriction '
          'is exactly the boundary where engine and NSQ semantics '
          'agree', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# battery

def run_battery(out, quick: bool, seed: int) -> bool:
    print('# nonstandard-time layer -- NSQ engine checks, the '
          'germ transfer shadow, C_eps soundness sweep, and the E2 '
          'semantic witnesses', file=out)
    print(file=out)
    ok = True
    ok &= check_algebra(out)
    ok &= check_diff_std(out, 120 if quick else 400, seed)
    print(file=out)
    ok &= check_zeno(out)
    ok &= check_witnesses(out)
    ok &= check_germ(out)
    ok &= check_soundness(out, quick, seed)
    print(f'nstime overall: {"PASS" if ok else "FAIL"}', file=out)
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest='cmd')
    b = sub.add_parser('battery', help='all checks (the receipt)')
    b.add_argument('--quick', action='store_true')
    b.add_argument('--seed', type=int, default=2026)
    args = ap.parse_args()
    quick = getattr(args, 'quick', False)
    seed = getattr(args, 'seed', 2026)
    ok = run_battery(sys.stdout, quick, seed)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
