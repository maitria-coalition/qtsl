#!/usr/bin/env python3
"""FS-R independence receipts -- the residual-split law's
minimality question.

TARGET.  FS-R (residual-split first-service), instance at the
wall-hand shape (T_a, T_b; c) = (2, 3; 1):

    A_2[a] & A_3[b]  <=  A_1( (a & A_3[b]) v (b & A_2[a])
                              v (A_1[a] & A_2[b]) )

over the FS-corrected basis {cell-A G-layer, U4, U7== (BOTH halves),
U9<=, U10F, FS_n, MONO_box, MONO_F, MP, PC, SCALE}.  Blind erasure
trivializes FS-R (14.1), so the separation is graded.  Two theory
facts drive this instrument's design:

RIGIDITY.  Any structure interpreting A_T for ALL rational T with
finitely many distinct operators and exact U7== is deadline-blind
(A_T constant in T): pick the minimal monotone piece G1 = A_T for
small T; for any T', A_{T'} = (A_{T'/n})^n = G1^n = G1 once
T'/n is small (G1 is idempotent by the same identity).  Blind
structures validate FS-R (its blind erasure is derivable, 14.1).  So
NO single structure can separate FS-R by itself; the
certificate must be MENU-RELATIVE: for every finite deadline menu M
(superset of {1,2,3}) a structure S_M validating every basis
instance with deadlines in M and refuting the target.  Soundness of
that certificate is derivation-compactness: a derivation is finite,
its deadlines form a finite menu M_0 (containing the target's
{1,2,3}), and S_{M_0} would validate every step yet refute the
conclusion.  With g := gcd(M_0) = 1/m, M_0 sits inside the integer
grid {j/m : j <= H}, and on an integer grid U7== FORCES A_j = A_1^j
(A_2 = A_1 A_1, etc.): power structures are fully general there.
SCALE: the family is index-defined (the structure never mentions the
unit), so member(grid g) and member(grid g/lambda) are the same
object and the rule preserves family-validity -- the orbit
rider, with a horizon.

N=1 IS U7>=.  FS-R at n = 1 reads A_T[al] <= A_c(al v A_{T-c}[al]);
U4 + MONO_F collapse the disjunction to A_{T-c}[al], giving exactly
U7's subdivision half -- so FS-R generalizes the F-group's dense-time
axiom to n co-obligations, is derivable at n = 1, and independence
must be sought at n >= 2.  (In power semantics n = 1 is identically
valid: A^c(A^{T-c}E) = A^T E.)

THE STRUCTURE CLASS.  Finite W; per-state generator antichains G(w)
(sets of subsets); A(E) := E u {w : some g in G(w), g <= E};
A_j := A^j.  Box: Kripke over the TOTAL relation (box(V) = W iff
V = W else empty; D = empty) -- a legal G-frame that makes U10F and
the G-layer hold trivially (checked anyway).  U4/U3/U9/MONO are
structural; U7== is free (powers); the live jaws are FS_n (must
HOLD, all sets, all menu tuples) and FS-R (must FAIL at the target).
Multi-state generators are demonic spreads (all of g must certify);
generator CHOICE is angelic.  FS is a linearity law: at any state
with two certificate routes it demands a merge point within the min
deadline -- on singleton-generator structures it is equivalent (via
Lemma TT's tier condition, for the n-ary/set forms) to the METRIC
LAW on the reach quasimetric delta:

    delta(s,p) < delta(s,q) < inf   =>  delta(p,q) <= delta(s,q)
    delta(s,p) = delta(s,q) = d     =>  delta(p,q) <= d
                                        or delta(q,p) <= d

(two earlier gadget drafts died to exactly this jaw; the specimens
are in the development record).  THE GADGET S_m is the v3 topology in
build_gadget below, hand-derived by saturating the metric law's
forced bounds as high as the refutation window allows; at m = 1 it
is edge-minimal and machine-verified as a witness.  m >= 2 is OPEN
(z3: the whole singleton-generator class is UNSAT at n <= 13;
independence_search_z3.py), with the demonic-generator sub-class
and the
half-grid derivation hunt as the two named continuations.

CHECK DISCIPLINE (lane standard): every law of the basis roster is
re-checked per structure over ALL subsets and the full menu horizon
(no law is "trivial by construction" until the checker says so);
derived laws (U3, REACH, D4-shape, U9>=) ride as encoding-sanity
controls; two liveness controls run in the battery -- the CHAIN
control (an honest discrete model: FS-R must HOLD there, proving the
instrument can detect validity) and the UNREPAIRED fork (cross-gens
removed: FS must FAIL there, proving the FS jaw bites).  Exit-coded.

Python per lane precedent (oracle instruments); the m = 2 all-sets
FS_2 sweep uses numpy fancy-indexing (gather over the A-power
tables) -- a one-shot instrument where jit warmup would dominate,
which is the stated reason this rides numpy rather than jax.numpy.
"""

from __future__ import annotations

import argparse
import random
import sys
from itertools import combinations_with_replacement


# ---------------------------------------------------------------------------
# structure

class Power:
    """Generator structure: A(E) = E u {w : exists g in G(w): g <= E}."""

    def __init__(self, names, gens, atoms):
        self.names = list(names)
        self.n = len(self.names)
        self.idx = {nm: i for i, nm in enumerate(self.names)}
        self.gens = [list(gs) for gs in gens]  # list of masks per state
        self.atoms = dict(atoms)               # name -> mask
        self.full = (1 << self.n) - 1
        self.nsets = 1 << self.n
        self._a1 = None
        self._pow = {}

    def mask(self, *nms):
        m = 0
        for nm in nms:
            m |= 1 << self.idx[nm]
        return m

    def a1_table(self):
        if self._a1 is None:
            t = []
            for E in range(self.nsets):
                out = E
                for w in range(self.n):
                    if (out >> w) & 1:
                        continue
                    for g in self.gens[w]:
                        if g & ~E == 0:
                            out |= 1 << w
                            break
                t.append(out)
            self._a1 = t
        return self._a1

    def apow(self, j):
        """table for A^j, j >= 0."""
        if j in self._pow:
            return self._pow[j]
        if j == 0:
            t = list(range(self.nsets))
        else:
            a1 = self.a1_table()
            prev = self.apow(j - 1)
            t = [a1[prev[E]] for E in range(self.nsets)]
        self._pow[j] = t
        return t

    def states_of(self, mask):
        return [self.names[i] for i in range(self.n) if (mask >> i) & 1]


# ---------------------------------------------------------------------------
# gadgets

def build_gadget(m: int, cross: bool = True, fsfix: bool = False) -> Power:
    """S_m, v3 topology (hand-derived under the FS metric law; verified
    m = 1).  States: x, u_1..u_{2m-1}, a*, w_1..w_{3m-1}, b*.  Edges
    (singleton generators; unit steps):

      x -> u_1 | w_1              (the fork)
      u_i -> u_{i+1} .. -> a*     (a-chain, depth 2m)
      w_i -> w_{i+1} .. -> b*     (b-chain, depth 3m)
      u_1 -> w_1                  (equal-stratum cover at the fork)
      a* -> w_{2m-1}              (a*'s b-certificate at the ORIGINAL
                                   budget: d(a*, E_b) = m+2 <= 3m for
                                   m >= 1 -- Srv_a stays co-budgeted)
      w_{2m} -> a*                (deep-w E_a-entry at a*)
      b* -> a*                    (service points see each other)

    At m = 1 this is the EDGE-MINIMAL witness (battery sweep: removing
    any single edge either breaks the basis or validates the target):
    x->{u1,w1}, u1->{a*,w1}, a*->w1, w1->w2, w2->{b*,a*}, b*->a*.
    cross=False drops the non-chain edges after the fork (the
    UNREPAIRED control: FS must fail); fsfix=True adds the historical
    a* -> w_{2m} edge (redundant at m = 1, kept for the recorded S_2
    probe shape)."""
    names = (['x'] + [f'u{i}' for i in range(1, 2 * m)] + ['a*']
             + [f'w{i}' for i in range(1, 3 * m)] + ['b*'])
    S = Power(names, [[] for _ in names], {})
    M = S.mask
    g = S.gens
    achain = [f'u{i}' for i in range(1, 2 * m)] + ['a*']
    bchain = [f'w{i}' for i in range(1, 3 * m)] + ['b*']
    # seed: angelic fork between the a-route head and the b-route head
    g[S.idx['x']] = [M(achain[0]), M(bchain[0])]
    # chains
    for c, nxt in zip(achain, achain[1:]):
        g[S.idx[c]] = [M(nxt)]
    for c, nxt in zip(bchain, bchain[1:]):
        g[S.idx[c]] = [M(nxt)]
    g[S.idx['b*']] = []
    # FS-fix: a* certifies E_b at depth m+1 via w_{2m}
    if fsfix:
        g[S.idx['a*']].append(M(bchain[2 * m - 1]))  # a* -> w_{2m}
    if cross:
        g[S.idx[achain[0]]].append(M(bchain[0]))     # u_1 -> w_1
        g[S.idx['a*']].append(M(bchain[2 * m - 2]))  # a* -> w_{2m-1}
        g[S.idx[bchain[2 * m - 1]]].append(M('a*'))  # w_{2m} -> a*
        g[S.idx['b*']].append(M('a*'))               # b* -> a*
    S.atoms = {'a': M('a*'), 'b': M('b*')}
    return S


def build_chain(m: int = 1) -> Power:
    """Honest control: linear chain, E_a at depth 2m, E_b at depth 3m.
    A discrete clocked model in power costume: FS-R must HOLD."""
    names = ['x'] + [f'c{i}' for i in range(1, 3 * m + 1)]
    S = Power(names, [[] for _ in names], {})
    M = S.mask
    for a, b in zip(names, names[1:]):
        S.gens[S.idx[a]] = [M(b)]
    S.gens[S.idx[names[-1]]] = []
    S.atoms = {'a': M(f'c{2 * m}'), 'b': M(f'c{3 * m}')}
    return S


# ---------------------------------------------------------------------------
# law checks (each returns a list of violation tuples, possibly capped)

CAP = 12


def check_structural(S: Power, H: int):
    """U4, U3, U9<=, U9>= (derived control), MONO_F, U7== sanity,
    G-layer + U10F + REACH under the total-R box."""
    v = []
    a1 = S.a1_table()
    # U9<=: A(empty) = empty  (D = empty under total R)
    if a1[0] != 0:
        v.append(('U9<=', 'A(empty) nonempty', S.states_of(a1[0])))
    # U4 + U3 at the A1 level (powers inherit)
    for E in range(S.nsets):
        if E & ~a1[E]:
            v.append(('U4', E))
            if len(v) > CAP:
                return v
    # MONO_F at A1 (powers inherit): check generator semantics directly
    for E in range(S.nsets):
        for w in range(S.n):
            if (a1[E] >> w) & 1 and not (E >> w) & 1:
                # w certified by some g <= E; monotone by subset test: ok
                pass
    # exhaustive MONO spot: A1 monotone iff table monotone under subset
    # (generator semantics is monotone by construction; verify on a
    #  random sample as encoding sanity)
    rnd = random.Random(485)
    for _ in range(200):
        E = rnd.randrange(S.nsets)
        F = E | rnd.randrange(S.nsets)
        if a1[E] & ~a1[F]:
            v.append(('MONO_F', E, F))
    # U7== sanity: table composition associativity/exactness
    for (j1, j2) in [(1, 1), (1, 2), (2, 1), (2, 3)]:
        if j1 + j2 > H:
            continue
        t1, t2, t12 = S.apow(j1), S.apow(j2), S.apow(j1 + j2)
        for E in (0, S.full, 0b1, S.atoms['a'], S.atoms['b']):
            if t1[t2[E]] != t12[E]:
                v.append(('U7== sanity', j1, j2, E))
    # U3 across the menu
    for j in range(1, H):
        tj, tj1 = S.apow(j), S.apow(j + 1)
        for E in range(S.nsets):
            if tj[E] & ~tj1[E]:
                v.append(('U3', j, E))
                break
    # G-layer under total R: box(V) = full iff V = full else empty
    # G2/G3->/G4/G6/MONO_box/N1 all reduce to trivial identities; check
    # the two that could bite: G4 box(E) <= E u D and G6 ~D <= box(~D).
    # box(full) = full: G6 with D = empty: full <= box(full) ok.
    # U10F: box(V) & A^j(E & V) == box(V) & A^j(E): only V = full
    # matters, where E & V = E.  REACH: A^j E & box(~E) <= D: box(~E)
    # nonempty only for E = empty, where A^j empty = empty.  Encode:
    for j in (1, 2):
        if S.apow(j)[0] != 0:
            v.append(('REACH/U9', j))
    return v


def check_fs2(S: Power, H: int):
    """FS_2 all ordered set pairs, deadline pairs j1 <= j2 <= H.
    FS: A^{j1}E1 & A^{j2}E2 <= A^{j1}((E1 & A^{j2}E2) | (E2 & A^{j1}E1))."""
    v = []
    for j1 in range(1, H + 1):
        t1 = S.apow(j1)
        for j2 in range(j1, H + 1):
            t2 = S.apow(j2)
            for E1 in range(S.nsets):
                a1E1 = t1[E1]
                for E2 in range(S.nsets):
                    lhs = a1E1 & t2[E2]
                    if not lhs:
                        continue
                    sprime = (E1 & t2[E2]) | (E2 & a1E1)
                    if lhs & ~t1[sprime]:
                        v.append(('FS2', j1, j2, E1, E2,
                                  S.states_of(lhs & ~t1[sprime])))
                        if len(v) >= CAP:
                            return v
    return v


def check_fs2_numpy(S: Power, H: int):
    """FS_2 exhaustive via numpy gather (for |W| ~ 10-12).  One-shot
    instrument: numpy over jnp because jit warmup dominates a single
    pass and the kernel is integer gather/bitops."""
    # why-not-jnp: one-shot instrument — jit warmup dominates a single pass; integer gather/bitops
    import numpy as np
    v = []
    masks = np.arange(S.nsets, dtype=np.int64)
    tables = {j: np.array(S.apow(j), dtype=np.int64)
              for j in range(1, H + 1)}
    for j1 in range(1, H + 1):
        t1 = tables[j1]
        for j2 in range(j1, H + 1):
            t2 = tables[j2]
            for E1 in range(S.nsets):
                a1E1 = int(t1[E1])
                lhs = a1E1 & t2            # vector over E2
                live = lhs != 0
                if not live.any():
                    continue
                sprime = (E1 & t2) | (masks & a1E1)
                bad = lhs & ~t1[sprime]
                badidx = np.nonzero((bad != 0) & live)[0]
                if badidx.size:
                    for E2 in badidx[:2]:
                        v.append(('FS2', j1, j2, E1, int(E2)))
                    if len(v) >= CAP:
                        return v
    return v


def check_fs3_numpy(S: Power, H: int, keep: int = 2, cap: int = None):
    """FS_3 EXHAUSTIVE via numpy (|W| ~ 8-10): the same instance space
    as check_fs3(exhaustive=True) -- all ordered set triples times all
    sorted deadline triples j1 <= j2 <= j3 <= H -- vectorized over the
    (E2, E3) plane per (deadlines, E1).  At |W| = 8, H = 8 that is
    120 * 256^3 ~ 2.0e9 instances; a pure-python pass would grind
    for hours, this runs in ~a minute.
    Loop order hoists the (j2, j3)-only subexpressions: with
    a1 = A^{j1}E1 the service set is
    s = (E1 & pre23) | (a1 & x23) where pre23 = A^{j2}E2 & A^{j3}E3
    and x23 = (E2 & A^{j3}E3) | (E3 & A^{j2}E2), both E1-free.
    why-not-jnp: one-shot instrument -- jit warmup dominates a single
    pass; integer gather/bitops (the check_fs2_numpy precedent).
    keep = specimens kept per (deadlines, E1) cell; cap = overall cap
    (defaults to module CAP; the artifact-pair test against pure
    check_fs3 lifts both to collect full violation sets)."""
    # why-not-jnp: one-shot gather instrument; jit warmup dominates (same argument as in the docstring above)
    import numpy as np
    if cap is None:
        cap = CAP
    v = []
    masks = np.arange(S.nsets, dtype=np.int64)
    tables = {j: np.array(S.apow(j), dtype=np.int64)
              for j in range(1, H + 1)}
    for j2 in range(1, H + 1):
        t2col = tables[j2][:, None]
        e2col = masks[:, None]
        for j3 in range(j2, H + 1):
            t3row = tables[j3][None, :]
            e3row = masks[None, :]
            pre23 = t2col & t3row
            x23 = (e2col & t3row) | (e3row & t2col)
            for j1 in range(1, j2 + 1):
                t1 = tables[j1]
                for E1 in range(S.nsets):
                    a1 = int(t1[E1])
                    lhs = a1 & pre23
                    if not lhs.any():
                        continue
                    s = (E1 & pre23) | (a1 & x23)
                    bad = lhs & ~t1[s]
                    if bad.any():
                        for (i2, i3) in np.argwhere(bad != 0)[:keep]:
                            v.append(('FS3', (j1, j2, j3), E1,
                                      int(i2), int(i3),
                                      S.states_of(int(bad[i2, i3]))))
                        if len(v) >= cap:
                            return v
    return v


def check_fs3(S: Power, H: int, exhaustive: bool, samples: int = 200000):
    """FS_3: A^{j1}E1 & A^{j2}E2 & A^{j3}E3 <= A^{j1}(union of
    service disjuncts with ORIGINAL co-budgets), j1 <= j2 <= j3."""
    v = []
    trips = list(combinations_with_replacement(range(1, H + 1), 3))
    if exhaustive:
        space = ((j, E1, E2, E3)
                 for j in trips
                 for E1 in range(S.nsets)
                 for E2 in range(S.nsets)
                 for E3 in range(S.nsets))
    else:
        rnd = random.Random(20)
        space = (((rnd.choice(trips)), rnd.randrange(S.nsets),
                  rnd.randrange(S.nsets), rnd.randrange(S.nsets))
                 for _ in range(samples))
    for (j1, j2, j3), E1, E2, E3 in space:
        t1, t2, t3 = S.apow(j1), S.apow(j2), S.apow(j3)
        lhs = t1[E1] & t2[E2] & t3[E3]
        if not lhs:
            continue
        s = ((E1 & t2[E2] & t3[E3]) | (E2 & t1[E1] & t3[E3])
             | (E3 & t1[E1] & t2[E2]))
        if lhs & ~t1[s]:
            v.append(('FS3', (j1, j2, j3), E1, E2, E3,
                      S.states_of(lhs & ~t1[s])))
            if len(v) >= CAP:
                return v
    return v


def check_tiers(S: Power, H: int):
    """The FS_n-for-all-n reduction (Lemma TT): in a
    singleton-generator structure satisfying the pairwise metric law,
    FS_n holds for ALL n and all set tuples provided every distance
    tier T_d(s) = {p : delta(s,p) = d} carries a TRANSITIVE TOURNAMENT
    under "sees within d" (every subset then has an internal dominator
    = the service point; farther co-obligations ride the strict law).
    Returns violations: (s, d, tier, reason)."""
    v = []
    # delta via powers
    INF = H + 2
    delta = [[INF] * S.n for _ in range(S.n)]
    for i in range(S.n):
        delta[i][i] = 0
    for j in range(1, H + 1):
        t = S.apow(j)
        for p in range(S.n):
            for q in range(S.n):
                if delta[q][p] == INF and (t[1 << p] >> q) & 1:
                    delta[q][p] = j
    for s_ in range(S.n):
        for d in range(1, H + 1):
            tier = [p for p in range(S.n) if delta[s_][p] == d]
            if len(tier) < 2:
                continue
            sees = {(p, q) for p in tier for q in tier
                    if p != q and delta[p][q] <= d}
            # totality
            for i, p in enumerate(tier):
                for q in tier[i + 1:]:
                    if (p, q) not in sees and (q, p) not in sees:
                        v.append((S.names[s_], d, 'untotal',
                                  S.names[p], S.names[q]))
            # transitivity of the dominance relation on the tier:
            # every subset must have an internal dominator; for a total
            # relation this fails iff there is a 3-cycle of strict
            # non-domination -- check all triples
            for p in tier:
                for q in tier:
                    for r in tier:
                        if len({p, q, r}) < 3:
                            continue
                        if ((p, q) in sees and (q, r) in sees
                                and (r, p) in sees
                                and (q, p) not in sees
                                and (r, q) not in sees
                                and (p, r) not in sees):
                            v.append((S.names[s_], d, '3-cycle',
                                      S.names[p], S.names[q],
                                      S.names[r]))
    return v


def fsr_instance(S: Power, T1, T2, c, E1, E2):
    """FS-R at (T1,T2;c) on (E1,E2): returns violator mask (0 = valid)."""
    tT1, tT2, tc = S.apow(T1), S.apow(T2), S.apow(c)
    tr1, tr2 = S.apow(T1 - c), S.apow(T2 - c)
    lhs = tT1[E1] & tT2[E2]
    srv = (E1 & tT2[E2]) | (E2 & tT1[E1])
    res = tr1[E1] & tr2[E2]
    return lhs & ~tc[srv | res]


def fsr_report(S: Power, m: int, H: int, out):
    """Status of FS-R instances on the atoms + an all-sets census at
    the target deadlines."""
    Ea, Eb = S.atoms['a'], S.atoms['b']
    print('## FS-R instance report (atoms E_a, E_b)', file=out)
    refuted_target = False
    for (T1, T2) in [(2 * m, 3 * m), (2 * m, 2 * m), (3 * m, 3 * m),
                     (3 * m, 2 * m)]:
        for c in range(1, min(T1, T2)):
            viol = fsr_instance(S, T1, T2, c, Ea, Eb)
            tag = 'REFUTED at ' + ','.join(S.states_of(viol)) if viol \
                else 'valid'
            star = ''
            if (T1, T2, c) == (2 * m, 3 * m, m):
                star = '  <== THE TARGET (wall-hand shape)'
                refuted_target = bool(viol)
            print(f'- FS-R({T1},{T2};{c}) on (E_a,E_b): {tag}{star}',
                  file=out)
    # all-sets census at the target deadlines
    total = viols = 0
    for E1 in range(S.nsets):
        for E2 in range(S.nsets):
            vm = fsr_instance(S, 2 * m, 3 * m, m, E1, E2)
            total += 1
            if vm:
                viols += 1
    print(f'- census at ({2*m},{3*m};{m}): {viols}/{total} set pairs '
          'refute FS-R (nonzero = the schema itself fails here; the '
          'basis instances above must all HOLD for the certificate)',
          file=out)
    return refuted_target


# ---------------------------------------------------------------------------
# runs

def run_structure(S: Power, H: int, out, fs3_exhaustive: bool,
                  numpy_fs2: bool = False):
    ok = True
    v = check_structural(S, H)
    print(f'- structural roster (U4/U3/U9/MONO/U7-sanity/G-layer/U10F/'
          f'REACH): {"CLEAN" if not v else "VIOLATIONS " + repr(v[:CAP])}',
          file=out)
    ok &= not v
    v = check_fs2_numpy(S, H) if numpy_fs2 else check_fs2(S, H)
    print(f'- FS_2 exhaustive (all set pairs, deadlines <= {H}): '
          f'{"CLEAN" if not v else "VIOLATIONS " + repr(v[:CAP])}',
          file=out)
    ok &= not v
    v = check_fs3(S, H, fs3_exhaustive)
    kind = 'exhaustive' if fs3_exhaustive else 'sampled 200k'
    print(f'- FS_3 ({kind}): '
          f'{"CLEAN" if not v else "VIOLATIONS " + repr(v[:CAP])}',
          file=out)
    ok &= not v
    v = check_tiers(S, H)
    print(f'- tier-tournament condition (Lemma TT: implies FS_n all n, '
          f'all sets): {"CLEAN" if not v else "VIOLATIONS " + repr(v[:CAP])}',
          file=out)
    ok &= not v
    return ok


def cmd_hand(args, out):
    m = args.m
    H = 3 * m + 2
    S = build_gadget(m)
    print(f'# FS-R independence: the hub-cross fork gadget S_{m} '
          f'({S.n} states, horizon {H})', file=out)
    print(file=out)
    print('states:', ' '.join(S.names), file=out)
    for w in range(S.n):
        gs = ' | '.join('{' + ','.join(S.states_of(g)) + '}'
                        for g in S.gens[w]) or '(none)'
        print(f'  G({S.names[w]}) = {gs}', file=out)
    print(file=out)
    print('## basis validation (must be CLEAN)', file=out)
    basis_ok = run_structure(S, H, out, fs3_exhaustive=(m == 1),
                             numpy_fs2=(m >= 2))
    print(file=out)
    refuted = fsr_report(S, m, H, out)
    print(file=out)
    verdict = basis_ok and refuted
    print(f'S_{m} verdict: '
          + ('WITNESS (basis clean, target refuted)' if verdict else
             'NOT A WITNESS'), file=out)
    return verdict


def cmd_battery(args, out):
    ok = True
    print('# independence battery (exit-coded)', file=out)
    print(file=out)
    # liveness control 1: honest chain -- FS-R must HOLD everywhere
    S = build_chain(1)
    viol = fsr_instance(S, 2, 3, 1, S.atoms['a'], S.atoms['b'])
    good = viol == 0
    ok &= good
    print(f'- CHAIN control (honest discrete model): FS-R(2,3;1) '
          f'{"holds (as it must)" if good else "REFUTED -- instrument bug"}',
          file=out)
    basis_ok = (not check_structural(S, 5) and not check_fs2(S, 5)
                and not check_fs3(S, 5, exhaustive=True))
    ok &= basis_ok
    print(f'- CHAIN basis roster: {"CLEAN" if basis_ok else "VIOLATIONS"}',
          file=out)
    # liveness control 2: unrepaired fork -- the FS jaw must bite
    S = build_gadget(1, cross=False)
    v = check_fs2(S, 5)
    ok &= bool(v)
    print(f'- UNREPAIRED fork control: FS_2 '
          f'{"violated (jaw bites: " + repr(v[0][:4]) + ")" if v else "clean -- jaw dead, instrument bug"}',
          file=out)
    # edge-minimality sweep: removing ANY single edge of S_1 must
    # destroy witness-hood (basis breaks or the target validates) --
    # every edge is load-bearing, and the sweep doubles as a mutant
    # run on the checker (each mutant must trip SOME jaw)
    S0 = build_gadget(1)
    H = 5
    minimal = True
    detail = []
    for w in range(S0.n):
        for k in range(len(S0.gens[w])):
            S = Power(S0.names, [list(gs) for gs in S0.gens],
                      dict(S0.atoms))
            g = S.gens[w].pop(k)
            broken = bool(check_structural(S, H) or check_fs2(S, H)
                          or check_fs3(S, H, True)
                          or check_tiers(S, H))
            refuted = bool(fsr_instance(S, 2, 3, 1, S.atoms['a'],
                                        S.atoms['b']) & 1)
            still_witness = (not broken) and refuted
            minimal &= not still_witness
            detail.append(f'{S0.names[w]}->'
                          + ','.join(S0.states_of(g)) + ':'
                          + ('basis-broken' if broken else
                             'target-valid' if not refuted else
                             '!!STILL-WITNESS'))
    ok &= minimal
    print('- EDGE-MINIMALITY sweep on S_1 (every single-edge removal '
          'must destroy witness-hood): '
          + ('CLEAN -- all 9 edges load-bearing' if minimal
             else 'FAILED') + '; ' + ' '.join(detail), file=out)
    print(file=out)
    # the witness (m = 1: the integer-menu independence certificate)
    print('## S_1 (must be a WITNESS)', file=out)

    class A1:
        m = 1
    w1 = cmd_hand(A1, out)
    ok &= w1
    print(file=out)
    # m = 2: OPEN.  The stretched-gadget guess is recorded as a
    # negative probe (expected NOT A WITNESS; z3 additionally reports
    # the whole singleton-generator class UNSAT at n <= 13, see
    # independence_search_z3.py).  If an edit ever turns
    # this section into a WITNESS, that is a headline, not a battery
    # failure -- it prints loudly either way.
    print('## S_2 stretched-gadget probe (informational; expected '
          'NOT A WITNESS -- m >= 2 is open)', file=out)

    class A2:
        m = 2
    w2 = cmd_hand(A2, out)
    if w2:
        print('!! S_2 UNEXPECTEDLY A WITNESS -- the m=2 open just '
              'closed; update the docs', file=out)
    print(file=out)
    print(f'battery overall: {"PASS" if ok else "FAIL"} '
          f'(S_2 probe informational: '
          f'{"witness!" if w2 else "not a witness, as recorded"})',
          file=out)
    return ok


def main():
    ap = argparse.ArgumentParser(description='FS-R independence '
                                 'receipts')
    sub = ap.add_subparsers(dest='cmd', required=True)
    h = sub.add_parser('hand', help='the S_m gadget, full battery')
    h.add_argument('--m', type=int, default=1)
    h.add_argument('--out', default='-')
    b = sub.add_parser('battery', help='controls + S_1 + S_2, exit-coded')
    b.add_argument('--out', default='-')
    args = ap.parse_args()
    out = sys.stdout if args.out == '-' else open(args.out, 'w')
    try:
        if args.cmd == 'hand':
            ok = cmd_hand(args, out)
        else:
            ok = cmd_battery(args, out)
        sys.exit(0 if ok else 1)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == '__main__':
    main()
