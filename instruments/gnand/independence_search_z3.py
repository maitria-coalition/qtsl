#!/usr/bin/env python3
"""z3 search for S_m gadgets (FS-R independence).

Two-stage CEGIS: z3 proposes a unit-edge digraph on n states satisfying
the NECESSARY first-order skeleton of the certificate --

  premise   d(x,a*) = 2m, d(x,b*) = 3m
  refute    no state within m of x is a service point or joint-residual
            carrier (E_a = {a*}, E_b = {b*} singletons)
  FS metric law (pairwise singleton form; necessary for FS_2):
            d(s,p) < d(s,q) < inf  =>  d(p,q) <= d(s,q)
            d(s,p) = d(s,q) = d    =>  d(p,q) <= d  or  d(q,p) <= d

-- and independence.py's exhaustive checker then verifies the FULL basis
(all sets, FS_2 exhaustive, FS_3 sampled/exhaustive).  A verification
failure adds the model as a blocking clause and loops.  UNSAT at a
given n is evidence (n-bounded, singleton-generator class) that no
gadget exists there -- the obstruction data for the leg's report.

Distances are Int variables linked to Boolean reachability layers
R_k (k <= H); infinity is encoded as H+1.
"""

from __future__ import annotations

import argparse
import sys

import z3

sys.path.insert(0, '.')
from independence import Power, check_structural, check_fs2, check_fs3, \
    fsr_instance  # noqa: E402


def search(m: int, n: int, max_models: int = 40, verbose: bool = True,
           fs3_exhaustive: bool = False):
    """Returns a verified Power witness or None (UNSAT / models exhausted)."""
    H = 3 * m + 2
    INF = H + 1
    X, A, B = 0, 1, 2  # designated: x, a*, b*
    s = z3.Solver()
    adj = [[z3.Bool(f'e_{i}_{j}') if i != j else z3.BoolVal(False)
            for j in range(n)] for i in range(n)]
    # reachability layers
    R = [[[z3.Bool(f'R{k}_{i}_{j}') for j in range(n)] for i in range(n)]
         for k in range(H + 1)]
    for i in range(n):
        for j in range(n):
            s.add(R[0][i][j] == (i == j))
    for k in range(1, H + 1):
        for i in range(n):
            for j in range(n):
                step = z3.Or([z3.And(adj[i][r], R[k - 1][r][j])
                              for r in range(n)])
                s.add(R[k][i][j] == z3.Or(R[k - 1][i][j], step))
    # dist ints
    dist = [[z3.Int(f'd_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            d = dist[i][j]
            s.add(d >= 0, d <= INF)
            for k in range(H + 1):
                s.add((d <= k) == R[k][i][j])
    # premise (relaxed to <=; the refutation clause rules out the
    # too-fast cases itself, so this covers e.g. d(x,a*) = 2m-1)
    s.add(dist[X][A] <= 2 * m)
    s.add(dist[X][B] <= 3 * m)
    # refutation: forall st within m of x: not Srv_a / Srv_b / Res
    for st in range(n):
        within = dist[X][st] <= m
        srv_a = z3.And(st == A, dist[A][B] <= 3 * m)
        srv_b = z3.And(st == B, dist[B][A] <= 2 * m)
        res = z3.And(dist[st][A] <= m, dist[st][B] <= 2 * m)
        s.add(z3.Implies(within, z3.Not(z3.Or(srv_a, srv_b, res))))
    # FS pairwise metric law
    for st in range(n):
        for p in range(n):
            for q in range(n):
                if len({st, p, q}) < 3:
                    continue
                dp, dq = dist[st][p], dist[st][q]
                fin = z3.And(dp <= H, dq <= H)
                strict = z3.Implies(
                    z3.And(fin, dp < dq), dist[p][q] <= dq)
                equal = z3.Implies(
                    z3.And(fin, dp == dq),
                    z3.Or(dist[p][q] <= dq, dist[q][p] <= dp))
                s.add(strict, equal)
    # mild symmetry break: non-designated states are reachable from x
    for st in range(3, n):
        s.add(dist[X][st] <= H)

    tried = 0
    while tried < max_models:
        r = s.check()
        if r != z3.sat:
            if verbose:
                print(f'  z3: {r} at n={n} after {tried} candidate(s)')
            return None
        mdl = s.model()
        tried += 1
        edges = [(i, j) for i in range(n) for j in range(n)
                 if i != j and z3.is_true(mdl.eval(adj[i][j]))]
        names = (['x', 'a*', 'b*']
                 + [f's{i}' for i in range(3, n)])
        S = Power(names, [[] for _ in range(n)], {})
        for (i, j) in edges:
            S.gens[i].append(1 << j)
        S.atoms = {'a': 1 << 1, 'b': 1 << 2}
        v = check_structural(S, H)
        v2 = check_fs2(S, H) if not v else ['skip']
        v3 = check_fs3(S, H, exhaustive=fs3_exhaustive) \
            if not v and not v2 else ['skip']
        tgt = fsr_instance(S, 2 * m, 3 * m, m, S.atoms['a'], S.atoms['b'])
        refuted = bool(tgt & 1)  # violated at x (bit 0)
        if not v and not v2 and not v3 and refuted:
            if verbose:
                print(f'  VERIFIED witness at n={n} '
                      f'(candidate {tried}): edges={edges}')
            return S
        if verbose:
            why = ('structural' if v else 'FS2' if v2 else
                   'FS3' if v3 else 'target-not-refuted-at-x')
            print(f'  candidate {tried} failed full verification ({why}); '
                  'blocking')
        s.add(z3.Not(z3.And([adj[i][j] if (i, j) in set(edges)
                             else z3.Not(adj[i][j])
                             for i in range(n) for j in range(n)
                             if i != j])))
    if verbose:
        print(f'  model budget exhausted at n={n}')
    return None


def search_sets(m: int, n: int, max_models: int = 25,
                verbose: bool = True):
    """Widened search: E_a, E_b are FREE SET variables (the FS-R schema
    refutes at any set pair), premise relaxed to <=.  The metric law
    stays (it is forced by singleton FS instances regardless).  Full
    python verification per candidate as in `search`."""
    H = 3 * m + 2
    INF = H + 1
    X = 0
    s = z3.Solver()
    adj = [[z3.Bool(f'e_{i}_{j}') if i != j else z3.BoolVal(False)
            for j in range(n)] for i in range(n)]
    R = [[[z3.Bool(f'R{k}_{i}_{j}') for j in range(n)] for i in range(n)]
         for k in range(H + 1)]
    for i in range(n):
        for j in range(n):
            s.add(R[0][i][j] == (i == j))
    for k in range(1, H + 1):
        for i in range(n):
            for j in range(n):
                step = z3.Or([z3.And(adj[i][r], R[k - 1][r][j])
                              for r in range(n)])
                s.add(R[k][i][j] == z3.Or(R[k - 1][i][j], step))
    dist = [[z3.Int(f'd_{i}_{j}') for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            d = dist[i][j]
            s.add(d >= 0, d <= INF)
            for k in range(H + 1):
                s.add((d <= k) == R[k][i][j])
    Ea = [z3.Bool(f'Ea_{i}') for i in range(n)]
    Eb = [z3.Bool(f'Eb_{i}') for i in range(n)]
    # set-distance layers: dA[i] <= k iff some j in Ea with R_k(i,j)
    dA = [z3.Int(f'dA_{i}') for i in range(n)]
    dB = [z3.Int(f'dB_{i}') for i in range(n)]
    for i in range(n):
        s.add(dA[i] >= 0, dA[i] <= INF, dB[i] >= 0, dB[i] <= INF)
        for k in range(H + 1):
            s.add((dA[i] <= k) == z3.Or([z3.And(Ea[j], R[k][i][j])
                                         for j in range(n)]))
            s.add((dB[i] <= k) == z3.Or([z3.And(Eb[j], R[k][i][j])
                                         for j in range(n)]))
    # premise (relaxed)
    s.add(dA[X] <= 2 * m, dB[X] <= 3 * m)
    # refutation
    for st in range(n):
        within = dist[X][st] <= m
        srv_a = z3.And(Ea[st], dB[st] <= 3 * m)
        srv_b = z3.And(Eb[st], dA[st] <= 2 * m)
        res = z3.And(dA[st] <= m, dB[st] <= 2 * m)
        s.add(z3.Implies(within, z3.Not(z3.Or(srv_a, srv_b, res))))
    # FS pairwise metric law (state singletons; necessary regardless)
    for st in range(n):
        for p in range(n):
            for q in range(n):
                if len({st, p, q}) < 3:
                    continue
                dp, dq = dist[st][p], dist[st][q]
                fin = z3.And(dp <= H, dq <= H)
                s.add(z3.Implies(z3.And(fin, dp < dq),
                                 dist[p][q] <= dq))
                s.add(z3.Implies(z3.And(fin, dp == dq),
                                 z3.Or(dist[p][q] <= dq,
                                       dist[q][p] <= dp)))
    for st in range(1, n):
        s.add(dist[X][st] <= H)

    tried = 0
    while tried < max_models:
        r = s.check()
        if r != z3.sat:
            if verbose:
                print(f'  z3(sets): {r} at n={n} after {tried} '
                      'candidate(s)')
            return None
        mdl = s.model()
        tried += 1
        edges = [(i, j) for i in range(n) for j in range(n)
                 if i != j and z3.is_true(mdl.eval(adj[i][j]))]
        ea = sum(1 << i for i in range(n)
                 if z3.is_true(mdl.eval(Ea[i])))
        eb = sum(1 << i for i in range(n)
                 if z3.is_true(mdl.eval(Eb[i])))
        names = ['x'] + [f's{i}' for i in range(1, n)]
        S = Power(names, [[] for _ in range(n)], {})
        for (i, j) in edges:
            S.gens[i].append(1 << j)
        S.atoms = {'a': ea, 'b': eb}
        v = check_structural(S, H)
        v2 = check_fs2(S, H) if not v else ['skip']
        v3 = check_fs3(S, H, exhaustive=False) \
            if not v and not v2 else ['skip']
        tgt = fsr_instance(S, 2 * m, 3 * m, m, ea, eb)
        refuted = bool(tgt & 1)
        if not v and not v2 and not v3 and refuted:
            if verbose:
                print(f'  VERIFIED witness at n={n} (candidate {tried}): '
                      f'edges={edges} Ea={ea:0{n}b} Eb={eb:0{n}b}')
            return S
        if verbose:
            why = ('structural' if v else 'FS2' if v2 else
                   'FS3' if v3 else 'target-not-refuted-at-x')
            print(f'  candidate {tried} failed ({why}); blocking')
        s.add(z3.Not(z3.And(
            [adj[i][j] if (i, j) in set(edges) else z3.Not(adj[i][j])
             for i in range(n) for j in range(n) if i != j]
            + [Ea[i] if (ea >> i) & 1 else z3.Not(Ea[i])
               for i in range(n)]
            + [Eb[i] if (eb >> i) & 1 else z3.Not(Eb[i])
               for i in range(n)])))
    if verbose:
        print(f'  model budget exhausted at n={n}')
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, default=2)
    ap.add_argument('--nmin', type=int, default=11)
    ap.add_argument('--nmax', type=int, default=13)
    ap.add_argument('--max-models', type=int, default=40)
    ap.add_argument('--sets', action='store_true',
                    help='E_a/E_b free set variables, premise relaxed')
    args = ap.parse_args()
    for n in range(args.nmin, args.nmax + 1):
        print(f'# m={args.m}, n={n}' + (' [sets]' if args.sets else ''))
        fn = search_sets if args.sets else search
        S = fn(args.m, n, args.max_models)
        if S is not None:
            print('states:', ' '.join(S.names))
            for w in range(S.n):
                gs = ' | '.join('{' + ','.join(S.states_of(g)) + '}'
                                for g in S.gens[w]) or '(none)'
                print(f'  G({S.names[w]}) = {gs}')
            print('Ea =', S.states_of(S.atoms['a']),
                  ' Eb =', S.states_of(S.atoms['b']))
            sys.exit(0)
    sys.exit(1)


if __name__ == '__main__':
    main()
