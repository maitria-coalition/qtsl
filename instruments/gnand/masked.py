#!/usr/bin/env python3
r"""masked -- the masked-branching witness tier.

THE FINDING: the per-trajectory certificate family
(GB-PIGEON and kin) is sound only for BRANCH-AT-SEED models, where
post-seed states are linear and graded boxes therefore bind along each
branch's own schedule.  Over the full clocked class, worst-case debuts
are sups over ALL continuations, so a sibling branch that delays a
service MASKS a same-path proximity: at every state before x's
service, a continuation serving x late keeps AF<=1[x] false there,
and the box ~(AF<=1[x] & AF<=1[y]) is satisfied even though this
path's x- and y-services sit within one unit of each other.
Branch-RESTRICTION is unsound for graded boxes (removing branches
strengthens A-facts), which is exactly why "refutes every trajectory"
does not refute the tree.

The load-bearing witness: a 57-state deep-branching clocked model of
the pigeon-3 specimen (three atoms pending at stage 2, pairwise
gnand(.,1,.,1)) -- the specimen GB-PIGEON "refutes".  Grid 1/4;
states (k, U, s) = (quarter-units elapsed at entry, unserved set
after this state's service, serving atom or idle); every path serves
two atoms strictly before time 1 and the third by 2; at every state
each unserved atom keeps a delayer continuation reaching time 2, so
no state ever has two atoms with worst-case debut <= 1.  tdenot
(the clocked oracle, ground truth) confirms the full seed formula.

Consequence chain, each step machine-checked or propositional:
  1. pigeon-3 is clocked-SATISFIABLE (this witness);
  2. by soundness its Lindenbaum cell is CONSISTENT;
  3. every pattern-form offer at that cell (Lemma SUCC-CON-P) is
     refused by a PROPOSITIONAL derivation: burst halves with |S| >= 2
     contain a gnand pair at A<=1 against the box member; boundary
     halves with |P \ S| >= 2 likewise; singleton and empty patterns
     are refused at their boundary halves;
  4. hence Lemma SUCC-CON-P as stated is FALSE: a consistent live cell
     with every offer deductively refused.  The pattern form's burst
     A<=1-tightening asserts cell-level facts that masking keeps
     false; the demand's early services live in the SCHEDULE, not in
     the cell.
This module checks 1 and 3 mechanically (2 is soundness, 4 is modus
tollens); check_masked is exit-coded and rides the cores battery.
"""

from __future__ import annotations

import sys
from fractions import Fraction

from oracle import atom, f_not, f_and, pg
from timed import INF, TModel, tstructure, tdenot, pfle
from cores import GSpec, gspec_formula, screen

ZERO = Fraction(0)
ATOMS = (0, 1, 2)
Q = Fraction(1, 4)

PIGEON = GSpec(name='pigeon-3', atoms=(0, 1, 2),
               pend=((0, 2), (1, 2), (2, 2)),
               gnand=((0, 1, 1, 1), (1, 1, 2, 1), (0, 1, 2, 1)))


def _legal(k, U, s):
    """Hand-derived legality: second service strictly before 1,
    third by 2, no dead states (a reachable dead state has vacuous
    A-facts and violates every gnand box)."""
    n = len(U)
    if s == '.':
        if n == 3:
            return k in (0, 1)
        if n == 2:
            return k == 2
        if n == 1:
            return 3 <= k <= 7
        return False
    if n == 2:
        return k in (1, 2)
    if n == 1:
        return k in (2, 3)
    if n == 0:
        return 3 <= k <= 8
    return False


def build_masked_pigeon():
    """The 57-state masked model; returns (tm, seed_index)."""
    states, index = [], {}

    def add(st):
        if st not in index:
            index[st] = len(states)
            states.append(st)
        return index[st]

    for k in range(0, 9):
        for mask in range(8):
            U = frozenset(a for a in ATOMS if mask >> a & 1)
            for s in ('.',) + ATOMS:
                if s != '.' and s in U:
                    continue
                if _legal(k, U, s):
                    add((k, U, s))
    tail = add(('tail', frozenset(), '.'))
    succ = {i: set() for i in range(len(states))}
    for st, i in list(index.items()):
        if st[0] == 'tail':
            continue
        k, U, s = st
        nxt = (k + 1, U, '.')
        if nxt in index:
            succ[i].add(index[nxt])
        for x in sorted(U):
            nxt = (k + 1, U - {x}, x)
            if nxt in index:
                succ[i].add(index[nxt])
        if not U and s != '.':
            succ[i].add(tail)
    live = set(range(len(states)))
    changed = True
    while changed:
        changed = False
        for i in list(live):
            if states[i][0] == 'tail':
                continue
            if not (succ[i] & live):
                live.discard(i)
                changed = True
    order = sorted(live)
    remap = {i: j for j, i in enumerate(order)}
    n = len(order)
    adj = [0] * n
    stay = 0
    dwell = []
    val = [0, 0, 0]
    for j, i in enumerate(order):
        st = states[i]
        for t in succ[i]:
            if t in live:
                adj[j] |= 1 << remap[t]
        if st[0] == 'tail':
            stay |= 1 << j
            dwell.append(INF)
        else:
            dwell.append(Q)
        if st[2] != '.' and st[2] in ATOMS:
            val[st[2]] |= 1 << j
    assert all(adj[j] or (stay >> j & 1) for j in range(n)), \
        'dead state survived pruning'
    tm = TModel(tstructure(n, tuple(adj), stay, tuple(dwell)),
                tuple(val))
    return tm, remap[index[(0, frozenset(ATOMS), '.')]], n


def offer_refusals_propositional():
    """Step 3: every pattern-form offer at the pigeon cell carries a
    propositional refusal witness.  Patterns S over three stage-2
    bases (due = empty): burst J_S adds A<=1 for S; boundary R_S is
    the joint decrement of the complement.  A gnand box member
    ~(A1 x & A1 y) refutes any half containing both A1-facts.
    Returns the witness table (all 8 patterns refused)."""
    import itertools
    pairs = {frozenset((0, 1)), frozenset((1, 2)), frozenset((0, 2))}
    table = {}
    for r in range(4):
        for S in itertools.combinations(ATOMS, r):
            Sf = frozenset(S)
            comp = frozenset(ATOMS) - Sf
            if any(p <= Sf for p in pairs):
                table[Sf] = ('burst', 'gnand pair at A<=1 in S: '
                             'box member + conjuncts, propositional')
            elif any(p <= comp for p in pairs):
                table[Sf] = ('boundary', 'gnand pair at A<=1 in the '
                             'remainder decrement, propositional')
            else:
                table[Sf] = ('OPEN', 'no propositional refusal')
    return table


def check_masked(out) -> bool:
    print('## masked: the deep-branching witness tier ('
          'per-trajectory certificates are builder-class only; '
          'SUCC-CON-P as stated is refuted)', file=out)
    ok = True
    tm, seed, n = build_masked_pigeon()
    g = gspec_formula(PIGEON)
    holds = tdenot(g, tm)[seed].contains(ZERO)
    ok &= holds
    print(f'- pigeon-3 masked witness: {n} states, full seed formula '
          f'{"HOLDS at seed (clocked-SAT; GB-PIGEON is class-unsound)" if holds else "!! FAILS -- witness broken"}',
          file=out)
    # the negative facts the masking provides (not asserted by the
    # spec; checked as the mechanism's signature): ~A<=1[x] at seed
    masked_negs = all(
        not tdenot(pfle(Fraction(1), atom(x)), tm)[seed].contains(ZERO)
        for x in ATOMS)
    ok &= masked_negs
    print(f'- masking signature: worst-case debut > 1 for every atom '
          f'at the seed {"confirmed" if masked_negs else "!! ABSENT"}',
          file=out)
    # the specimen is still (correctly) refused by the branch-at-seed
    # instruments: screen silent, certificate fires -- the label now
    # reads "builder-class infeasible", not "unsatisfiable"
    from cores import semantic_certificate
    cert = semantic_certificate(PIGEON, deep=False)
    print(f'- branch-at-seed tier: certificate '
          f'{"fires (GB-PIGEON) -- sound for that class, refuted as a satisfiability claim by the witness above" if cert else "!! silent"}',
          file=out)
    ok &= cert is not None
    tbl = offer_refusals_propositional()
    bad = {tuple(sorted(S)): v for S, v in tbl.items() if v[0] == 'OPEN'}
    ok &= not bad
    print(f'- pattern-form offers at the pigeon cell: 8/8 refused '
          f'propositionally ({sum(1 for v in tbl.values() if v[0] == "burst")} burst, '
          f'{sum(1 for v in tbl.values() if v[0] == "boundary")} boundary)'
          + (f' !! OPEN: {bad}' if bad else
             ' -- consistent cell, all offers refused: SUCC-CON-P '
             'as stated is FALSE'), file=out)
    print(file=out)
    return ok


def main():
    ok = check_masked(sys.stdout)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
