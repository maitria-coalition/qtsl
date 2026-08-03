#!/usr/bin/env python3
r"""family -- the masked-family builder.

Generalizes masked.py's hand-built witness construction (the
(k, U, s) grid graph) into a masked-family builder for arbitrary
GSpec cores, so specimens the branch-at-seed builder refuses can be
probed for masking-SAT mechanically.

THE FAMILY.  Fix a grid Q = 1/m.  States are (k, O, s):
  k  -- grid units elapsed at entry (time k*Q);
  O  -- the open-obligation map, a frozenset of (atom, deadline in
        grid units): every continuation must serve each open atom by
        its absolute deadline (min-law kept by construction: at most
        one entry per atom, tightenings take min);
  s  -- '.' (idle), an atom being served (true exactly during this
        state's dwell), or ('E', eid) (a voluntary escape visit: the
        escape's pos atoms true during the dwell).
Transitions: delay (k+1, O, '.'); serve x for (x,D) in O, removing x
and firing rows from x at k+1; visit escape eid (firing rows from its
pos atoms).  Every state's dwell is Q; when O empties the path exits
to an all-false stay tail.  Branching is TOTAL over these options --
that totality IS the masking: every unserved obligation retains, at
every state, a delayer continuation reaching its absolute deadline,
so worst-case debuts sit at (deadline - now) rather than at any
branch's schedule, exactly the Finding-11 mechanism.

LEGALITY (generation-time pruning, all NECESSARY conditions):
  EDF     -- open obligations sorted by deadline D_(1) <= D_(2) <= ..
             must satisfy k + i <= D_(i) (services are serialized,
             one per grid step): a state past this bound has a dead
             obligation on every continuation;
  HOT     -- for gnand(x,d1,y,d2): A<=d[a] is FORCED TRUE at any
             state where a is being served (reflexive) or a's open
             deadline cap D_a - k <= d*m (the deadline-cap lemma:
             every continuation serves within the window); a state
             where both sides are forced is illegal in every model
             extension -- prune;
  XHOT    -- xnand(x,y,d): serving x with y's cap inside the window;
  LOCKCAP -- pattern-capable escape visits for a lock-T escape sit at
             k <= T*m - 1 (a later pattern instance would hold box-nu
             debuts above T on every path through it).
These prune to a candidate graph; then the EXACT pass computes
worst-case debuts per (state, atom) by the longest-path recursion
(backward over k -- the graph is acyclic in k) and re-checks every
graded box pointwise; violators are pruned and the pass iterates.
Pruning only removes trajectories, which only SHRINKS sups, which
only strengthens A-facts, so the loop is monotone and terminates;
a seed death is a family refusal (sound for the family only).

Entry-point checks suffice: dwells are uniformly Q and all deadlines
are integral, so by the grid-closure/interior-control lemmas
every relevant formula is constant on dwell interiors (all thresholds
are on-grid; integer arithmetic makes the strict/closed edges exact).

GROUND TRUTH: every candidate the family emits is confirmed with
tdenot (the clocked oracle) against the FULL seed formula; core
(esc-free) failure after a clean arithmetic pass is an instrument
ALARM (the proposer's arithmetic is then wrong, not the specimen).
Escapes ride tdenot entirely: when the plain grid fails only the
escape conjuncts, single-atom TIGHTENING variants are retried (the
seed deadline of one atom lowered through the grid menu) -- schedule
tightening is the family's own "cells loose, schedule tight" knob:
it prunes delayers, making A<=d[y] spos conjuncts true at witness
states that masking would otherwise keep false.

VERDICTS: MASKED-SAT (tdenot-confirmed model emitted; specimen is
clocked-satisfiable -- reclassifies a REFUSED-SEMANTIC specimen) and
FAMILY-REFUSED (no member of this family satisfies the specimen;
clocked-SAT stays open unless a class-sound argument closes it --
growth-guard trips report as refusals with the guard named).  Rows
fire DYNAMICALLY at every instance state, so multi-firing specimens
are in scope.  The sweep re-runs the constructive tier's random
population (same seed), re-classifies, and probes every
certificate-refused specimen.

Python as orchestration-class code (tiny
exact search spaces, Fractions; the state graphs here are hundreds of
nodes).

THE WINGED FAMILY + THE MS INSTRUMENTS.  Three additions:
  WINGS   -- forcing wings mechanized as FORCED-SHADOW OBLIGATIONS:
             (i) an escape visit attaches its spos conjuncts as fresh
             obligations (y, k1 + d*m) -- the witness's A<=d[y] is
             then CAP-forced on every continuation, structurally
             (spos at a witness is not optional, so this is not a
             search choice); (ii) a candidate state matching a lock
             pattern at k >= T*m is never admitted bare -- it either
             takes a shadow obligation falsifying one sneg conjunct
             (the grand102 chaser, mechanized: the shadow funnels
             every continuation through a target service inside the
             window) or is dropped (generation-time LOCK-TIGHTEN,
             theorem-backed for the bare case).  Pattern-hood at
             generation reads the CAP formula (state-local, so the
             non-monotonicity that barred LOCK-PRUNE from spos
             patterns never arises); cap-vs-exact divergences are
             caught by tdenot at emission, as everywhere else.
  COLLAPSE -- the box-saturated-pattern certificate (class-SOUND,
             unlike generic conjunct ESC-LOCK): a lock pattern whose
             every conjunct is box-forced at every instance of its
             pos atom collapses to the bare pattern, re-enabling
             LOCK-TIGHTEN and the three ESC-LOCK prongs.
  MS      -- pure-gnand decision-form instruments: the law
             feasibility checker, the serialization constants, the
             minimal-grid sweep (the m = 2 conjecture's empirical
             judge), and the CAP-invariant probe (the sufficiency
             lemma's shadow).
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction

from oracle import atom, f_not, f_and, pg
from timed import INF, TModel, tstructure, tdenot, pfle
from cores import (GSpec, Esc, gspec_formula, graded_core, screen,
                        semantic_certificate, build_core_model, Refusal,
                        random_gspec, burst_spec, g_roster)
from masked import PIGEON

ZERO = Fraction(0)
IDLE = '.'


# ---------------------------------------------------------------------------
# the grid family

def _k_cap(gs: GSpec, m: int) -> int:
    """Horizon: max seed deadline plus single-firing row extensions."""
    base = max([s for x, s in gs.pend], default=0)
    base = max([base] + [h for z, h in gs.avoid])
    rows_d = sum(d for x, y, d in gs.rows)
    locks = max([e.lock for e in gs.esc if e.lock is not None],
                default=0)
    return (base + rows_d + max(locks, 0) + 1) * m


def _fire_rows(gs: GSpec, O: dict, atoms_true, k1: int, m: int):
    """Row firings from an instance of atoms_true at grid time k1:
    each row x->y with x in atoms_true opens/tightens y's obligation
    to k1 + d*m.  O is a dict atom->deadline (grid units), mutated
    copy returned."""
    O = dict(O)
    for x, y, d in gs.rows:
        if x in atoms_true:
            dl = k1 + d * m
            O[y] = min(O.get(y, dl), dl)
    return O


def _edf_ok(O: dict, k: int) -> bool:
    ds = sorted(O.values())
    return all(k + i + 1 <= D for i, D in enumerate(ds))


def _forced_due(O: dict, k: int, a, s_atoms, d_grid: int) -> bool:
    """A<=d[a] forced TRUE at this state: a true now (reflexive), or
    a's open deadline cap sits inside the window (deadline-cap
    lemma)."""
    if a in s_atoms:
        return True
    return a in O and O[a] - k <= d_grid


def _state_atoms(gs: GSpec, s):
    if s == IDLE:
        return frozenset()
    if isinstance(s, tuple) and s[0] == 'E':
        return frozenset(gs.esc[s[1]].pos)
    return frozenset((s,))


def _hard_legal(gs: GSpec, m: int, k: int, O: dict, s) -> bool:
    """Generation-time necessary conditions (EDF + HOT + XHOT)."""
    if not _edf_ok(O, k):
        return False
    ats = _state_atoms(gs, s)
    for x, y in gs.disj:
        if x in ats and y in ats:
            return False
    for x, d1, y, d2 in gs.gnand:
        if _forced_due(O, k, x, ats, d1 * m) \
                and _forced_due(O, k, y, ats, d2 * m):
            return False
    for x, y, d in gs.xnand:
        if x in ats and _forced_due(O, k, y, ats, d * m):
            return False
    return True


def _late_lock_patterns(gs: GSpec, m: int, k: int, O: dict, s):
    """Lock-escapes whose pattern this state satisfies at or past the
    lock horizon, under the CAP-reading of A-facts (state-local:
    reflexive service or open-obligation cap inside the window).
    The cap-reading under-detects spos-pattern-hood and over-detects
    sneg-pattern-hood (exact debuts only shrink below caps); both
    directions are family-safe -- over-pruning weakens refusals
    only, under-pruning is caught by tdenot at emission."""
    ats = _state_atoms(gs, s)
    out = []
    for e in gs.esc:
        if e.lock is None or k < e.lock * m:
            continue
        if not set(e.pos) <= ats or set(e.neg) & ats:
            continue
        if any(not _forced_due(O, k, y, ats, d * m) for y, d in e.spos):
            continue
        if any(_forced_due(O, k, y, ats, d * m) for y, d in e.sneg):
            continue
        out.append(e)
    return out


def _wing_expand(gs: GSpec, m: int, nxt, stats):
    """The forcing-wing discipline at candidate generation: a state
    matching a lock pattern at k >= T*m is not admitted bare.  Each
    sneg conjunct of a violated pattern offers a FORCED-SHADOW
    variant -- the obligation (y, k + d*m), which cap-falsifies the
    conjunct and funnels every continuation through a y-service
    inside the window (the grand102 chaser, mechanized).  A pattern
    with no sneg conjunct offers nothing: the candidate is dropped
    (generation-time LOCK-TIGHTEN; theorem-backed when bare)."""
    nk, nOf, ns = nxt
    late = _late_lock_patterns(gs, m, nk, dict(nOf), ns)
    if not late:
        return [nxt]
    outs = []
    snegs = sorted({(y, d) for e in late for y, d in e.sneg})
    for y, d in snegs:
        O2 = dict(nOf)
        dl = nk + d * m
        O2[y] = min(O2.get(y, dl), dl)
        if _late_lock_patterns(gs, m, nk, O2, ns):
            continue        # another pattern still hot: one shadow
        stats['shadows'] += 1               # per candidate (see note)
        outs.append((nk, frozenset(O2.items()), ns))
    return outs


def _grid_states(gs: GSpec, m: int, tighten: dict, stats=None):
    """Forward reachability from the seed under hard legality.
    Returns (states list, index, succ dict, seed_key, tail_key) or a
    Refusal.  tighten: atom -> grid deadline override for the SEED
    obligation (the schedule-tightening knob).  stats (optional
    dict): wing bookkeeping -- 'shadows' counts forced-shadow
    variants admitted, 'spos_shadows' counts visit-attached spos
    obligations."""
    if stats is None:
        stats = {'shadows': 0, 'spos_shadows': 0}
    K = _k_cap(gs, m)
    seed_O = {}
    for x, s in gs.pend:
        seed_O[x] = min(s * m, tighten.get(x, s * m))
    seed = (0, frozenset(seed_O.items()), IDLE)
    if not _hard_legal(gs, m, 0, seed_O, IDLE):
        raise Refusal('seed state hard-illegal (forced box violation '
                      'or EDF-dead at time 0)')
    index, states, succ = {}, [], {}
    lock_of = {eid: e.lock for eid, e in enumerate(gs.esc)}

    def add(st):
        if st not in index:
            index[st] = len(states)
            states.append(st)
            succ[st] = set()
        return st

    add(seed)
    tail = ('tail', frozenset(), IDLE)
    frontier = [seed]
    while frontier:
        st = frontier.pop()
        k, Of, s = st
        O = dict(Of)
        k1 = k + 1
        cands = []
        if not O:
            # obligation-free: the stay tail is always available, and
            # -- when the specimen carries escapes -- so is POST-BUSY
            # idling with escape visits (the branch-at-seed builder's
            # commonest escape placement; without these states the
            # family would refuse every post-busy-hosted escape for a
            # structural non-reason)
            if tail not in index:
                add(tail)
            succ[st].add(tail)
            if not gs.esc or k1 > K:
                continue
            cands.append((k1, Of, IDLE))
        else:
            if k1 > K:
                continue
            cands.append((k1, Of, IDLE))                # delay
            for x in sorted(O):                         # serve x
                O2 = dict(O)
                del O2[x]
                O2 = _fire_rows(gs, O2, (x,), k1, m)
                cands.append((k1, frozenset(O2.items()), x))
        for eid, e in enumerate(gs.esc):                # escape visit
            T = lock_of[eid]
            if T is not None and k1 > T * m - 1:
                continue
            O2 = _fire_rows(gs, O, e.pos, k1, m)
            for y, d in e.spos:     # forced-shadow: the witness's
                dl = k1 + d * m     # spos conjunct is structural,
                if O2.get(y, dl + 1) > dl:      # not a search choice
                    O2[y] = dl
                    stats['spos_shadows'] += 1
            cands.append((k1, frozenset(O2.items()), ('E', eid)))
        for cand in cands:
            for nxt in _wing_expand(gs, m, cand, stats):
                nk, nOf, ns = nxt
                if len(nOf) > 12:
                    raise Refusal('obligation map exceeded 12 entries '
                                  '(row-firing growth)')
                if len(states) > 200000:
                    raise Refusal('state explosion (>200k grid states)')
                if _hard_legal(gs, m, nk, dict(nOf), ns):
                    if nxt not in index:
                        add(nxt)
                        frontier.append(nxt)
                    succ[st].add(nxt)
    return states, index, succ, seed, tail


def _exact_pass(gs: GSpec, m: int, states, succ, seed, tail):
    """The exact fixpoint: prune dead-ends, restrict to reachable,
    compute exact worst-case debuts (longest path over max-dwell
    continuations), re-check every graded box pointwise; iterate.
    Returns (live set, debuts dict) or raises Refusal when the seed
    dies.  debuts: state -> {atom: grid debut or None(=infinite)}."""
    live = set(states)

    def prune_structure():
        changed = True
        while changed:
            changed = False
            for st in list(live):
                if st == tail:
                    continue
                if not any(t in live for t in succ[st]):
                    live.discard(st)
                    changed = True
            reach, stack = {seed} & live, [s for s in (seed,)
                                           if s in live]
            while stack:
                st = stack.pop()
                for t in succ[st]:
                    if t in live and t not in reach:
                        reach.add(t)
                        stack.append(t)
            if reach != live:
                live.intersection_update(reach)
                changed = True

    atoms = set(gs.atoms)
    while True:
        prune_structure()
        if seed not in live:
            raise Refusal('seed pruned (family infeasible)')
        order = sorted((st for st in live if st != tail),
                       key=lambda st: -st[0])
        deb = {st: {} for st in live}
        if tail in live:
            deb[tail] = {a: None for a in atoms}
        for st in order:
            ats = _state_atoms(gs, st[2])
            row = {}
            for a in atoms:
                if a in ats:
                    row[a] = 0
                    continue
                worst = -1
                for t in succ[st]:
                    if t not in live:
                        continue
                    d = deb[t].get(a)
                    if d is None:
                        worst = None
                        break
                    worst = max(worst, d)
                row[a] = None if worst is None else worst + 1
            deb[st] = row
        bad = set()
        for st in live:
            if st == tail:
                continue
            k = st[0]
            ats = _state_atoms(gs, st[2])
            d_of = deb[st]

            def due(a, w):
                x = 0 if a in ats else d_of.get(a)
                return x is not None and x <= w
            for x, d1, y, d2 in gs.gnand:
                if due(x, d1 * m) and due(y, d2 * m):
                    bad.add(st)
            for x, y, d in gs.xnand:
                if x in ats and due(y, d * m):
                    bad.add(st)
            for x, y, d in gs.rows:
                if x in ats and not due(y, d * m):
                    bad.add(st)
            # LOCK-PRUNE: for a lock-T escape whose pattern uses only
            # pos/neg/sneg conjuncts, a pattern-satisfying state at
            # k >= T*m breaks the lock on every path through it --
            # prune it (the hand-designer's "ban the hosting order"
            # move, mechanized).  Monotone: pruning strengthens
            # A-facts, which only FALSIFIES sneg conjuncts, so the
            # pattern-state set shrinks; spos-carrying locked
            # patterns are skipped (non-monotone; the tightening
            # menu is their knob).  Post-prune the lock holds
            # structurally: every pattern state sits below T*m, so
            # box-nu is true at every state from k = T*m on, and
            # every trajectory reaches such a state by time T.
            for e in gs.esc:
                if e.lock is None or e.spos:
                    continue
                if k < e.lock * m:
                    continue
                if not set(e.pos) <= ats or set(e.neg) & ats:
                    continue
                if all(not due(y, d * m) for y, d in e.sneg):
                    bad.add(st)
        if not bad:
            return live, deb
        live -= bad
        if seed not in live:
            raise Refusal('seed pruned (exact box pass)')


def _emit(gs: GSpec, m: int, live, succ, seed, tail):
    """Assemble the TModel (seed at index 0, dwell Q, stay tail)."""
    Q = Fraction(1, m)
    natoms = max(gs.atoms) + 1 if gs.atoms else 1
    order = [seed] + sorted((st for st in live
                             if st not in (seed, tail)),
                            key=lambda st: (st[0], str(st)))
    has_tail = tail in live
    if has_tail:
        order.append(tail)
    remap = {st: i for i, st in enumerate(order)}
    n = len(order)
    adj = [0] * n
    stay = 0
    dwell = []
    val = [0] * natoms
    for st in order:
        i = remap[st]
        if st == tail:
            stay |= 1 << i
            dwell.append(INF)
            continue
        dwell.append(Q)
        for t in succ[st]:
            if t in live:
                adj[i] |= 1 << remap[t]
        for a in _state_atoms(gs, st[2]):
            val[a] |= 1 << i
    assert all(adj[i] or (stay >> i & 1) for i in range(n)), \
        'dead state survived pruning'
    return TModel(tstructure(n, tuple(adj), stay, tuple(dwell)),
                  tuple(val)), n


def _seed_facts_ok(gs: GSpec, m: int, deb, seed):
    """Proposer-level seed checks (exact debuts).  pend is guaranteed
    by construction (assert); exact/avoid can die with the delayers."""
    d = deb[seed]
    for x, s in gs.pend:
        v = d.get(x)
        assert v is not None and v <= s * m, \
            f'pend {x} debut {v} > {s * m}: construction broken'
    for x in gs.exact:
        s = dict(gs.pend)[x]
        if d.get(x) is None or d[x] <= (s - 1) * m:
            return f'exact-delayer-lost({x}: debut {d.get(x)})'
    for z, h in gs.avoid:
        v = d.get(z)
        if v is not None and v <= h * m:
            return f'avoid-delayer-lost({z}: debut {v})'
    return None


def _tighten_menu(gs: GSpec, m: int):
    """Single-atom seed-deadline tightenings, escape-motivated: for
    each spos/sneg atom and each lock pos atom, the grid values below
    its seed deadline."""
    stages = dict(gs.pend)
    cands = set()
    for e in gs.esc:
        for y, d in e.spos:
            if y in stages:
                cands.add(y)
        for y, d in e.sneg:
            if y in stages:
                cands.add(y)
        if e.lock is not None:
            for z in e.pos:
                if z in stages:
                    cands.add(z)
    menu = []
    for y in sorted(cands):
        for C in range(stages[y] * m - 1, 0, -1):
            menu.append({y: C})
    return menu


def family_verdict(gs: GSpec, m: int = 4):
    """Returns (status, detail, n_states):
    status in {'MASKED-SAT', 'MASKED-SAT-variant', 'FAMILY-REFUSED',
    'ALARM'}.  (No single-firing gate: the family fires rows
    DYNAMICALLY at every instance state, so multi-firing specimens
    are in scope; unbounded growth is caught by the obligation-map
    and state-count guards and reported as a family refusal.)"""
    core = graded_core(gs)
    g_full = gspec_formula(gs)
    g_core = gspec_formula(core)

    def attempt(tighten, stats):
        states, index, succ, seed, tail = _grid_states(gs, m, tighten,
                                                       stats)
        live, deb = _exact_pass(gs, m, states, succ, seed, tail)
        bad = _seed_facts_ok(gs, m, deb, seed)
        if bad:
            raise Refusal(bad)
        tm, n = _emit(gs, m, live, succ, seed, tail)
        return tm, n

    def wingmark(stats):
        w = []
        if stats['shadows']:
            w.append(f"{stats['shadows']} forced-shadows")
        if stats['spos_shadows']:
            w.append(f"{stats['spos_shadows']} spos-shadows")
        return ('; winged: ' + ', '.join(w)) if w else ''

    detail = ''
    stats = {'shadows': 0, 'spos_shadows': 0}
    try:
        tm, n = attempt({}, stats)
    except Refusal as r:
        return ('FAMILY-REFUSED', str(r), 0)
    if tdenot(g_full, tm)[0].contains(ZERO):
        return ('MASKED-SAT', f'plain grid m={m}' + wingmark(stats), n)
    if not tdenot(g_core, tm)[0].contains(ZERO):
        return ('ALARM', 'core formula fails on an arithmetically '
                'clean grid: proposer arithmetic wrong', n)
    detail = 'core holds, escape conjuncts unmet on the plain grid'
    for tighten in _tighten_menu(gs, m):
        vstats = {'shadows': 0, 'spos_shadows': 0}
        try:
            tm, n = attempt(tighten, vstats)
        except Refusal:
            continue
        if tdenot(g_full, tm)[0].contains(ZERO):
            return ('MASKED-SAT-variant',
                    f'tightening {tighten} (grid units)'
                    + wingmark(vstats), n)
    return ('FAMILY-REFUSED', detail + '; tightening menu exhausted',
            0)


# ---------------------------------------------------------------------------
# probes and battery

def masking_signature(gs: GSpec, tm, m: int = 4):
    """Which pend atoms are masked at the seed: worst-case debut
    strictly above every gnand window the atom sits in."""
    out = {}
    for x, s in gs.pend:
        wins = [d1 for a, d1, b, d2 in gs.gnand if a == x] \
            + [d2 for a, d1, b, d2 in gs.gnand if b == x]
        if not wins:
            continue
        w = min(wins)
        out[x] = not tdenot(pfle(Fraction(w), atom(x)),
                            tm)[0].contains(ZERO)
    return out


LOCKHOLE = GSpec(
    name='lockhole (ESC-LOCK prong-a conjunct hole)',
    atoms=(0, 1), pend=((0, 3), (1, 1)), exact=(0,),
    esc=(Esc(pos=(0,), spos=((1, 1),), lock=1),))

LATEPINCH_CLEAN = GSpec(
    name='latepinch-clean (theorem control: class-UNSAT)',
    atoms=(0, 1), pend=((0, 2), (1, 2)), exact=(0,),
    gnand=((0, 2, 1, 1),))

# grand102 (sweep specimen, hardcoded from the seed-20260720 dump):
# the FORCING-WING frontier shape.  Its sneg-conjunct lock needs the
# late exact-delayer 2-instances SHADOWED (A<=2[1] true there), i.e.
# a 1-instance on EVERY continuation -- but atom 1 is non-pending, and
# every family behavior is optional (delayers always include a
# visit-free continuation), so the family cannot express "forced"
# voluntary instances and refuses.  The hand model below adds a
# CHASER: the delayer branch's late 2-service funnels into a single
# 1-serving continuation.  Wings must sometimes force, not just
# permit -- the mechanism MS's wing construction has to carry.
GRAND102 = GSpec(
    name='grand102 (sneg lock; forcing-wing witness)',
    atoms=(0, 1, 2), pend=((2, 3),), exact=(2,), avoid=((0, 2),),
    gnand=((0, 2, 1, 2), (1, 1, 2, 2)),
    esc=(Esc(pos=(2,), sneg=((1, 2),), lock=1),))


def build_grand102_hand():
    """24 states, grid 1/4.  Branch A: 2 served at t=1/4 -- the
    pattern state (its cone is 1-free, so ~A<=2[1] holds) -- then a
    1-free stay tail; box-nu from t=1/2.  Branch B: idle to t=11/4,
    2 served at t=3 (the exactness delayer), six idles, then the
    CHASER 1-instance at t=19/4 (inside [3,5], so A<=2[1] holds at
    the late 2-state -- shadowed, non-pattern; far enough out that
    A<=1[1] only becomes true after 2 is closed, keeping
    gnand(1,1,2,2) safe), then tail.  box-nu on B from t=1/4.
    Seed sees the pattern state (escape) and every trajectory has
    box-nu by 1/2 <= T=1 (lock)."""
    Q = Fraction(1, 4)
    # 0 seed; 1 A-2serve (k=1); 2 A-idle; 3 A-tail(stay);
    # 4..14 B-idles (k=1..11); 15 B-2serve (k=12, t=3);
    # 16..21 B-idles (k=13..18); 22 B-1serve (k=19, t=19/4);
    # 23 B-tail(stay).
    n = 24
    adj = [0] * n
    dwell = [Q] * n
    stay = 0
    val = [0, 0, 0]

    def edge(a, b):
        adj[a] |= 1 << b

    edge(0, 1)
    edge(1, 2)
    edge(2, 3)
    stay |= 1 << 3
    dwell[3] = INF
    edge(0, 4)
    for i in range(4, 15):
        edge(i, i + 1)
    for i in range(15, 22):
        edge(i, i + 1)
    edge(22, 23)
    stay |= 1 << 23
    dwell[23] = INF
    val[2] = (1 << 1) | (1 << 15)
    val[1] = 1 << 22
    return TModel(tstructure(n, tuple(adj), stay, tuple(dwell)),
                  tuple(val)), n


# ---------------------------------------------------------------------------
# the box-saturated-pattern certificate (class-SOUND)

def collapse_certificate(gs: GSpec):
    """ESC-LOCK-COLLAPSE (class-SOUND,
    unlike generic conjunct ESC-LOCK).  A lock-T escape whose pattern
    is a pos-singleton z plus conjuncts each BOX-FORCED at every
    z-point -- spos (y, d) forced by a row z->y within d' <= d (the
    row box makes A<=d[y] true wherever z is true), neg w forced by
    disj{z, w}, and no sneg conjunct (no box can force a negative
    A-fact) -- holds at EVERY z-point of every model: the pattern
    collapses to bare z, LOCK-TIGHTEN applies verbatim (every z-point
    strictly below T), and the three ESC-LOCK prongs refute:
      (a) z pending-exact with s_z - 1 >= T
          (sup first-z <= T <= s_z - 1 against exactness);
      (b) avoid (z, h) with h >= T (same against > h);
      (c) row x->z within d, x pending-exact with s_x - 1 >= T
          (the late x-instance forces a z-point past T).
    Returns a reason string or None.  Settles grand533 (prong a via
    row 0->1 <= 2 saturating spos (1, 2))."""
    stages = dict(gs.pend)
    for e in gs.esc:
        if e.lock is None or len(e.pos) != 1 or e.sneg:
            continue
        z, T = e.pos[0], e.lock
        if not all(any(rx == z and ry == y and rd <= d
                       for rx, ry, rd in gs.rows)
                   for y, d in e.spos):
            continue
        if not all((z, w) in gs.disj or (w, z) in gs.disj
                   for w in e.neg):
            continue
        sat = ('box-saturated: '
               + ', '.join([f'spos({y},{d}) by row' for y, d in e.spos]
                           + [f'neg({w}) by disj' for w in e.neg]))
        if z in gs.exact and stages.get(z, 0) - 1 >= T:
            return (f'ESC-LOCK-COLLAPSE(a): lock {T} on {z}, {sat}; '
                    f'sup first-{z} <= {T} <= {stages[z] - 1} against '
                    f'exactness at stage {stages[z]}')
        for zz, h in gs.avoid:
            if zz == z and h >= T:
                return (f'ESC-LOCK-COLLAPSE(b): lock {T} on {z}, '
                        f'{sat}; avoid({z},{h}) with h >= T')
        for x, y, d in gs.rows:
            if y == z and x in gs.exact and stages.get(x, 0) - 1 >= T:
                return (f'ESC-LOCK-COLLAPSE(c): lock {T} on {z}, '
                        f'{sat}; row {x}->{z} within {d} with exact '
                        f'{x} at stage {stages[x]}')
    return None


# the two frontier specimens of the development sweeps (hardcoded
# from the seed-20260720 dump, like GRAND102): the spos-non-
# monotonicity witnesses -- LOCK-PRUNE on spos patterns would be
# unsound exactly here, which is why pattern-hood at generation reads
# the CAP formula (see the winged-family notes above)
GRAND533 = GSpec(
    name='grand533 (row-saturated spos lock; COLLAPSE prong-a)',
    atoms=(0, 1), pend=((1, 3), (0, 3)), exact=(0,),
    rows=((0, 1, 2),), gnand=((0, 2, 1, 1),),
    esc=(Esc(pos=(1,), sneg=((0, 2),), lock=3),
         Esc(pos=(0,), spos=((1, 2),), lock=2)))
# (transcription audited field-by-field against the generator after
# an artifact-pair catch: the first hardcoding dropped the gnand --
# refusal debuts 7-vs-6 between the witness check and the sweep
# were the tell.  The collapse derivation never cites the gnand, so the
# UNSAT conclusion was correct for the true spec throughout.)

GRAND554 = GSpec(
    name='grand554 (two spos locks + disj on a gnand clique; '
         'double forcing wing)',
    atoms=(0, 1, 2, 3), pend=((2, 1), (1, 3)),
    disj=((0, 1), (2, 3)),
    gnand=((1, 1, 2, 1), (0, 1, 2, 1)), xnand=((2, 0, 2),),
    esc=(Esc(pos=(0,), spos=((3, 2),), lock=2),
         Esc(pos=(1,), spos=((2, 2),), lock=None)))


def check_witnesses(out) -> bool:
    """The frontier specimens grand533/grand554, the collapse
    certificate with its soundness controls, and the winged family's
    regression against the theorem-UNSAT tier (via the sweep)."""
    print('## witnesses: the frontier specimens + the collapse '
          'certificate', file=out)
    ok = True
    # grand533: the collapse certificate fires (class-sound: UNSAT)
    cert533 = collapse_certificate(GRAND533)
    fired = cert533 is not None and 'COLLAPSE(a)' in cert533
    ok &= fired
    print(f'- grand533 collapse certificate: '
          f'{cert533 if fired else "!! expected prong-(a) fire"}',
          file=out)
    status533, det533, _ = family_verdict(GRAND533)
    ok &= status533 == 'FAMILY-REFUSED'
    print(f'- grand533 winged-family verdict: {status533} ({det533}) '
          f'{"-- corroborates the theorem (a SAT here would refute COLLAPSE)" if status533 == "FAMILY-REFUSED" else "!! a family model contradicts the collapse theorem: ALARM"}',
          file=out)
    # grand554: the winged family should emit (double forcing wing)
    status554, det554, n554 = family_verdict(GRAND554)
    ok &= status554.startswith('MASKED-SAT')
    print(f'- grand554 winged-family verdict: {status554} '
          f'({det554}; n={n554}) '
          f'{"-- clocked-SAT settled by the mechanized wings" if status554.startswith("MASKED-SAT") else "!! still refused: the wing search is incomplete for this shape"}',
          file=out)
    # collapse-certificate soundness controls: must NOT fire on any
    # specimen with a CONFIRMED model (bare-pattern UNSAT roster
    # members are excluded -- collapse subsumes bare, and firing
    # there is the theorem working, not a control failure)
    buildable = {'jd-rebuilt (mechanical JD)',
                 'gnand-chain (stages 1,3: reorder, no branch)',
                 'pigeon-3-relaxed (stages 2,3,4)',
                 'xnand-sep (x@1, y@2, sep 1)',
                 'avoid-gnand (z avoid 2 pending 4, y@1, gap 1)',
                 'row-gnand (x fires y, y gnand z)',
                 'esc-free (z somewhere, no lock)',
                 'esc-lock (z somewhere, era ends by 2)',
                 'esc-window (z with AF<=1[y] at witness)',
                 'esc-window-lock (witness in y-window, era ends '
                 'by 1)'}
    controls = [LOCKHOLE, GRAND102, GRAND554, PIGEON] + \
        [gs for gs in g_roster() if gs.name in buildable]
    bad = [gs.name for gs in controls if collapse_certificate(gs)]
    ok &= not bad
    print(f'- collapse soundness controls ({len(controls)} '
          f'model-confirmed specimens): '
          f'{"no fires" if not bad else "!! FIRES on " + str(bad)}',
          file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# MS-pure-gnand decision-form instruments

def random_pg_core(rng: random.Random, i: int) -> GSpec:
    """Random pure-gnand core: pend + exact + avoid + gnand only."""
    n = rng.randint(2, 4)
    atoms = tuple(range(n))
    pend = tuple((x, rng.randint(1, 4)) for x in atoms)
    stages = dict(pend)
    exact = tuple(x for x in atoms
                  if stages[x] >= 2 and rng.random() < 0.3)
    avoid = tuple((x, rng.randint(1, stages[x] - 1)) for x in atoms
                  if stages[x] >= 2 and x not in exact
                  and rng.random() < 0.2)
    gnand = []
    for _ in range(rng.randint(0, 3)):
        x, y = rng.sample(atoms, 2)
        gnand.append((x, rng.randint(1, 3), y, rng.randint(1, 3)))
    return GSpec(name=f'pg{i}', atoms=atoms, pend=pend, exact=exact,
                 avoid=avoid, gnand=tuple(dict.fromkeys(gnand)))


def pg_effective(gs: GSpec):
    """The EFFECTIVE-STAGE FIXPOINT --
    the compound law calculus the pairwise laws generate.
    Iterate to stability:
      BAN     -- b-first banned iff eff_a <= d_a (at a b-instance
                 with a-free history, CAP forces A<=d_a[a] whenever
                 eff_a <= tau + d_a, and tau > 0): edge (a, b) in
                 prec, a strictly first on every trajectory;
      TIGHTEN -- (a, b) in prec: every FIRST a-instance has b-free
                 history, so NAND-ORDER(iii) gives first-a
                 strictly below eff_b - d_b: eff_a shrinks to it.
    eff_a is a STRICT bound once tightened below s_a (first-a <
    eff_a on every trajectory); the seed stage itself is the closed
    bound (first-a <= s_a).  Both directions of every law cited are
    proved over the full clocked class (12.2); the fixpoint is
    monotone (eff only shrinks, prec only grows) and terminates.
    Returns (eff, prec)."""
    eff = dict(gs.pend)
    prec = set()
    changed = True
    while changed:
        changed = False
        for x, d1, y, d2 in gs.gnand:
            for a, da, b, db in ((x, d1, y, d2), (y, d2, x, d1)):
                if a not in eff or b not in eff:
                    continue    # a voluntary side never forces
                if eff[a] <= da and (a, b) not in prec:
                    prec.add((a, b))
                    changed = True
                # clamp at -1: eff <= 0 is already EFF-ZERO (UNSAT),
                # and around a prec-CYCLE the raw tightening recurses
                # downward forever (found by hang: specimen pg157)
                nv = max(eff[b] - db, -1)
                if (a, b) in prec and nv < eff[a]:
                    eff[a] = nv
                    changed = True
    return eff, prec


def pg_law_infeasible(gs: GSpec):
    """Law-calculus refutation for a pure-gnand core; returns a
    derivation name or None.  Runs the effective-stage fixpoint and
    then four checks, each sound over the full clocked class:
      EFF-ZERO  -- eff_a <= 0: a service forced strictly before
                   time 0;
      GB-REFL-EFF -- a pair with both sides effective-forced
                   (eff_x <= d1 and eff_y <= d2: both A-facts true
                   at the seed, box dead);
      PREC-CYCLE -- the forced-precedence digraph has a cycle
                   (pairwise strict orders cannot all hold);
      LATE-EFF  -- exactness (avoid) on a with eff_a tightened to
                   or below its late threshold s_a - 1 (h): every
                   trajectory's first-a sits strictly below eff_a,
                   so the late fact's sup > L fails.  GB-LATE-PINCH
                   is exactly this check after ONE
                   fixpoint step -- the calculus subsumes it."""
    eff, prec = pg_effective(gs)
    for a, v in eff.items():
        if v <= 0:
            return f'EFF-ZERO({a}: effective deadline {v})'
    for x, d1, y, d2 in gs.gnand:
        if x in eff and y in eff and eff[x] <= d1 and eff[y] <= d2:
            return (f'GB-REFL-EFF{(x, d1, y, d2)}: '
                    f'eff ({eff[x]},{eff[y]})')
    # cycle in prec
    adj = {}
    for a, b in prec:
        adj.setdefault(a, []).append(b)
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {a: WHITE for a in eff}
    def dfs(a):
        color[a] = GRAY
        for b in adj.get(a, ()):
            if color.get(b) == GRAY:
                return True
            if color.get(b) == WHITE and dfs(b):
                return True
        color[a] = BLACK
        return False
    for a in list(eff):
        if color[a] == WHITE and dfs(a):
            return f'PREC-CYCLE (forced orders: {sorted(prec)})'
    stages = dict(gs.pend)
    for a in gs.exact:
        if a in eff and eff[a] <= stages[a] - 1:
            return (f'LATE-EFF(exact {a}: eff {eff[a]} <= '
                    f'{stages[a] - 1})')
    for z, h in gs.avoid:
        if z in eff and eff[z] <= h:
            return f'LATE-EFF(avoid {z}: eff {eff[z]} <= {h})'
    return None


def serial_c(gs: GSpec) -> int:
    """The plain EDF-serialization constant c = max over integer j of
    ceil(#{s_i <= j} / j) -- the least per-unit service rate any grid
    must carry from stage counts alone."""
    stages = sorted(s for _, s in gs.pend)
    if not stages:
        return 1
    c = 1
    for j in range(1, stages[-1] + 1):
        cnt = sum(1 for s in stages if s <= j)
        c = max(c, -(-cnt // j))
    return c


def serial_c_eff(gs: GSpec) -> int:
    """The window-effective serialization constant: the fixpoint
    effective stages, counted like serial_c.  Strictness is charged
    one half-step at the grid; the +1/2 lives in the m0 formula's
    factor 2."""
    eff, _ = pg_effective(gs)
    if not eff:
        return 1
    if any(v <= 0 for v in eff.values()):
        return 0                # EFF-ZERO: law-infeasible territory
    vals = sorted(eff.values())
    c = 1
    for j in range(1, vals[-1] + 1):
        cnt = sum(1 for s in vals if s <= j)
        c = max(c, -(-cnt // j))
    return c


def serial_c_branch(gs: GSpec):
    """Branch-local effective serialization (found by the
    pg62/pg84 counterexamples to m0 = 2*max(c, c_eff)): on the late
    branch of an exact/avoid atom a, every gnand partner b that
    cannot delay past a's lateness (L >= eff_b - d_b) must PRECEDE a
    there, inside the window t < eff_a - d_a (the partner's serve
    state has a reflexively-due side, so the box demands the a-side
    A-fact false while a is still pending).  The branch's stage
    multiset tightens accordingly; its serialization constant joins
    the m0 count.  Returns (max branch constant, law-gap flags) --
    a partner bound <= 0 means the late branch is arithmetically
    impossible, a LATE-BRANCH law candidate surfaced for the
    soundness/completeness ledger rather than silently clamped."""
    eff, prec = pg_effective(gs)
    stages = dict(gs.pend)
    best, flags = 1, []
    lates = [(a, stages[a] - 1) for a in gs.exact if a in stages] \
        + [(z, h) for z, h in gs.avoid if z in stages]
    for a, L in lates:
        if a not in eff:
            continue
        tight = dict(eff)
        for x, d1, y, d2 in gs.gnand:
            if x == a and y in eff:
                b, da, db = y, d1, d2
            elif y == a and x in eff:
                b, da, db = x, d2, d1
            else:
                continue
            if L < eff[b] - db:
                continue        # b can delay past a's lateness
            tight[b] = min(tight[b], eff[a] - da)
        if any(v <= 0 for v in tight.values()):
            flags.append((a, L, {k: v for k, v in tight.items()
                                 if v <= 0}))
            continue
        vals = sorted(tight.values())
        c = 1
        for j in range(1, vals[-1] + 1):
            cnt = sum(1 for s in vals if s <= j)
            c = max(c, -(-cnt // j))
        best = max(best, c)
    return best, flags


def minimal_m(gs: GSpec, mmax: int = 8):
    """Smallest grid m <= mmax with a family model (verdict starts
    with MASKED-SAT), plus the full verdict row for monotonicity
    reading.  Returns (m or None, {m: status})."""
    row = {}
    first = None
    for m in range(1, mmax + 1):
        status, _, _ = family_verdict(gs, m)
        row[m] = status
        if first is None and status.startswith('MASKED-SAT'):
            first = m
    return first, row


def cap_invariant_report(gs: GSpec, m: int):
    """The CAP-invariant probe (the MS sufficiency lemma's shadow):
    on the converged family graph, at every live non-tail state and
    every atom, the exact worst-case debut should equal the cap
    formula -- 0 when serving, O[a] - k when open, infinite when
    absent.  Returns (n_states, violations) where violations lists
    (state, atom, exact, cap) for every divergence."""
    states, index, succ, seed, tail = _grid_states(gs, m, {})
    live, deb = _exact_pass(gs, m, states, succ, seed, tail)
    bad = []
    n = 0
    for st in live:
        if st == tail:
            continue
        n += 1
        k, Of, s = st
        O = dict(Of)
        ats = _state_atoms(gs, st[2])
        for a in gs.atoms:
            exact = deb[st].get(a)
            if a in ats:
                cap = 0
            elif a in O:
                cap = O[a] - k
            else:
                cap = None
            if exact != cap:
                bad.append((st, a, exact, cap))
    return n, bad


M2REFUTE = GSpec(
    name='m2-refute (three stage-1 pends: law-feasible, m=2 dead)',
    atoms=(0, 1, 2), pend=((0, 1), (1, 1), (2, 1)))


def check_ms(out, rounds: int = 200, seed: int = 20260720) -> bool:
    """The MS-pure-gnand instrument battery."""
    print('## ms: pure-gnand decision-form instruments',
          file=out)
    ok = True
    # 1. the m = 2 conjecture, refuted by serialization
    assert pg_law_infeasible(M2REFUTE) is None and screen(M2REFUTE) \
        is None
    _, row = minimal_m(M2REFUTE, 4)
    good = (not row[2].startswith('MASKED-SAT')) \
        and row[3].startswith('MASKED-SAT')
    ok &= good
    print(f'- m2-refute: verdicts by grid {row} '
          f'{"-- law-feasible core REFUSED at m=2, SAT at m=3: the m=2 conjecture is refuted by serialization (c=3)" if good else "!! expected refusal at 2, SAT at 3"}',
          file=out)
    # 2. the pure-gnand sweep: decision-form + minimal-m vs the
    #    serialization constants + monotonicity-in-m
    rng = random.Random(seed)
    n_sat = n_law = n_open = n_alarm = n_screened = 0
    m_gaps = []
    mono_breaks = []
    over_c = []
    for i in range(rounds):
        gs = random_pg_core(rng, i)
        if screen(gs):
            n_screened += 1
            law = pg_law_infeasible(gs)
            continue
        law = pg_law_infeasible(gs)
        mm, row = minimal_m(gs, 8)
        sat = mm is not None
        # monotonicity: once SAT, SAT at every finer grid probed
        if sat:
            after = [row[m] for m in range(mm, 9)]
            if not all(s.startswith('MASKED-SAT') for s in after):
                mono_breaks.append((i, row))
        if sat and law:
            n_alarm += 1
            print(f'- pg{i}: !! ALARM family-SAT (m={mm}) with law '
                  f'refutation {law} -- one of them is wrong',
                  file=out)
        elif sat:
            n_sat += 1
            c, ce = serial_c(gs), serial_c_eff(gs)
            cb, cbflags = serial_c_branch(gs)
            if cbflags:
                print(f'- pg{i}: LATE-BRANCH flag on a family-SAT '
                      f'core ({cbflags}) -- the branch-tightening '
                      f'arithmetic is UNSOUND as a refutation: '
                      f'law-gap ledger cargo', file=out)
            m0 = len(gs.pend) + 1       # the repaired conjecture
            m_gaps.append((i, mm, c, ce, cb))
            if mm > m0:
                over_c.append((i, mm, len(gs.pend), c, ce, cb))
        elif law:
            n_law += 1
        else:
            n_open += 1
            print(f'- pg{i}: OPEN -- family-refused through m=8, no '
                  f'law refutation (law gap or deep grid): '
                  f'pend={gs.pend} exact={gs.exact} '
                  f'avoid={gs.avoid} gnand={gs.gnand}', file=out)
    ok &= n_alarm == 0
    print(f'- sweep ({rounds} cores, seed {seed}): {n_screened} '
          f'screened, {n_sat} family-SAT, {n_law} law-UNSAT, '
          f'{n_open} open, {n_alarm} alarms', file=out)
    if mono_breaks:
        print(f'- !! m-monotonicity breaks: {mono_breaks[:5]}',
              file=out)
        ok = False
    else:
        print(f'- m-monotonicity: SAT persists at every finer grid '
              f'probed (all SAT specimens, m..8)', file=out)
    mstats = {}
    for i, mm, c, ce, cb in m_gaps:
        key = (mm, max(c, ce, cb))
        mstats[key] = mstats.get(key, 0) + 1
    print(f'- minimal-m vs serialization constant (m_min, '
          f'max(c, c_eff, c_branch)) -> count: '
          f'{dict(sorted(mstats.items()))}', file=out)
    if over_c:
        print(f'- specimens with m_min > n_pending + 1 (the m0 '
              f'conjecture\'s counterexamples): {over_c}', file=out)
    else:
        print(f'- m0 = n_pending + 1 covered every family-SAT '
              f'specimen (the repaired grid conjecture: every '
              f'integer window is >= 1 and holds n slots strictly '
              f'inside at m = n + 1; the per-atom constants c/c_eff/'
              f'c_branch above are descriptive cargo -- pg62/pg84 '
              f'showed per-atom counting cannot close the bound: '
              f'first-of-PAIR windows are pair-level demands)',
              file=out)
    # 3. the CAP-invariant probe on family-SAT cores
    rng2 = random.Random(seed + 1)
    probed = viol = 0
    viol_rows = []
    for i in range(60):
        gs = random_pg_core(rng2, 1000 + i)
        if screen(gs) or pg_law_infeasible(gs):
            continue
        mm, _ = minimal_m(gs, 6)
        if mm is None:
            continue
        probed += 1
        n, bad = cap_invariant_report(gs, mm)
        if bad:
            viol += 1
            viol_rows.append((1000 + i, mm, len(bad), bad[:2]))
    print(f'- CAP-invariant probe: {probed} family-SAT cores at '
          f'minimal m; {viol} with exact-vs-cap divergence'
          + (f' -- specimens {viol_rows[:4]}' if viol_rows
         else ' (exact debut == cap formula at every live state)'),
          file=out)
    # divergence is CARGO, not failure: it marks where the
    # sufficiency write-through must weaken the invariant
    print(file=out)
    return ok


def check_family(out) -> bool:
    print('## family: the masked-family builder (the hand-built '
          'witness generalized to a mechanical tier)', file=out)
    ok = True

    def probe(gs, expect, note=''):
        nonlocal ok
        status, detail, n = family_verdict(gs)
        good = status.startswith(expect)
        ok &= good
        mark = '' if good else f' !! expected {expect}'
        print(f'- {gs.name}: {status} ({detail}; n={n}){mark}'
              + (f' -- {note}' if note else ''), file=out)
        return status, detail

    # 1. the pigeon witness, mechanically rediscovered
    status, _ = probe(PIGEON, 'MASKED-SAT',
                      'the hand-built witness, now emitted by '
                      'the general family')
    if status == 'MASKED-SAT':
        states, index, succ, seed, tail = _grid_states(PIGEON, 4, {})
        live, deb = _exact_pass(PIGEON, 4, states, succ, seed, tail)
        tm, n = _emit(PIGEON, 4, live, succ, seed, tail)
        sig = masking_signature(PIGEON, tm)
        allm = all(sig.values()) and len(sig) == 3
        ok &= allm
        print(f'  masking signature at seed (debut > window, all '
              f'three atoms): '
              f'{"confirmed" if allm else "!! ABSENT " + str(sig)}',
              file=out)
    # 2. the pigeon singleton-burst cells (masking-SAT as
    #    conjectured; GB-PIGEON fires on each, so each is also a
    #    fresh class-unsoundness witness for that schema)
    for x in (0, 1, 2):
        S = frozenset((x,))
        bs = burst_spec(PIGEON, ('spine', None), S)
        cert = semantic_certificate(bs)
        status, _ = probe(bs, 'MASKED-SAT',
                          f'singleton burst {sorted(S)}; '
                          f'branch-at-seed cert: '
                          f'{cert.split(":")[0] if cert else "none"}')
    # 3. negative control: |S|=2 bursts carry propositional
    #    refutations (a gnand pair at A<=1) -- the family MUST refuse
    for S in (frozenset((0, 1)), frozenset((1, 2))):
        bs = burst_spec(PIGEON, ('spine', None), S)
        probe(bs, 'FAMILY-REFUSED',
              f'burst {sorted(S)} is propositionally refuted; a SAT '
              f'here would break soundness')
    # 4. theorem controls
    probe(LATEPINCH_CLEAN, 'FAMILY-REFUSED',
          'GB-LATE-PINCH premises hold; the class-soundness theorem '
          'says clocked-UNSAT -- family refusal corroborates')
    cert = semantic_certificate(LOCKHOLE)
    fired = cert is not None and cert.startswith('ESC-LOCK')
    ok &= fired
    print(f'- lockhole: branch-at-seed certificate '
          f'{"fires (" + cert.split(":")[0] + ")" if fired else "!! silent"}',
          file=out)
    probe(LOCKHOLE, 'MASKED-SAT',
          'conjunct-pattern lock + exactness: the prong-(a) '
          'class-unsoundness witness -- late z-instances fail the '
          'spos conjunct, so the lock survives the late branch')
    # the forcing-wing pair: the
    # UNWINGED family refused grand102 -- every family behavior was
    # optional, so the shadow A<=2[1] could not be forced at the late
    # 2-instances -- and the hand-built chaser settled it clocked-SAT
    # (the matched pair that NAMED forcing wings).  The wing
    # mechanization (forced-shadow obligations) closes the gap: the
    # family now emits the chaser shape itself.  The hand model stays
    # in-battery as the independent witness.
    tm102, n102 = build_grand102_hand()
    holds102 = tdenot(gspec_formula(GRAND102), tm102)[0].contains(ZERO)
    ok &= holds102
    print(f'- grand102-hand (chaser model, n={n102}): full formula '
          f'{"HOLDS at seed -- the independent forcing-wing witness" if holds102 else "!! FAILS"}',
          file=out)
    status102, det102, n102f = family_verdict(GRAND102)
    ok &= status102.startswith('MASKED-SAT')
    print(f'- grand102 winged-family verdict: {status102} '
          f'({det102}; n={n102f}) '
          f'{"-- the forcing wing, mechanized (the unwinged refusal closed)" if status102.startswith("MASKED-SAT") else "!! expected MASKED-SAT from the winged family"}',
          file=out)
    # 5. buildable-specimen coverage controls (family should agree
    #    SAT with the branch-at-seed builder on these)
    roster = {gs.name: gs for gs in g_roster()}
    for name in ('jd-rebuilt (mechanical JD)',
                 'gnand-chain (stages 1,3: reorder, no branch)',
                 'pigeon-3-relaxed (stages 2,3,4)',
                 'xnand-sep (x@1, y@2, sep 1)',
                 'avoid-gnand (z avoid 2 pending 4, y@1, gap 1)',
                 'row-gnand (x fires y, y gnand z)',
                 'esc-free (z somewhere, no lock)',
                 'esc-lock (z somewhere, era ends by 2)',
                 'esc-window (z with AF<=1[y] at witness)',
                 'esc-window-lock (witness in y-window, era ends '
                 'by 1)'):
        probe(roster[name], 'MASKED-SAT', 'buildable branch-at-seed; '
              'family coverage control')
    # 6. the roster's certificate-refused specimens
    probe(roster['esc-lock-pinch (z exact@3, lock@1)'],
          'FAMILY-REFUSED',
          'bare-pattern lock pinch: class-sound (ESC-LOCK '
          'bare case) -- refusal corroborates')
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# the sweep: the constructive tier's random population, refused
# specimens probed

def sweep(out, rounds: int, seed: int) -> bool:
    print(f'## sweep: {rounds} randoms (seed {seed}) re-classified; '
          f'every certificate-refused specimen probed by the masked '
          f'family', file=out)
    rng = random.Random(seed)
    ok = True
    counts = {'built': 0, 'screened': 0}
    refused = []
    for i in range(rounds):
        gs = random_gspec(rng, i)
        if screen(gs):
            counts['screened'] += 1
            continue
        cert = semantic_certificate(gs)
        try:
            build_core_model(gs)
            built = True
        except Refusal:
            built = False
            if cert is None:
                cert = semantic_certificate(gs, deep=True)
        if built:
            counts['built'] += 1
            continue
        if cert is None:
            print(f'- grand{i}: !! ALARM refused with no certificate '
                  f'(the constructive tier should have caught it)',
                  file=out)
            ok = False
            continue
        refused.append((i, gs, cert))
    print(f'- classification: {counts["built"]} built, '
          f'{counts["screened"]} screened, {len(refused)} '
          f'certificate-refused (banked receipts: 398/181/21)',
          file=out)
    verdicts = {}
    by_kind = {}
    for i, gs, cert in refused:
        kind = cert.split(':')[0]
        status, detail, n = family_verdict(gs)
        verdicts[i] = status
        by_kind.setdefault(kind, []).append((i, status))
        flags = []
        if gs.esc:
            flags.append(f'{len(gs.esc)} esc'
                         + (' lock' if any(e.lock is not None
                                           for e in gs.esc) else '')
                         + (' spos' if any(e.spos for e in gs.esc)
                            else '')
                         + (' sneg' if any(e.sneg for e in gs.esc)
                            else ''))
        if gs.rows:
            flags.append('rows')
        print(f'- grand{i} [{kind}'
              + (f'; {" ".join(flags)}' if flags else '')
              + f']: {status}'
              + (f' ({detail})' if status != 'MASKED-SAT'
                 else f' ({detail}; n={n})'), file=out)
    print(f'- verdict x certificate-kind table:', file=out)
    for kind in sorted(by_kind):
        row = by_kind[kind]
        sat = sum(1 for _, s in row if s.startswith('MASKED-SAT'))
        ref = sum(1 for _, s in row if s == 'FAMILY-REFUSED')
        alarm = sum(1 for _, s in row if s == 'ALARM')
        ok &= alarm == 0
        print(f'  {kind}: {len(row)} specimens -> {sat} masked-SAT '
              f'(reclassified), {ref} family-refused'
              + (f', !! {alarm} ALARM' if alarm else ''), file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------

def run_battery(out, rounds: int, seed: int) -> bool:
    print('# family: the masked-family tier',
          file=out)
    print(file=out)
    ok = check_family(out)
    ok &= check_witnesses(out)
    ok &= check_ms(out, seed=seed)
    ok &= sweep(out, rounds, seed)
    print(f'family overall: {"PASS" if ok else "FAIL"}',
          file=out)
    return ok


def main():
    ap = argparse.ArgumentParser(
        description='family: the masked-family builder')
    ap.add_argument('cmd', nargs='?', default='battery',
                    choices=['battery', 'family', 'witnesses', 'ms',
                             'sweep'])
    ap.add_argument('--rounds', type=int, default=600)
    ap.add_argument('--seed', type=int, default=20260720)
    args = ap.parse_args()
    out = sys.stdout
    if args.cmd == 'battery':
        ok = run_battery(out, args.rounds, args.seed)
    elif args.cmd == 'family':
        ok = check_family(out)
    elif args.cmd == 'witnesses':
        ok = check_witnesses(out)
    elif args.cmd == 'ms':
        ok = check_ms(out, seed=args.seed)
    else:
        ok = sweep(out, args.rounds, args.seed)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
