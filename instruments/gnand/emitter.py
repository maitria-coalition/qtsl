#!/usr/bin/env python3
r"""emitter -- the model emitter (schedule trees, machine-verified
per core).

Turns the wing-closure construction of the completeness proof into a
machine-verified build per core.  For an EXTENDED-law-feasible
pure-gnand core (13.3's four checks + LATE-BRANCH-PINCH all silent),
BUILD the witness subgraph the prose describes -- the prec-topological
spine plus eff-slot delayer wings -- as explicit family states
(k, O, s) at grid m = n + 1, and hand it to the family's own exact
pass (`family._exact_pass`, unmodified).  Verdicts per core:

  EMIT-VERIFIED   -- the pass prunes NOTHING, the seed late-facts
                     hold, and tdenot confirms the full formula on the
                     emitted TModel: 14.5's (a)-(d) machine-checked on
                     this core.
  EMIT-PRUNED     -- the pass pruned some states but the seed
                     survived and tdenot confirms: the construction
                     over-emitted (prose gap, mild) yet the witness
                     stands.
  CONSTRUCTION-GAP -- the emitter could not close (slot collision it
                     could not serialize, demand with no delayable
                     side, wing slot in the past, or the exact pass
                     killed the seed): the wing arithmetic has a hole
                     at this core.  Every specimen is first-order
                     cargo.

The construction, faithful to the prose (choices where the prose
underdetermines are flagged in comments and adjudicated by the pass):

  spine  -- serve all n pending atoms in a prec-topological order at
            grid steps 1..n (entry times Q..nQ, all inside unit 0
            since m = n + 1); O carries seed deadlines s_x * m.
  wings  -- attached on demand, to closure: wherever the current
            subgraph's own worst-case debuts violate a gnand box
            (both sides due), the open non-reflexive side q gets a
            delayer wing: X = prec-descendant closure of q; slot
            times sigma_x = (s_q + lp(q -> x)) * m - shift_x with lp
            the longest path in the tighten digraph restricted to X
            (edge weight = the partner-side window, max over the
            pair's gnands -- the fixpoint's tighten window) and
            shift_x = #(prec-descendants of x inside X) (root gets
            |X| - 1, strictly decreasing along chains);
            non-X open atoms are served promptly at the first free
            steps (prec-topological order).  Slot collisions
            serialize downward one grid step at a time (the prose is
            silent on unrelated-sibling ties; the pass adjudicates).
  late   -- every exact/avoid atom gets its wing at the SEED
            unconditionally: the delayer branch that holds the
            seed's late fact.

The demand loop iterates (attach wing -> recompute debuts) to a
fixpoint; adding delayer branches only raises worst-case debuts,
which only helps box negatives and never breaks a deadline (every
wing serves every open atom by its seed deadline), so the loop is
monotone in the demand set and terminates on the finite state space.

The extended-completeness hunt rides the same sweep: the standing
instrument question -- does extended-feasible AND family-refused
occur? -- is answered per random core with `pg_law_infeasible_ext`
as the judge and the winged family probed at m = n + 1 (and finer,
on a refusal).  Any such specimen is a T3+ alarm; absence at scale
is the empirical face of the feasibility theorem.

Python as orchestration-class code per the standing warrant (tiny
exact spaces, integer arithmetic; the emitted graphs are tens of
states).
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction

from timed import tdenot
from cores import GSpec, gspec_formula, screen, Refusal
from family import (_exact_pass, _emit, _seed_facts_ok, _state_atoms,
                         pg_effective, pg_law_infeasible, family_verdict,
                         random_pg_core, minimal_m, M2REFUTE)
from derivation import late_branch_pinch, pg_law_infeasible_ext

ZERO = Fraction(0)
IDLE = '.'


class Gap(Exception):
    """A construction gap: 14.5's arithmetic has a hole here."""


# ---------------------------------------------------------------------------
# arithmetic helpers

def _pair_windows(gs: GSpec):
    """w[(a, b)] = the clearance a's service demands of b, in stage
    units: max over gnands on {a, b} of the b-side window (at a's
    service point a is reflexively due, so EVERY gnand on the pair
    demands its b-side negative there).  This is the tighten window
    the fixpoint uses (pg_effective applies every pair-gnand once the
    prec edge exists)."""
    w = {}
    for x, d1, y, d2 in gs.gnand:
        w[(x, y)] = max(w.get((x, y), 0), d2)
        w[(y, x)] = max(w.get((y, x), 0), d1)
    return w


def _topo(atoms, prec):
    """Prec-topological order (a before b for (a, b) in prec),
    deterministic; raises Gap on a cycle (extended-feasible cores
    have none -- PREC-CYCLE was checked)."""
    atoms = sorted(atoms)
    out_edges = {a: set() for a in atoms}
    indeg = {a: 0 for a in atoms}
    for a, b in prec:
        if a in indeg and b in indeg and b not in out_edges[a]:
            out_edges[a].add(b)
            indeg[b] += 1
    order, ready = [], sorted(a for a in atoms if indeg[a] == 0)
    while ready:
        a = ready.pop(0)
        order.append(a)
        for b in sorted(out_edges[a]):
            indeg[b] -= 1
            if indeg[b] == 0:
                ready.append(b)
        ready.sort()
    if len(order) != len(atoms):
        raise Gap('prec cycle inside emitter (should be unreachable '
                  'on extended-feasible cores)')
    return order


def _desc_closure(prec, root):
    """Prec-descendant closure of root (root included)."""
    out, todo = {root}, [root]
    while todo:
        u = todo.pop()
        for p, q in prec:
            if p == u and q not in out:
                out.add(q)
                todo.append(q)
    return out


def _wing_slots(gs: GSpec, m: int, prec, q, eff):
    """The eff-slot schedule for q's wing (14.5(b), REPAIRED): X =
    descendant closure of q; sigma_x = (eff_q + lp(q -> x)) * m -
    shift_x, lp the longest path in the tighten digraph over X,
    shift_x the count of x's strict prec-descendants inside X.

    EFF-ANCHOR CORRECTION (found by this instrument's first
    122-core run): the wing prose as first WRITTEN anchors the slots
    at the root's SEED
    stage s_rho, and its claim (i) -- s_rho + lp(rho -> x) <= eff_x
    -- is REFUTED on 5/122 family-SAT cores (specimens
    pg68/90/107/182/185) whenever the wing root is TIGHTENED
    (eff_rho < s_rho):
    the fixpoint inequality eff_x >= eff_rho + lp(rho -> x) only
    supports the EFF anchor, which is also what the prose's own name
    ('delays q to its EFF-SLOT') says.  With sigma anchored at
    eff_rho, (i) is the fixpoint inequality verbatim.  (c) survives:
    EXACT roots are never tightened (LATE-EFF feasibility forces
    eff_a = s_a), and AVOID roots keep their late fact because
    feasibility gives eff_rho > h while shift < m <= (eff_rho - h)m.
    Returns {x: slot} in grid units (absolute, from the seed)."""
    stages = dict(gs.pend)
    X = _desc_closure(prec, q)
    w = _pair_windows(gs)
    edges = {(a, b): w.get((a, b), 0) for a, b in prec
             if a in X and b in X}
    order = _topo(X, {(a, b) for a, b in edges})
    lp = {x: (0 if x == q else None) for x in X}
    for a in order:
        if lp[a] is None:
            continue                    # not reachable from q: below
        for b in X:
            if (a, b) in edges:
                cand = lp[a] + edges[(a, b)]
                if lp[b] is None or cand > lp[b]:
                    lp[b] = cand
    # members of X not lp-reachable from q (joined via another chain):
    # anchor them at their own stage (the prose anchors on the root;
    # descendants only via prec-paths from q are lp-anchored -- an
    # unreachable member would mean prec edges into X from elsewhere,
    # excluded by construction of X as the FORWARD closure)
    for x in X:
        if lp[x] is None:
            raise Gap(f'wing member {x} not lp-reachable from root '
                      f'{q} (unexpected: X is the forward closure)')
    shift = {x: len(_desc_closure(prec, x) & X) - 1 for x in X}
    slots = {}
    for x in X:
        s = (eff[q] + lp[x]) * m - shift[x]
        if s > stages[x] * m:
            # repaired (i): converged TIGHTEN gives eff_q + lp <=
            # eff_x <= s_x, so this cannot fire; if it does, the
            # repair itself has a hole -- flag loudly
            raise Gap(f'wing slot for {x} past its deadline: '
                      f'sigma={s} > {stages[x] * m} (repaired (i) '
                      f'fails)')
        slots[x] = s
    return slots


# ---------------------------------------------------------------------------
# the emitter

class Emitter:
    def __init__(self, gs: GSpec, m: int = None):
        assert not (gs.rows or gs.esc or gs.xnand or gs.disj), \
            'emitter scope is pure-gnand cores'
        self.gs = gs
        self.n = len(gs.pend)
        self.m = m if m is not None else self.n + 1
        self.stages = dict(gs.pend)
        self.eff, self.prec = pg_effective(gs)
        self.index = {}
        self.states = []
        self.succ = {}
        self.tail = ('tail', frozenset(), IDLE)
        self.wings = set()          # (attach_state, q) keys
        self.notes = []
        seed_O = {x: s * self.m for x, s in gs.pend}
        self.seed = (0, frozenset(seed_O.items()), IDLE)
        self._add(self.seed)

    def _add(self, st):
        if st not in self.index:
            self.index[st] = len(self.states)
            self.states.append(st)
            self.succ[st] = set()
        return st

    def _edge(self, a, b):
        self._add(a)
        self._add(b)
        self.succ[a].add(b)

    def _schedule_branch(self, st, sched):
        """Materialize a deterministic branch from state st serving
        atoms per sched = {atom: absolute grid step}; idle between
        services; tail on exhaustion.  States dedupe globally."""
        k, Of, _ = st
        O = dict(Of)
        by_time = sorted((t, x) for x, t in sched.items())
        for t, x in by_time:
            if t <= k:
                raise Gap(f'slot {t} for atom {x} not in the future '
                          f'of attach step {k}')
            if x not in O:
                raise Gap(f'scheduled atom {x} not open at attach')
        cur = st
        for t, x in by_time:
            k_cur = cur[0]
            while k_cur + 1 < t:            # idle up to the slot
                nxt = (k_cur + 1, cur[1], IDLE)
                self._edge(cur, nxt)
                cur, k_cur = nxt, k_cur + 1
            O = dict(cur[1])
            del O[x]
            nxt = (t, frozenset(O.items()), x)
            self._edge(cur, nxt)
            cur = nxt
        if dict(cur[1]):
            raise Gap(f'branch left obligations open: {dict(cur[1])}')
        self._edge(cur, self.tail)

    def _spine(self):
        order = _topo([x for x, _ in self.gs.pend], self.prec)
        sched = {x: i + 1 for i, x in enumerate(order)}
        self._schedule_branch(self.seed, sched)

    def _attach_wing(self, st, q):
        """The q-delayer wing at st (14.5(b)): X to eff-slots, other
        open atoms promptly."""
        key = (st, q)
        if key in self.wings:
            return False
        self.wings.add(key)
        k, Of, _ = st
        O = dict(Of)
        X = _desc_closure(self.prec, q) & set(O)
        slots = {x: t for x, t in
                 _wing_slots(self.gs, self.m, self.prec, q,
                             self.eff).items()
                 if x in O}
        # serialize collisions downward (prose silent on unrelated
        # ties; the exact pass adjudicates the result)
        used = set()
        for x in sorted(slots, key=lambda x: (slots[x], x)):
            t = slots[x]
            while t in used:
                t -= 1
                self.notes.append(f'slot bump {x} at wing({st},{q})')
            if t <= k:
                raise Gap(f'wing({q}) slot for {x} fell to {t} <= '
                          f'attach step {k}')
            used.add(t)
            slots[x] = t
        rest = [x for x in _topo(sorted(O), self.prec) if x not in X]
        t = k
        for x in rest:
            t += 1
            while t in used:
                t += 1
            if t > self.stages[x] * self.m:
                raise Gap(f'prompt slot {t} for non-wing atom {x} '
                          f'past its deadline at wing({st},{q})')
            used.add(t)
            slots[x] = t
        self._schedule_branch(st, slots)
        return True

    # -- worst-case debuts on the current subgraph (the exact-pass
    #    recursion, no pruning: the demand detector)
    def _debuts(self):
        deb = {self.tail: {a: None for a in self.gs.atoms}}
        for st in sorted((s for s in self.states if s != self.tail),
                         key=lambda s: -s[0]):
            ats = _state_atoms(self.gs, st[2])
            row = {}
            for a in self.gs.atoms:
                if a in ats:
                    row[a] = 0
                    continue
                worst = -1
                for t in self.succ[st]:
                    d = deb[t].get(a)
                    if d is None:
                        worst = None
                        break
                    worst = max(worst, d)
                row[a] = None if worst is None else worst + 1
            deb[st] = row
        return deb

    def _demands(self, deb):
        """Box violations under the subgraph's own debuts; for each,
        the delayable side (open, non-reflexive)."""
        out = []
        for st in self.states:
            if st == self.tail:
                continue
            ats = _state_atoms(self.gs, st[2])
            O = dict(st[1])
            row = deb[st]

            def due(a, w):
                v = 0 if a in ats else row.get(a)
                return v is not None and v <= w
            for x, d1, y, d2 in self.gs.gnand:
                if due(x, d1 * self.m) and due(y, d2 * self.m):
                    cands = [q for q in (x, y)
                             if q not in ats and q in O]
                    if not cands:
                        raise Gap(f'undelayable box violation at '
                                  f'{st}: gnand{(x, d1, y, d2)}')
                    # prefer the side with more slack (s - d), the
                    # doc's un-banned side; ties break low
                    q = max(cands, key=lambda a: (
                        self.stages[a]
                        - (d2 if a == y else d1), -a))
                    out.append((st, (x, d1, y, d2), q))
        return out

    def build(self, max_wings=200, max_states=60000):
        self._spine()
        for a in self.gs.exact:
            self._attach_wing(self.seed, a)
        for z, _ in self.gs.avoid:
            self._attach_wing(self.seed, z)
        while True:
            if len(self.states) > max_states:
                raise Gap('state explosion in emitter')
            deb = self._debuts()
            new = False
            for st, clause, q in self._demands(deb):
                if self._attach_wing(st, q):
                    new = True
            if not new:
                remaining = self._demands(self._debuts())
                if remaining:
                    st, clause, q = remaining[0]
                    raise Gap(f'demand fixpoint stuck: {clause} at '
                              f'{st} (wing({q}) already attached)')
                return
            if len(self.wings) > max_wings:
                raise Gap('wing explosion in emitter')

    def verify(self):
        """Hand the subgraph to the family's exact pass + tdenot."""
        gs, m = self.gs, self.m
        try:
            live, deb = _exact_pass(gs, m, self.states, self.succ,
                                    self.seed, self.tail)
        except Refusal as r:
            raise Gap(f'exact pass killed the seed: {r}')
        pruned = len(self.states) - len(live)
        bad = _seed_facts_ok(gs, m, deb, self.seed)
        if bad:
            raise Gap(f'seed late-facts lost after pass: {bad}')
        tm, nst = _emit(gs, m, live, self.succ, self.seed, self.tail)
        if not tdenot(gspec_formula(gs), tm)[0].contains(ZERO):
            raise Gap('tdenot refutes the emitted model (ALARM '
                      'class: construction arithmetic wrong)')
        return pruned, nst


def emit_verify(gs: GSpec, m: int = None):
    """Returns (verdict, detail, n_states):
    verdict in {'EMIT-VERIFIED', 'EMIT-PRUNED', 'CONSTRUCTION-GAP'}."""
    try:
        em = Emitter(gs, m)
        em.build()
        pruned, nst = em.verify()
    except Gap as g:
        return 'CONSTRUCTION-GAP', str(g), 0
    detail = (f'{len(em.wings)} wings, {nst} states'
              + (f', {len(em.notes)} slot bumps' if em.notes else ''))
    if pruned:
        return 'EMIT-PRUNED', f'{detail}; {pruned} states pruned', nst
    return 'EMIT-VERIFIED', detail, nst


# ---------------------------------------------------------------------------
# the battery

def _the_122(out):
    """Replicate the check_ms population exactly (seed 20260720,
    200 draws): the family-SAT cores the sweep counted -- the named
    reproduction target."""
    rng = random.Random(20260720)
    cores = []
    for i in range(200):
        gs = random_pg_core(rng, i)
        if screen(gs):
            continue
        mm, _ = minimal_m(gs, 8)
        if mm is not None:
            cores.append((i, gs, mm))
    print(f'- population replay: {len(cores)} family-SAT cores '
          f'(banked receipts: 122)', file=out)
    return cores


def battery(out) -> bool:
    ok = True
    print('## hand controls', file=out)
    # out-of-scope guards: the two lawgap witnesses are correctly
    # rejected by the emitter's precondition (extended-infeasible)
    wall = GSpec(name='wall-hand', atoms=(0, 1),
                 pend=((0, 2), (1, 3)), exact=(0,),
                 gnand=((0, 2, 1, 2),))
    gap = GSpec(name='lawgap-hand', atoms=(0, 1, 2),
                pend=((0, 2), (1, 4), (2, 4)), exact=(0,),
                gnand=((0, 2, 1, 1), (0, 2, 2, 1), (1, 3, 2, 3)))
    w_ext = pg_law_infeasible_ext(wall)
    g_ext = pg_law_infeasible_ext(gap)
    ok &= w_ext is not None and g_ext is not None
    print(f'- wall-hand extended-check: {w_ext} (must fire)', file=out)
    print(f'- lawgap-hand extended-check: {g_ext} (must fire -- the '
          f'T3-as-stated refuter, caught by the branch check)',
          file=out)
    # in-scope hand cores
    for gs, note in (
            (M2REFUTE, 'three stage-1 pends; m0 = 4 = n + 1'),
            (GSpec(name='chain3', atoms=(0, 1, 2),
                   pend=((0, 1), (1, 2), (2, 3)),
                   gnand=((0, 1, 1, 1), (1, 1, 2, 1))),
             'a tighten chain; prec spine order load-bearing'),
            (GSpec(name='exact-pair', atoms=(0, 1),
                   pend=((0, 2), (1, 2)), exact=(0,),
                   gnand=((0, 1, 1, 1),)),
             'exact root with a gnand partner: seed wing + demand '
             'wings'),
            (GSpec(name='avoid-pair', atoms=(0, 1),
                   pend=((0, 3), (1, 2)), avoid=((0, 1),),
                   gnand=((0, 1, 1, 1),)),
             'avoid root: the (c) case')):
        ext = pg_law_infeasible_ext(gs)
        if ext is not None:
            ok = False
            print(f'- {gs.name}: !! extended-check fired ({ext}) on '
                  f'an intended-feasible control', file=out)
            continue
        v, d, nst = emit_verify(gs)
        good = v == 'EMIT-VERIFIED'
        ok &= good
        fam, fdet, fn = family_verdict(gs, len(gs.pend) + 1)
        agree = fam.startswith('MASKED-SAT')
        ok &= agree
        print(f'- {gs.name}: {v} ({d}) | family at n+1: {fam}'
              + ('' if good and agree else ' !! ')
              + f' -- {note}', file=out)
    print(file=out)
    print('## the family-SAT population (seed replay)',
          file=out)
    cores = _the_122(out)
    counts = {}
    gaps = []
    for i, gs, mm in cores:
        ext = pg_law_infeasible_ext(gs)
        if ext is not None:
            ok = False
            print(f'- pg{i}: !! ALARM extended-check fired on a '
                  f'family-SAT core: {ext} (class-soundness breach)',
                  file=out)
            continue
        v, d, nst = emit_verify(gs)
        counts[v] = counts.get(v, 0) + 1
        if v == 'CONSTRUCTION-GAP':
            gaps.append((i, gs, d))
    print(f'- emitter verdicts at m = n + 1: {counts}', file=out)
    for i, gs, d in gaps[:12]:
        print(f'  gap pg{i}: pend={gs.pend} exact={gs.exact} '
              f'avoid={gs.avoid} gnand={gs.gnand}: {d}', file=out)
    ok &= counts.get('CONSTRUCTION-GAP', 0) == 0
    print(file=out)
    return ok


def hunt(out, rounds=800, seed=485018) -> bool:
    """Primary (b): fresh random tier; extended-check as the judge;
    every extended-feasible core emitter-verified AND family-probed
    at m = n + 1.  extended-feasible AND family-refused (at n + 1 and
    finer) = the T3+ alarm, SIXTH-check material."""
    print(f'## the extended-completeness hunt ({rounds} fresh '
          f'randoms, seed {seed})', file=out)
    rng = random.Random(seed)
    ok = True
    tot = {'screened': 0, 'law-refuted': 0, 'branch-refuted': 0,
           'feasible': 0}
    emv = {}
    alarms = []
    branch_specimens = []
    for i in range(rounds):
        gs = random_pg_core(rng, i)
        if screen(gs):
            tot['screened'] += 1
            continue
        law = pg_law_infeasible(gs)
        if law is not None:
            tot['law-refuted'] += 1
            continue
        br = late_branch_pinch(gs)
        if br is not None:
            tot['branch-refuted'] += 1
            if len(branch_specimens) < 40:
                branch_specimens.append((i, gs, br))
            continue
        tot['feasible'] += 1
        n = len(gs.pend)
        v, d, nst = emit_verify(gs)
        emv[v] = emv.get(v, 0) + 1
        fam, fdet, fn = family_verdict(gs, n + 1)
        if not fam.startswith('MASKED-SAT'):
            # probe finer before alarming (the family is
            # refusal-sound only)
            finer = [family_verdict(gs, mm)[0]
                     for mm in (n + 2, n + 3)]
            alarms.append((i, gs, v, fam, finer))
        if v == 'CONSTRUCTION-GAP' and fam.startswith('MASKED-SAT'):
            print(f'- gap pg{i} (family-SAT at n+1): pend={gs.pend} '
                  f'exact={gs.exact} avoid={gs.avoid} '
                  f'gnand={gs.gnand}: {d}', file=out)
    print(f'- classification: {tot}', file=out)
    print(f'- emitter verdicts on the feasible tier: {emv}', file=out)
    print(f'- T3+ alarms (extended-feasible, family-refused at '
          f'n+1): {len(alarms)}'
          + (' (NONE: the empirical face of 14.6 at this scale)'
             if not alarms else ''), file=out)
    for i, gs, v, fam, finer in alarms:
        print(f'  !! pg{i}: emitter={v}, family n+1={fam}, finer='
              f'{finer}: pend={gs.pend} exact={gs.exact} '
              f'avoid={gs.avoid} gnand={gs.gnand}', file=out)
    ok &= not alarms
    ok &= emv.get('CONSTRUCTION-GAP', 0) == 0
    # hand the branch-refuted tier to the nested-derivation sweep
    # (derivation.py's nested command consumes the same seed)
    print(f'- branch-refuted specimens banked for the derivation '
          f'sweep: {len(branch_specimens)} of '
          f'{tot["branch-refuted"]}', file=out)
    print(file=out)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', nargs='?', default='battery',
                    choices=['battery', 'hunt', 'all'])
    ap.add_argument('--rounds', type=int, default=800)
    ap.add_argument('--seed', type=int, default=485018)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    out = open(args.out, 'w') if args.out else sys.stdout
    print('# emitter -- the model emitter (schedule trees)', file=out)
    print(file=out)
    ok = True
    if args.cmd in ('battery', 'all'):
        ok &= battery(out)
    if args.cmd in ('hunt', 'all'):
        ok &= hunt(out, args.rounds, args.seed)
    print(f't3_emitter {args.cmd}: {"OK" if ok else "PROBLEMS"}',
          file=out)
    if args.out:
        out.close()
        print(f'wrote {args.out}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
