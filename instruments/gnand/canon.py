#!/usr/bin/env python3
r"""canon -- the elimination-prototype instrument.

Prototypes the canonical construction's
type elimination AS AN INSTRUMENT before the E1 induction is written:
for concrete specimens, build the finite schedulable-type space, run
the demand elimination, emit the surviving model as a TModel at the
uniform grid, and cross-check with the evaluator (ground truth) that
the emitted model actually satisfies the seed formula -- positives,
negatives, avoid-facts, and the E2 blockers -- at the fresh seed type.

Scope discipline: this is a PROFILE-level prototype, not a general
Sigma+-type engine. A specimen is given as a Spec (unit-normalized
integer deadlines): pending atom-bases with stages, box rows
x -> AF<=d[y], pairwise-disjointness constraints, avoid horizons
~AF<=h[z]. Types are (valuation, residual-vector) profiles; the box
content is global (every specimen here has a single global box). The
evaluator cross-check is what keeps the prototype honest: the emitted
TModel is evaluated with tdenot, so any architecture error surfaces
as a failed check, not a wrong claim.

What the prototype adjudicates:
  1. E1 architecture: elimination + EDF residual bookkeeping produce
     a model whose seed satisfies the specimen (incl. negatives --
     the avoiding-chain types must survive elimination).
  2. E2 semantics: the FRESH profile (all residuals maximal) survives
     and satisfies the blockers ~AF<=(s - 1/N)[psi] -- the
     constructive loose-seed witness at the canonical grid.
  3. The schedulability fork (a stress finding): the SCHED group
     invariant assumes pairwise-disjoint worst case; profiles that
     violate the strict invariant can still be BATCH-feasible when
     bases overlap. canon builds the demand relation with batching
     allowed wherever disjointness permits, and reports how many
     surviving types are strict-invariant violators -- data for E1's
     definitional choice of "schedulable".

Python as orchestration/check-scale code (oracle.py module
docstring).
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations, product

from oracle import atom, f_not, f_and, pg, impl, DEAD
from timed import (INF, TModel, tstructure, tdenot, pfle, tshow,
                        _witness_point)

ONE = Fraction(1)


# ---------------------------------------------------------------------------
# specimen specs (unit-normalized: all deadlines positive integers)

@dataclass(frozen=True)
class Spec:
    name: str
    atoms: tuple            # atom indices in play
    pend: tuple             # ((atom, stage), ...) -- positive obligations
    rows: tuple = ()        # ((x, y, d), ...): box row  x -> AF<=d[y]
    disj: tuple = ()        # ((x, y), ...): box  ~(x & y)
    avoid: tuple = ()       # ((z, h), ...): seed fact  ~AF<=h[z]
    N: int = 0              # grid steps per unit (0 => len(pend))

    def grid(self) -> int:
        return self.N if self.N else max(1, len(self.pend))


def spec_formula(sp: Spec, loose: bool):
    """The specimen's seed formula (optionally blocker-strengthened),
    in the unit-normalized language the emitted model speaks."""
    N = sp.grid()
    g = None

    def add(c):
        nonlocal g
        g = c if g is None else f_and(g, c)

    for x, s in sp.pend:
        add(f_and(f_not(atom(x)), pfle(Fraction(s), atom(x))))
        if loose:
            add(f_not(pfle(Fraction(s * N - 1, N), atom(x))))
    for z, h in sp.avoid:
        add(f_not(pfle(Fraction(h), atom(z))))
    box = None

    def badd(c):
        nonlocal box
        box = c if box is None else f_and(box, c)

    for x, y, d in sp.rows:
        badd(impl(atom(x), pfle(Fraction(d), atom(y))))
    for x, y in sp.disj:
        badd(f_not(f_and(atom(x), atom(y))))
    if box is not None:
        add(pg(box))
    return g


# ---------------------------------------------------------------------------
# profile types
#
# A type is (val, res): val = frozenset of true atoms; res = tuple of
# per-job residuals in GRID STEPS (1..stage*N) or DONE. Jobs: one per
# pending base (index into sp.pend) -- a base whose atom is true is
# serviced (DONE). Row-armed obligations are tracked as extra jobs
# keyed by row index, armed whenever the row's antecedent is true at
# the PREVIOUS type and discharged/re-armed per successor.

DONE = 0  # residual sentinel: no live obligation


@dataclass(frozen=True)
class PType:
    val: frozenset          # true atoms
    res: tuple              # per-pend-job residual (grid steps; 0 = done)
    rowres: tuple           # per-row residual for armed row obligations

    def key(self):
        return (self.val, self.res, self.rowres)


def _coherent(sp: Spec, t: PType) -> bool:
    """Local coherence: disjointness respected; serviced bases DONE;
    live obligations have positive residual within their stage cap;
    row obligations: consequent true => DONE."""
    for x, y in sp.disj:
        if x in t.val and y in t.val:
            return False
    N = sp.grid()
    for i, (x, s) in enumerate(sp.pend):
        r = t.res[i]
        if x in t.val:
            if r != DONE:
                return False
        else:
            if r == DONE:
                continue  # serviced in the past, target since left
            if not (1 <= r <= s * N):
                return False
    for j, (x, y, d) in enumerate(sp.rows):
        rr = t.rowres[j]
        if y in t.val:
            if rr != DONE:
                return False
        elif rr != DONE and not (1 <= rr <= d * N):
            return False
        if x in t.val and y not in t.val and rr == DONE:
            return False  # row fired at this state: obligation must be live
    return True


def build_types(sp: Spec):
    """All coherent profiles. Small by construction for the specimens."""
    N = sp.grid()
    atom_sets = []
    for bits in range(1 << len(sp.atoms)):
        v = frozenset(sp.atoms[i] for i in range(len(sp.atoms))
                      if (bits >> i) & 1)
        atom_sets.append(v)
    out = []
    res_ranges = [range(0, s * N + 1) for _, s in sp.pend]
    row_ranges = [range(0, d * N + 1) for _, _, d in sp.rows]
    for v in atom_sets:
        for res in product(*res_ranges) if res_ranges else ((),):
            for rr in product(*row_ranges) if row_ranges else ((),):
                t = PType(v, tuple(res), tuple(rr))
                if _coherent(sp, t):
                    out.append(t)
    return out


def _jobs(sp: Spec, t: PType):
    """Live (kind, idx, residual) obligations at t."""
    out = []
    for i, _ in enumerate(sp.pend):
        if t.res[i] != DONE:
            out.append(('pend', i, t.res[i]))
    for j, _ in enumerate(sp.rows):
        if t.rowres[j] != DONE:
            out.append(('row', j, t.rowres[j]))
    return out


def strict_invariant(sp: Spec, t: PType) -> bool:
    """SCHED's group invariant: #{jobs with residual <= j} <= j for
    all j (the pairwise-disjoint worst case)."""
    rs = sorted(r for _, _, r in _jobs(sp, t))
    return all(r >= i + 1 for i, r in enumerate(rs))


def _job_target(sp: Spec, kind, idx):
    return sp.pend[idx][0] if kind == 'pend' else sp.rows[idx][1]


def clique_invariant(sp: Spec, t: PType) -> bool:
    """SCHED-C: the group invariant per pairwise-UNBATCHABLE
    clique -- jobs whose targets are pairwise box-disjoint can never
    share a service step (a successor valuation satisfies at most one
    of them), so SCHED's count argument binds within every such
    clique; jobs with batchable targets are exempt from each other's
    counts. Discovered by the strict-universe rand5 failure: the
    loose witness needs two overlapping bases serviced in one step,
    which the strict invariant wrongly excludes."""
    jobs = _jobs(sp, t)
    disj = set(sp.disj) | {(y, x) for x, y in sp.disj}

    def unbatch(i, j):
        a = _job_target(sp, jobs[i][0], jobs[i][1])
        b = _job_target(sp, jobs[j][0], jobs[j][1])
        return a != b and (a, b) in disj

    m = len(jobs)
    # every pairwise-unbatchable subset must satisfy the count law;
    # subsets are tiny at prototype scale -- enumerate directly.
    for bits in range(1, 1 << m):
        mem = [i for i in range(m) if (bits >> i) & 1]
        if len(mem) < 2:
            continue
        if all(unbatch(i, j) for i in mem for j in mem if i < j):
            rs = sorted(jobs[i][2] for i in mem)
            if any(r < i + 1 for i, r in enumerate(rs)):
                return False
    return True


def successors(sp: Spec, t: PType, types_by_key):
    """Demand-satisfying successors: every live job decrements or its
    target atom is true at the successor (service-at-entry); jobs at
    residual 1 MUST be serviced. Batching is whatever the successor
    valuation admits (disjointness constrains it there). Row
    obligations re-arm at full residual whenever the row's antecedent
    is true at the successor and the consequent is not."""
    N = sp.grid()
    out = []
    for t2 in types_by_key.values():
        ok = True
        for i, (x, s) in enumerate(sp.pend):
            r = t.res[i]
            if r == DONE:
                if t2.res[i] != DONE:
                    ok = False
                    break
                continue
            if x in t2.val:
                if t2.res[i] != DONE:
                    ok = False
                    break
            else:
                if r == 1 or t2.res[i] != r - 1:
                    ok = False
                    break
        if not ok:
            continue
        for j, (x, y, d) in enumerate(sp.rows):
            rr = t.rowres[j]
            if y in t2.val:
                want = DONE
            elif rr == 1:
                ok = False  # prior arming expires unserviced -- even a
                break       # fresh re-fire cannot relax it (min law)
            elif x in t2.val:
                # fired at t2: fresh full residual, but a live prior
                # arming keeps its (decremented) tighter deadline --
                # taking the max instead was an early re-arm bug: a
                # persistent-antecedent chain would postpone service
                # forever and violate the row at every chain state.
                want = d * N if rr == DONE else min(rr - 1, d * N)
            elif rr == DONE:
                want = DONE
            else:
                want = rr - 1
            if t2.rowres[j] != want:
                ok = False
                break
        if ok:
            out.append(t2)
    return out


def can_stay(sp: Spec, t: PType) -> bool:
    """Stay flag: no live obligations, and dwelling forever violates
    no row (antecedents true here have consequents true here --
    already enforced by coherence via rowres arming)."""
    return not _jobs(sp, t)


def eliminate(sp: Spec, types):
    """Fixpoint elimination: a type survives iff it can stay or has a
    surviving demand-satisfying successor. Returns (survivors, log)."""
    alive = {t.key(): t for t in types}
    rounds = 0
    while True:
        rounds += 1
        dead = []
        for k, t in alive.items():
            if can_stay(sp, t):
                continue
            if not successors(sp, t, alive):
                dead.append(k)
        if not dead:
            break
        for k in dead:
            del alive[k]
    return alive, rounds


def emit_tmodel(sp: Spec, alive) -> tuple:
    """Surviving types -> TModel at uniform dwell 1/N; stay flags on
    obligation-free types. Returns (tm, index_of[key])."""
    N = sp.grid()
    keys = sorted(alive.keys(), key=repr)
    idx = {k: i for i, k in enumerate(keys)}
    n = len(keys)
    adj = [0] * n
    stay = 0
    u = [None] * n
    for k, i in idx.items():
        t = alive[k]
        if can_stay(sp, t):
            stay |= 1 << i
            u[i] = INF
            # stays may also move: successors keep the graph rich for
            # avoidance runs; a stay location's u must be INF, edges
            # allowed
        else:
            u[i] = Fraction(1, N)
        for t2 in successors(sp, t, alive):
            adj[i] |= 1 << idx[t2.key()]
    natoms = max(sp.atoms) + 1 if sp.atoms else 1
    val = [0] * natoms
    for k, i in idx.items():
        for a in alive[k].val:
            val[a] |= 1 << i
    tm = TModel(tstructure(n, tuple(adj), stay, tuple(u)), tuple(val))
    return tm, idx


def fresh_seed(sp: Spec):
    """The fresh profile: seed valuation empty (all pending atoms
    false -- specimens declare them pending), all residuals maximal,
    rows unarmed (no antecedent true at the seed)."""
    N = sp.grid()
    return PType(frozenset(),
                 tuple(s * N for _, s in sp.pend),
                 tuple(DONE for _ in sp.rows))


UNIVERSES = {'batched': None, 'strict': strict_invariant,
             'clique': clique_invariant}


def run_spec(sp: Spec, out, check_loose=True, universe='batched') -> dict:
    """universe selects the type-space filter applied BEFORE
    elimination: 'batched' = coherence only (elimination-survival is
    the schedulability notion); 'strict' = SCHED's group invariant
    (the pairwise-disjoint worst case -- KNOWN to lose loose
    witnesses on overlapping bases: the rand5 finding); 'clique' =
    SCHED-C, the invariant per pairwise-unbatchable clique (the E1
    recommendation)."""
    N = sp.grid()
    types = build_types(sp)
    filt = UNIVERSES[universe]
    if filt is not None:
        types = [t for t in types if filt(sp, t)]
    alive, rounds = eliminate(sp, types)
    seed = fresh_seed(sp)
    seed_alive = seed.key() in alive
    strict_viol = [t for t in alive.values()
                   if not strict_invariant(sp, t)]
    tag = f' [{universe.upper()} universe]' if universe != 'batched' \
        else ''
    res = {'name': sp.name, 'types': len(types), 'alive': len(alive),
           'rounds': rounds, 'seed_alive': seed_alive,
           'strict_violators': len(strict_viol), 'sat': None,
           'loose_sat': None, 'n': None}
    print(f'## {sp.name}{tag} (N = {N}, |types| = {len(types)}, '
          f'survivors = {len(alive)}, elimination rounds = {rounds})',
          file=out)
    if not seed_alive:
        print('- !! fresh seed ELIMINATED -- architecture failure '
              '(or the specimen is genuinely unsatisfiable at this '
              'grid); investigate by hand', file=out)
        return res
    tm, idx = emit_tmodel(sp, alive)
    res['n'] = tm.s.n
    si = idx[seed.key()]
    checks = [('seed formula', spec_formula(sp, loose=False), 'sat')]
    if check_loose and sp.pend:
        checks.append(('blocker-loose strengthening',
                       spec_formula(sp, loose=True), 'loose_sat'))
    for label, f, kk in checks:
        d, dd = tdenot(f, tm), tdenot(DEAD, tm)
        diff = d[si].minus(dd[si], tm.s.u[si])
        got = not diff.is_empty()
        res[kk] = got
        wp = _witness_point(diff) if got else None
        print(f'- {label}: '
              + (f'SATISFIED at seed location {si} (clock {wp}) '
                 '-- evaluator cross-check PASS'
                 if got else '!! NOT satisfied at the seed location '
                 '-- evaluator cross-check FAIL, architecture bug '
                 'or genuine E2 obstruction'), file=out)
    if universe != 'batched':
        return res
    print(f'- emitted model: n = {tm.s.n} locations at uniform dwell '
          f'1/{N}; strict-SCHED-invariant violators among survivors: '
          f'{len(strict_viol)}'
          + (' (batch-feasible profiles the strict filter would '
             'exclude -- the E1 definitional fork is live on this '
             'specimen)' if strict_viol else
             ' (strict filter and batched feasibility agree here)'),
          file=out)
    return res


# ---------------------------------------------------------------------------
# the specimen roster

def roster():
    specs = []
    # S_2, S_3: pending atoms at stage 1, pairwise disjoint.
    for k in (2, 3):
        specs.append(Spec(
            name=f'S_{k}', atoms=tuple(range(k)),
            pend=tuple((i, 1) for i in range(k)),
            disj=tuple((i, j) for i in range(k) for j in range(i + 1, k))))
    # curfew Phi, unit-normalized at lambda = G = 4: deadlines
    # {1, 1/2, 5/4} -> {4, 2, 5}; atoms b1 = 0, b2 = 1, c = 2;
    # N = N_chi = 3.
    specs.append(Spec(
        name='curfew Phi (normalized x4)', atoms=(0, 1, 2),
        pend=((0, 4), (1, 4)),
        rows=((0, 2, 2), (1, 2, 2)),
        disj=((0, 1), (0, 2), (1, 2)),
        avoid=((2, 5),),
        N=3))
    # the four random-tier tight-candidates from the looseseed probe
    # : hand analysis found loose witnesses for each; canon
    # must reproduce them constructively.
    specs.append(Spec(
        name='rand3 (row a->c, stages 1/2/2)', atoms=(0, 1, 2),
        pend=((2, 1), (0, 2), (1, 2)), rows=((0, 2, 1),)))
    specs.append(Spec(
        name='rand5 (row b->c, stages 2/1/1)', atoms=(0, 1, 2),
        pend=((2, 2), (1, 1), (0, 1)), rows=((1, 2, 1),)))
    specs.append(Spec(
        name='rand10 (row a->c, stages 2/1/1)', atoms=(0, 1, 2),
        pend=((1, 2), (0, 1), (2, 1)), rows=((0, 2, 1),)))
    specs.append(Spec(
        name='rand11 (row c->b, disj, stages 1/1)', atoms=(0, 1, 2),
        pend=((1, 1), (2, 1)), rows=((2, 1, 1),),
        disj=((0, 1), (0, 2), (1, 2))))
    return specs


def overload_controls(out) -> bool:
    """The poison boundary, machine-checked at its sharpest:
    two bases both pending at residual 1 grid step. Disjoint: the
    profile must be ELIMINATED (no successor can service both -- the
    scaled-S_2 poison case, consistent at finer grids, unrealizable
    at grid N). Overlapping (disjointness dropped): the same residual
    profile is batch-serviceable and must SURVIVE. The pair is the
    schedulability fork at its boundary."""
    ok = True
    print('## overload controls (the elimination-contract stress '
          'test, per the standing check discipline)', file=out)
    for disj, expect_dead, label in (
            (((0, 1),), True, 'disjoint overload (poison case)'),
            ((), False, 'overlapping overload (batchable)')):
        sp = Spec(name='ctrl', atoms=(0, 1),
                  pend=((0, 1), (1, 1)), disj=disj, N=2)
        types = build_types(sp)
        alive, _ = eliminate(sp, types)
        over = PType(frozenset(), (1, 1), ())
        assert _coherent(sp, over), 'control profile must be coherent'
        dead = over.key() not in alive
        good = dead == expect_dead
        ok &= good
        print(f'- {label}: residual profile (1, 1) '
              + ('ELIMINATED' if dead else 'SURVIVES')
              + (' as the architecture requires'
                 if good else ' -- !! CONTRARY TO EXPECTATION, '
                 'investigate'), file=out)
    print(file=out)
    return ok


def main():
    ap = argparse.ArgumentParser(
        description='canon: elimination-prototype instrument')
    ap.add_argument('--out', default='-')
    args = ap.parse_args()
    out = sys.stdout if args.out == '-' else open(args.out, 'w')
    try:
        print('# canon: the type-elimination prototype '
              '(architecture machine-check)', file=out)
        print(file=out)
        print('Ground truth is the evaluator: every emitted model is '
              'cross-checked with tdenot at the fresh seed type. '
              '"seed formula SATISFIED" corroborates the E1 '
              'architecture (elimination + EDF bookkeeping + stays '
              'build a genuine countermodel); "blocker-loose '
              'SATISFIED" is the constructive loose-seed witness '
              '(E2\'s semantic shadow) at the canonical grid.',
              file=out)
        print(file=out)
        ok = True
        strict_losses = 0
        for sp in roster():
            r = run_spec(sp, out)
            good = r['seed_alive'] and r['sat'] and \
                (r['loose_sat'] is not False)
            ok &= good
            if r['strict_violators']:
                # the fork, adjudicated on both branches. strict is
                # INFORMATIONAL: a strict loss is the finding that
                # the strict invariant is the wrong universe (first
                # specimen: rand5), not an instrument failure.
                r2 = run_spec(sp, out, universe='strict')
                if not (r2['seed_alive'] and r2['sat']
                        and r2['loose_sat'] is not False):
                    strict_losses += 1
                    print('  (STRICT loses a witness here -- the '
                          'fork adjudicated against the bare strict '
                          'invariant)', file=out)
                # clique (SCHED-C) is the recommended universe: GATES.
                r3 = run_spec(sp, out, universe='clique')
                good3 = r3['seed_alive'] and r3['sat'] and \
                    (r3['loose_sat'] is not False)
                ok &= good3
            print(file=out)
        ok &= overload_controls(out)
        print(f'- fork tally: strict-universe witness losses: '
              f'{strict_losses} (>= 1 expected: the rand5 finding); '
              'SCHED-C (clique) universe: gating, all specimens '
              'above', file=out)
        print(file=out)
        print(f'canon overall: {"PASS" if ok else "FAIL"}', file=out)
        sys.exit(0 if ok else 1)
    finally:
        if out is not sys.stdout:
            out.close()


if __name__ == '__main__':
    main()
