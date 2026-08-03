#!/usr/bin/env python3
r"""derivation -- the derivation-sweep instrument (the deductive
bridge).

Every profile the effective-stage fixpoint calculus refutes
semantically must be DERIVABLY inconsistent (cell |- D), else a
consistent-but-law-infeasible cell strands the completeness proof's
graded-positive clause.  This instrument enumerates small pure-gnand
profiles the calculus refutes, attempts a mechanized derivation of D
for each, and files survivors as basis-correction candidates.

THE DERIVATION SEARCHER mirrors the calculus move-for-move; every
move is a proved lemma of the banked basis (or of the FS-R-corrected
basis, below), so a DERIVED verdict carries a sound certificate:

  bounds    E_a -- "u |- A_{E_a} a", initialized at seed stages (the
            pend facts), only ever lowered by derivations.
  disjunct death (pointwise refutation in Box(u)-context): a
            first-service cell C or residual cell R dies iff some
            gnand G-clause has both A-conjuncts forced at the point:
            a TRUE atom forces its A-fact by U4 (reflexivity, any
            deadline); a budget fact A_T x forces A_d x by D1 iff
            T <= d.  The reached point carries every G by U10F
            (box relativization), so death = Box(u) |- ~C.
  FS-TIGHTEN (current basis): pair {a,b}; FS_2 gives
            u |- A_{s*}(C_a v C_b), s* = min(E_a, E_b); if C_b dies,
            R6 + D4 force the a-first disjunct: u |- A_{s*} C_a,
            MONO projects u |- A_{s*} a: E_a <- min(E_a, E_b).
            Both die => R6 + D3 land D (SC-B's avoidance-free chain).
  FSR-TIGHTEN (corrected basis): the residual-split axiom

      FS-R (residual split):   /\_i A_{T_i} alpha_i  <=
        A_c ( \/_i (alpha_i /\ /\_{i'=/=i} A_{T_i'} alpha_i')
              \/  /\_i A_{T_i - c} alpha_i )        (0 < c < min T_i)

            -- within c, either the subset's first service has
            happened (original co-budgets, as in FS) or no service
            yet and every obligation holds at its true residual.
            Validity over the clocked class is by the FS fusion
            argument plus the no-service branch at the time-c point
            (proof in the development record).  Pair instance at {a,b},
            cutoff c: if C_b dies (originals) and R(c) = A_{E_a-c}a
            /\ A_{E_b-c}b dies (residuals), R6 + D4 force the
            a-first disjunct at deadline c: E_a <- min(E_a, c).
            All three die => D3 lands D.
  global checks at the current bounds, after every round:
    GB-REFL   -- some gnand with E_x <= d1, E_y <= d2: D1 weakens
                 both bounds into the windows, G4 + liveness put G
                 at the live seed, PC lands bottom;
    LATE/AV   -- exact a with E_a <= s_a - 1 (avoid (z,h) with
                 E_z <= h): D1 weakens the bound onto the seed's
                 own negative fact; PC lands bottom.

The searcher runs each move set to fixpoint; DERIVED verdicts carry
the certificate trace.  A cell no move set derives is a SURVIVOR:
calculus-refuted (hence UNSAT -- T2 is proved sound) but not
derivably inconsistent by these mirrors -- basis-gap material.

CLASSIFICATION per refuted cell:
  DERIVED-BASE  -- current basis suffices (FS + screens tier);
  DERIVED-FSR   -- needs FS-R: a fourth-basis-correction WITNESS
                   (the current basis's transport delivers original
                   stages only -- FS's own statement flags the
                   weakening -- and these cells need true residuals);
  SURVIVOR      -- neither mirror derives; dissected against the
                   doc-vs-code tightening divergence (13.3 states
                   TIGHTEN pair-locally; pg_effective tightens
                   cross-pair, sound via reflexivity at the first-a
                   point, which the R-disjunct mirror cannot use).

SOUNDNESS CONTROLS: (i) derive() must stay silent on every
family-SAT core (a model witnesses consistency); the sweep replays
the family battery specimens and a random family-SAT tier.  (ii)
survivors and a DERIVED-FSR sample are re-judged semantically (the
winged family at fine grids): every one must be FAMILY-REFUSED --
a masked-SAT law-infeasible core would falsify the PROVED T2 and is
a loud instrument alarm, per the lane's fourth-correction protocol.

Python as orchestration-class code (tiny exact spaces; integer
arithmetic throughout).
"""

from __future__ import annotations

import argparse
import itertools
import random
import sys

from cores import GSpec, screen
from family import pg_effective, pg_law_infeasible, family_verdict


def family_probe(gs: GSpec, m: int) -> str:
    """'SAT' iff the winged family emits a tdenot-confirmed model at
    grid m; 'REFUSED' otherwise (family-sound only)."""
    status, _, _ = family_verdict(gs, m)
    return 'SAT' if status.startswith('MASKED-SAT') else 'REFUSED'


# ---------------------------------------------------------------------------
# the doc-calculus variant (pair-local TIGHTEN), for the divergence class

def pg_effective_doc(gs: GSpec):
    """The calculus as DOCUMENTED: TIGHTEN only 'from that pair' -- the
    prec edge and the tightening window must come from the same
    gnand.  pg_effective (the code) tightens cross-pair: any prec
    edge (a,b) lets any gnand on (a,b) tighten, sound via U4
    reflexivity at the first-a point.  The delta between the two is
    the divergence class the searcher measures."""
    eff = dict(gs.pend)
    prec = set()          # (a, b, da, db): edge with its OWN pair data
    changed = True
    while changed:
        changed = False
        for x, d1, y, d2 in gs.gnand:
            for a, da, b, db in ((x, d1, y, d2), (y, d2, x, d1)):
                if a not in eff or b not in eff:
                    continue
                if eff[a] <= da and (a, b, da, db) not in prec:
                    prec.add((a, b, da, db))
                    changed = True
                if (a, b, da, db) in prec:
                    nv = max(eff[b] - db, -1)
                    if nv < eff[a]:
                        eff[a] = nv
                        changed = True
    return eff, {(a, b) for a, b, _, _ in prec}


def pg_law_infeasible_doc(gs: GSpec):
    """The four checks over the doc-calculus fixpoint."""
    eff, prec = pg_effective_doc(gs)
    for a, v in eff.items():
        if v <= 0:
            return f'EFF-ZERO({a})'
    for x, d1, y, d2 in gs.gnand:
        if x in eff and y in eff and eff[x] <= d1 and eff[y] <= d2:
            return f'GB-REFL-EFF{(x, d1, y, d2)}'
    adj = {}
    for a, b in prec:
        adj.setdefault(a, []).append(b)
    color = {a: 0 for a in eff}

    def dfs(a):
        color[a] = 1
        for b in adj.get(a, ()):
            if color.get(b) == 1 or (color.get(b) == 0 and dfs(b)):
                return True
        color[a] = 2
        return False

    for a in list(eff):
        if color[a] == 0 and dfs(a):
            return 'PREC-CYCLE'
    stages = dict(gs.pend)
    for a in gs.exact:
        if a in eff and eff[a] <= stages[a] - 1:
            return f'LATE-EFF(exact {a})'
    for z, h in gs.avoid:
        if z in eff and eff[z] <= h:
            return f'LATE-EFF(avoid {z})'
    return None


# ---------------------------------------------------------------------------
# the LATE-BRANCH-PINCH check (the calculus extension the lawgap
# witness forces)

def _prec_desc(prec, a):
    """Downward closure of a under the forced-precedence relation."""
    out, todo = {a}, [a]
    while todo:
        u = todo.pop()
        for p, q in prec:
            if p == u and q not in out:
                out.add(q)
                todo.append(q)
    return out


def late_branch_pinch(gs: GSpec):
    """The branch-conditional refuter the global fixpoint cannot
    see (witness: lawgap-hand; serial_c_branch flagged the
    family).  For a late fact on atom a (exact: L = s_a - 1; avoid:
    L = h), the late branch serves a at t_a > L and every
    prec-descendant after it.  At any late service p@t_p with
    partner q unserved, the box needs ~A_{d_q}q there, while q's
    residual latest is eff_q - t_p: the clearance is IMPOSSIBLE
    whenever eff_q - d_q <= L (t_p > L >= eff_q - d_q forces the
    A-fact; sound by the 13.3 eff invariant + fusion).  So each
    in-branch gnand pair imposes: a doubly-pinched pair refutes
    outright; a singly-pinched pair forces the pinched side EARLIER;
    with the prec edges these order demands form a digraph, and a
    CYCLE refutes (no service order exists); a deadline s_x <= L in
    the branch set refutes trivially.  Returns a reason or None."""
    eff, prec = pg_effective(gs)
    stages = dict(gs.pend)
    lates = [(a, stages[a] - 1, 'exact') for a in gs.exact
             if a in stages] + \
            [(z, h, 'avoid') for z, h in gs.avoid if z in stages]
    for a, L, kind in lates:
        X = _prec_desc(prec, a)
        for x in X:
            if x != a and stages.get(x, 10**9) <= L:
                return (f'LATE-BRANCH({kind} {a}): descendant {x} '
                        f'deadline {stages[x]} <= L {L}')
        edges = {(u, v) for u, v in prec if u in X and v in X}
        for x, d1, y, d2 in gs.gnand:
            if x not in X or y not in X or x not in eff or \
                    y not in eff:
                continue
            px = eff[x] - d1 <= L      # x pinched: x must be earlier
            py = eff[y] - d2 <= L
            if px and py:
                return (f'LATE-BRANCH({kind} {a}): pair '
                        f'{(x, d1, y, d2)} doubly pinched '
                        f'(eff {eff[x]},{eff[y]}, L {L})')
            if px:
                edges.add((x, y))
            if py:
                edges.add((y, x))
        adj = {}
        for u, v in edges:
            adj.setdefault(u, []).append(v)
        color = {u: 0 for u in X}

        def dfs(u):
            color[u] = 1
            for w in adj.get(u, ()):
                if color.get(w) == 1 or (color.get(w) == 0
                                         and dfs(w)):
                    return True
            color[u] = 2
            return False

        for u in sorted(X):
            if color[u] == 0 and dfs(u):
                return (f'LATE-BRANCH({kind} {a}): pinch/prec order '
                        f'cycle in branch set {sorted(X)}')
    return None


def pg_law_infeasible_ext(gs: GSpec):
    """The extended calculus: the four 13.3 checks, then
    LATE-BRANCH-PINCH."""
    return pg_law_infeasible(gs) or late_branch_pinch(gs)


# ---------------------------------------------------------------------------
# the derivation searcher

def _dead(true_atoms, budgets, gnand):
    """Pointwise disjunct death: some gnand clause has both
    A-conjuncts forced at a point satisfying exactly these facts.
    U4 forces the A-fact of a TRUE atom at any deadline; D1 forces
    A_d x from a budget A_T x iff T <= d.  Returns a witness or
    None."""
    for x, d1, y, d2 in gnand:
        okx = x in true_atoms or (x in budgets and budgets[x] <= d1)
        oky = y in true_atoms or (y in budgets and budgets[y] <= d2)
        if okx and oky:
            jx = 'U4' if x in true_atoms else f'D1({budgets[x]}<={d1})'
            jy = 'U4' if y in true_atoms else f'D1({budgets[y]}<={d2})'
            return f'gnand{(x, d1, y, d2)}[{jx},{jy}]'
    return None


def derive(gs: GSpec, use_fsr: bool, state_out: dict = None):
    """Mechanized derivation search for D from the pure-gnand cell.
    Returns a certificate list (DERIVED) or None (survivor for this
    move set).  Every step cites its lemma chain.  state_out, if
    given, receives the final tightened bounds E (for the nested
    engine to consume)."""
    E = dict(gs.pend)
    stages = dict(gs.pend)
    if state_out is not None:
        state_out.clear()
        E = state_out
        E.update(gs.pend)
    cert = []

    def globals_check():
        for x, d1, y, d2 in gs.gnand:
            if x in E and y in E and E[x] <= d1 and E[y] <= d2:
                cert.append(
                    f'GB-REFL at bounds: A_{E[x]}[{x}]-D1->A_{d1}, '
                    f'A_{E[y]}[{y}]-D1->A_{d2}, G4+live+PC: D')
                return True
        for a in gs.exact:
            if a in E and E[a] <= stages[a] - 1:
                cert.append(
                    f'LATE: A_{E[a]}[{a}]-D1->A_{stages[a]-1} vs '
                    f'exactness ~A_{stages[a]-1}[{a}]: D')
                return True
        for z, h in gs.avoid:
            if z in E and E[z] <= h:
                cert.append(
                    f'AV: A_{E[z]}[{z}]-D1->A_{h} vs avoid '
                    f'~A_{h}[{z}]: D')
                return True
        return False

    if globals_check():
        return cert
    changed = True
    while changed:
        changed = False
        atoms = sorted(E)
        for a, b in itertools.permutations(atoms, 2):
            # first-service cells of the pair sub-profile {a, b}
            ca = _dead({a}, {b: E[b]}, gs.gnand)   # a-first cell
            cb = _dead({b}, {a: E[a]}, gs.gnand)   # b-first cell
            if ca and cb:
                cert.append(
                    f'FS_2{{{a},{b}}}: both cells die ({ca}; {cb}); '
                    f'R6+D3: D')
                return cert
            if cb and not ca:
                s_star = min(E[a], E[b])
                if s_star < E[a]:
                    cert.append(
                        f'FS-TIGHTEN({a}|{b}): C_{b} dies ({cb}); '
                        f'R6+D4+MONO: A_{s_star}[{a}]')
                    E[a] = s_star
                    changed = True
                if use_fsr:
                    # minimal cutoff c with the residual cell dead
                    for c in range(1, min(E[a], E[b])):
                        r = _dead(set(),
                                  {a: E[a] - c, b: E[b] - c},
                                  gs.gnand)
                        if not r:
                            continue
                        ca_c = _dead({a}, {b: E[b]}, gs.gnand)
                        if ca_c:
                            cert.append(
                                f'FS-R({a},{b};c={c}): all three '
                                f'die ({ca_c}; {cb}; R:{r}); D3: D')
                            return cert
                        if c < E[a]:
                            cert.append(
                                f'FSR-TIGHTEN({a}|{b};c={c}): C_{b} '
                                f'dies ({cb}), R dies ({r}); '
                                f'R6+D4+MONO: A_{c}[{a}]')
                            E[a] = c
                            changed = True
                        break
            if changed and globals_check():
                return cert
        if globals_check():
            return cert
    return None


# ---------------------------------------------------------------------------
# the nested engine (SOUND form) -- and the grave of two unsound
# drafts, kept as doctrine:
#
# NESTED FS-R AS SERVICE-SEQUENCE ELIMINATION.  From an origin (the
# seed, or a service point), FS-R at cutoff c over the currently-open
# profile gives first-service cells (service within c, ORIGINAL
# co-budgets, per FS) and -- when c < min budget -- a residual branch
# (all budgets minus c).  The searcher tries EVERY integer cutoff.  A
# branch dies ONLY by pointwise means: gnand death at the reached
# point (_dead: U4 for the served atom, D1 on carried budgets, boxes
# by U10F), or recursively (every continuation of the sub-profile
# dies).  When every branch at some cutoff dies, R6 + D3 land D.
#
# THE EXTRACTION MOVE (the sound use of seed negatives): when at
# cutoff c every branch EXCEPT the i-cells is dead, R6 reduces the
# FS-R instance to u |- A_c(i-cell), and MONO projects the seed-level
# bound A_{tau+c}[i] (tau = the origin's closed cumulative depth).
# If i carries a late fact ~A_L[i] with tau + c <= L, PC lands D.
# This is derivable machinery -- R6 + D4 + MONO + U7 + PC -- no new
# axiom.
#
# TWO UNSOUND DRAFTS, caught by the soundness control (8 false fires
# on family-SAT cores, receipts in the development record), banked
# so no successor rebuilds them:
#   (1) per-branch late_kill -- refuting an i-cell directly by the
#       seed negative ~A_L[i].  UNSOUND: ~A_L is the negation of an
#       ALL-trajectory bound, i.e. EXISTENTIAL ("some trajectory
#       delays i past L"); it cannot refute a single branch, only
#       contradict a derived all-trajectory bound.  The two-exact
#       specimen pend=((0,3),(1,3)), gnand=((0,1,1,1)) is SAT
#       (masked delayers) yet died to the draft engine.
#   (2) FS-L ("late-service residuals": at i's first-service cell,
#       cap co-budgets at E_j - L_i because i's debut sits past
#       L_i).  UNSOUND for the same reason: i's debut exceeds L only
#       on SOME trajectory; the trajectory hitting this cell may
#       serve i early.  What the pinch semantics actually licenses
#       is the extraction at cutoff c = L (derive A_L[i], then PC)
#       -- the natural lawgap specimen closes exactly that way, no
#       new law needed.

def derive_ext(gs: GSpec, depth_cap: int = 20):
    """The extended searcher: base+FS-R tighten fixpoint, then
    multi-cutoff nested FS-R elimination with DEAD/FORCES typing.

    elim returns (dead_reason | None, forces): forces[i] = b asserts
    "every trajectory through this origin serves i by seed-level
    closed bound b" -- established when, at some cutoff, every
    branch is dead or itself forces i (an i-cell forces i by
    tau + c natively; a serve(j) branch inherits its sub-profile's
    forces; a residual branch its own).  Bounds are tracked only for
    late atoms and only while b <= L_i.  ONLY THE TOP LEVEL may cash
    forces against a seed negative (A_b[i] by R6+D4+MONO+U7, then PC
    with ~A_L[i]): a seed negative is the negation of an
    all-trajectory bound -- existential -- so it can never refute an
    individual branch, and an intermediate 'extraction kill' would
    be unsound (the previous draft's second bug, caught by the
    soundness control alongside per-branch late_kill).  A depth cap
    yields (None, {}): survivor, never a false D."""
    E = {}
    cert = derive(gs, use_fsr=True, state_out=E)
    if cert:
        return cert
    stages = dict(gs.pend)
    lates = {a: stages[a] - 1 for a in gs.exact}
    lates.update({z: h for z, h in gs.avoid})
    memo = {}

    def elim(open_B: tuple, tau: int):
        if not open_B:
            return None, {}
        key = (open_B, tau)
        if key in memo:
            return memo[key]
        memo[key] = (None, {})      # cycle guard (conservative)
        B = dict(open_B)
        r0 = _dead(set(), B, gs.gnand)
        if r0:
            memo[key] = (f'cell-dead:{r0}', {})
            return memo[key]
        if tau > depth_cap:
            return None, {}
        best_forces = {}
        for c in range(1, min(B.values()) + 1):
            deaths = []
            branch_forces = []      # per surviving branch
            for i in sorted(B):
                co = {j: b for j, b in B.items() if j != i}
                r = _dead({i}, co, gs.gnand)
                if r:
                    deaths.append(f'{i}@c{c}:point:{r}')
                    continue
                sub_dead, sub_f = elim(tuple(sorted(co.items())),
                                       tau + c)
                if sub_dead:
                    deaths.append(f'{i}@c{c}:serve[{sub_dead}]')
                    continue
                f = dict(sub_f)
                if i in lates and tau + c <= lates[i]:
                    f[i] = min(f.get(i, tau + c), tau + c)
                branch_forces.append(f)
            if c < min(B.values()):
                sub_dead, sub_f = elim(
                    tuple(sorted((j, b - c) for j, b in B.items())),
                    tau + c)
                if sub_dead:
                    deaths.append(f'res@c{c}[{sub_dead}]')
                else:
                    branch_forces.append(dict(sub_f))
            if not branch_forces:
                memo[key] = (f'FSR(c={c}) ALL-DEAD{{'
                             + ' ;; '.join(deaths) + '}}', {})
                return memo[key]
            # atoms forced on EVERY surviving branch: bound = the
            # worst (max) branch bound -- every trajectory hits some
            # branch, and dead branches carry no trajectories
            common = set.intersection(*[set(f) for f in
                                        branch_forces])
            for i in common:
                b = max(f[i] for f in branch_forces)
                if b <= lates.get(i, -1):
                    cur = best_forces.get(i)
                    if cur is None or b < cur:
                        best_forces[i] = b
        # PROFILE SELECTION (the drop rule): FS/FS-R apply to any
        # sub-conjunction of the budget facts, and a DISTRACTOR atom
        # -- one whose early service rides an FS branch carrying
        # original co-budgets, un-pinning the residual time
        # accounting (the deduction-side costume of the family's
        # masking mechanism) -- can make every full-profile split
        # inconclusive while a sub-profile split closes.  Dropping x
        # analyzes the same cell using strictly fewer facts: dead and
        # forces conclusions remain sound verbatim.
        if len(B) > 1:
            for x in sorted(B):
                sub_dead, sub_f = elim(
                    tuple(kv for kv in open_B if kv[0] != x), tau)
                if sub_dead:
                    memo[key] = (f'drop({x})[{sub_dead}]', {})
                    return memo[key]
                for i, b in sub_f.items():
                    cur = best_forces.get(i)
                    if cur is None or b < cur:
                        best_forces[i] = b
        memo[key] = (None, best_forces)
        return memo[key]

    dead, forces = elim(tuple(sorted(E.items())), 0)
    if dead:
        return ['NESTED (multi-cutoff FS-R); R6+D3: D', dead]
    for i, b in sorted(forces.items()):
        if b <= lates.get(i, -1):
            return [f'NESTED-FORCES: every trajectory serves {i} '
                    f'by {b} (R6+D4+MONO+U7: A_{b}[{i}]) vs '
                    f'~A_{lates[i]}[{i}]: PC: D']
    return None


def random_branch_core(rng: random.Random, i: int):
    """Targeted generator for the lawgap class (the branch-refuted
    population is ~1/4000 in the uniform tiers -- too thin to sweep).
    Shape: a late root (exact or avoid) whose seed stage sits inside
    the root-side windows of its follower gnands (creating the bans
    that put followers on the late branch), plus follower-follower
    structure with windows near budgets (pinch material)."""
    nf = rng.randint(1, 3)
    atoms = tuple(range(nf + 1))
    s0 = rng.randint(2, 3)
    pend = [(0, s0)]
    for u in range(1, nf + 1):
        pend.append((u, rng.randint(2, 5)))
    stages = dict(pend)
    if rng.random() < 0.6:
        exact, avoid = (0,), ()
    else:
        exact, avoid = (), ((0, rng.randint(1, s0 - 1)),)
    gnand = []
    for u in range(1, nf + 1):
        if rng.random() < 0.85:
            d0 = rng.randint(s0, s0 + 1)        # ban material
            du = rng.randint(1, 2)
            gnand.append((0, d0, u, du))
    for u in range(1, nf + 1):
        for v in range(u + 1, nf + 1):
            if rng.random() < 0.7:
                gnand.append((u, rng.randint(1, stages[u]), v,
                              rng.randint(1, stages[v])))
    return GSpec(name=f'br{i}', atoms=atoms, pend=tuple(pend),
                 exact=exact, avoid=avoid,
                 gnand=tuple(dict.fromkeys(gnand)))


def nested_sweep(out, want=300, tries=40000, seed=485118,
                 fam_sample=30):
    """The branch-engine sweep: build a branch-refuted population
    with the targeted generator, corroborate a sample semantically
    (family refusal -- the branch check is class-sound, so a SAT here
    is a LOUD alarm), then attempt the nested derivation.  Every
    STUCK cell is a genuine fifth-correction candidate (the sound
    engine has no law left to blame)."""
    print(f'## nested-derivation sweep (targeted generator, seed '
          f'{seed})', file=out)
    rng = random.Random(seed)
    pop = []
    drawn = 0
    for i in range(tries):
        if len(pop) >= want:
            break
        gs = random_branch_core(rng, i)
        drawn += 1
        if screen(gs) or pg_law_infeasible(gs) is not None:
            continue
        br = late_branch_pinch(gs)
        if br is None:
            continue
        pop.append((gs, br))
    print(f'- population: {len(pop)} branch-refuted cores from '
          f'{drawn} draws (13.3-clean, LATE-BRANCH-PINCH fires)',
          file=out)
    by_mode = {}
    for gs, br in pop:
        mode = ('deadline' if 'deadline' in br else
                'doubly' if 'doubly' in br else 'cycle')
        by_mode[mode] = by_mode.get(mode, 0) + 1
    print(f'- pinch modes: {by_mode}', file=out)
    ok = True
    # semantic corroboration (class-soundness control)
    alarms = 0
    for gs, br in pop[:fam_sample]:
        n = len(gs.pend)
        for m in range(1, n + 3):
            if family_probe(gs, m) == 'SAT':
                alarms += 1
                ok = False
                print(f'- !! ALARM family-SAT on branch-refuted '
                      f'{gs.name}: pend={gs.pend} exact={gs.exact} '
                      f'avoid={gs.avoid} gnand={gs.gnand} at m={m} '
                      f'({br}) -- LATE-BRANCH-PINCH class-soundness '
                      f'breach', file=out)
                break
    print(f'- semantic corroboration: {min(fam_sample, len(pop))} '
          f'specimens family-probed, {alarms} alarms'
          f'{" (clean)" if alarms == 0 else ""}', file=out)
    # the derivation tiers
    tiers = {'pair-mirror': 0, 'nested': 0, 'stuck': 0}
    stuck = []
    for gs, br in pop:
        if derive(gs, use_fsr=True):
            tiers['pair-mirror'] += 1
        elif derive_ext(gs):
            tiers['nested'] += 1
        else:
            tiers['stuck'] += 1
            if len(stuck) < 24:
                stuck.append((gs, br))
    print(f'- derivation tiers: {tiers}', file=out)
    print(file=out)
    if stuck:
        print('## STUCK cells (branch-refuted, underivable by the '
              'sound engine -- genuine fifth-correction candidates)',
              file=out)
        for gs, br in stuck:
            print(f'- pend={gs.pend} exact={gs.exact} '
                  f'avoid={gs.avoid} gnand={gs.gnand}', file=out)
            print(f'  {br}', file=out)
        print(file=out)
    return ok, tiers, stuck


def nested_soundness(out, rounds=400, seed=485) -> bool:
    """derive_ext (both flavors) must stay silent on family-SAT
    cores -- the nested engine is a new deduction surface and gets
    its own control, same population as soundness_control."""
    from family import random_pg_core
    rng = random.Random(seed)
    fired = checked = 0
    for i in range(rounds):
        gs = random_pg_core(rng, i)
        if pg_law_infeasible(gs) is not None or screen(gs):
            continue
        n = len(gs.pend)
        sat = any(family_probe(gs, m) == 'SAT'
                  for m in range(1, n + 2))
        if not sat:
            continue
        checked += 1
        if derive_ext(gs):
            fired += 1
            print(f'!! derive_ext fired on family-SAT core '
                  f'pend={gs.pend} exact={gs.exact} '
                  f'avoid={gs.avoid} gnand={gs.gnand}', file=out)
    print('## nested soundness control (derive_ext silent on '
          'family-SAT cores)', file=out)
    print(f'- {checked} family-SAT cores checked, {fired} false '
          f'fires {"(clean)" if fired == 0 else "!! ALARM"}',
          file=out)
    print(file=out)
    return fired == 0


# ---------------------------------------------------------------------------
# the enumerator (exhaustive small boxes, deduped by atom symmetry)

def _canon(gs: GSpec):
    """Canonical form under atom permutation."""
    n = len(gs.atoms)
    stages = dict(gs.pend)
    best = None
    for perm in itertools.permutations(range(n)):
        p = {a: perm[i] for i, a in enumerate(gs.atoms)}
        key = (tuple(sorted((p[x], s) for x, s in gs.pend)),
               tuple(sorted(p[x] for x in gs.exact)),
               tuple(sorted((p[z], h) for z, h in gs.avoid)),
               tuple(sorted(min((p[x], d1, p[y], d2),
                                (p[y], d2, p[x], d1))
                            for x, d1, y, d2 in gs.gnand)))
        if best is None or key < best:
            best = key
    return best


def _marker_options(s):
    """Per-atom lateness marker: none, exact (s>=2), avoid-h (h<s)."""
    opts = [('none', None)]
    if s >= 2:
        opts.append(('exact', None))
        for h in range(1, s):
            opts.append(('avoid', h))
    return opts


def enumerate_pg(n, smax, wmax, pmax, out):
    """All pure-gnand cores: n atoms all pending at stages 1..smax,
    one lateness marker per atom, up to pmax distinct gnand
    constraints with windows 1..wmax; deduped by atom symmetry."""
    pair_universe = []
    for x, y in itertools.combinations(range(n), 2):
        for d1 in range(1, wmax + 1):
            for d2 in range(1, wmax + 1):
                pair_universe.append((x, d1, y, d2))
    seen = set()
    count = 0
    for stages in itertools.product(range(1, smax + 1), repeat=n):
        marker_axes = [_marker_options(s) for s in stages]
        for markers in itertools.product(*marker_axes):
            exact = tuple(i for i in range(n)
                          if markers[i][0] == 'exact')
            avoid = tuple((i, markers[i][1]) for i in range(n)
                          if markers[i][0] == 'avoid')
            for k in range(0, pmax + 1):
                for pairs in itertools.combinations(pair_universe, k):
                    gs = GSpec(name=f'e{count}',
                               atoms=tuple(range(n)),
                               pend=tuple((i, stages[i])
                                          for i in range(n)),
                               exact=exact, avoid=avoid,
                               gnand=pairs)
                    key = _canon(gs)
                    if key in seen:
                        continue
                    seen.add(key)
                    count += 1
                    yield gs


# ---------------------------------------------------------------------------
# the sweep

def sweep(out, nmax=3, smax=4, wmax=3, pmax_by_n={2: 3, 3: 2},
          fine_check=True):
    tot = {'feasible': 0, 'derived-base': 0, 'derived-fsr': 0,
           'survivor': 0}
    by_check = {}
    crosstab = {}
    survivors, fsr_specimens = [], []
    doc_code_split = {'both': 0, 'code-only': 0, 'doc-only': 0}
    code_only_tiers = {}

    def classify(gs, law, tier_sink=None):
        kind = law.split('(')[0].split(' ')[0]
        by_check[kind] = by_check.get(kind, 0) + 1
        law_doc = pg_law_infeasible_doc(gs)
        if law_doc is None:
            doc_code_split['code-only'] += 1
        else:
            doc_code_split['both'] += 1
        c0 = derive(gs, use_fsr=False)
        if c0:
            tier = 'derived-base'
        else:
            c1 = derive(gs, use_fsr=True)
            tier = 'derived-fsr' if c1 else 'survivor'
        tot[tier] += 1
        crosstab[(kind, tier)] = crosstab.get((kind, tier), 0) + 1
        if law_doc is None:
            code_only_tiers[tier] = code_only_tiers.get(tier, 0) + 1
        if tier == 'derived-fsr' and len(fsr_specimens) < 12:
            fsr_specimens.append((gs, law, derive(gs, use_fsr=True)))
        if tier == 'survivor' and len(survivors) < 40:
            survivors.append((gs, law, law_doc))
        return tier

    tot['branch-refuted'] = 0
    branch_specimens = []
    for n in range(2, nmax + 1):
        pmax = pmax_by_n.get(n, 2)
        for gs in enumerate_pg(n, smax, wmax, pmax, out):
            law = pg_law_infeasible(gs)
            if law is None:
                br = late_branch_pinch(gs)
                if br is None:
                    tot['feasible'] += 1
                else:
                    tot['branch-refuted'] += 1
                    if len(branch_specimens) < 10:
                        branch_specimens.append((gs, br))
                continue
            classify(gs, law)
    # out-of-box random tier: n=3 at 3 pairs, n=4, stages to 5,
    # windows to 4 -- the exhaustive box's blind spots
    rng = random.Random(20260720)
    rand_stats = {'refuted': 0}
    for i in range(4000):
        n = rng.choice((3, 3, 4))
        atoms = tuple(range(n))
        pend = tuple((x, rng.randint(1, 5)) for x in atoms)
        stages = dict(pend)
        exact = tuple(x for x in atoms
                      if stages[x] >= 2 and rng.random() < 0.35)
        avoid = tuple((x, rng.randint(1, stages[x] - 1))
                      for x in atoms if stages[x] >= 2
                      and x not in exact and rng.random() < 0.25)
        gnand = []
        for _ in range(rng.randint(1, 4)):
            x, y = rng.sample(atoms, 2)
            gnand.append((x, rng.randint(1, 4), y, rng.randint(1, 4)))
        gs = GSpec(name=f'r{i}', atoms=atoms, pend=pend, exact=exact,
                   avoid=avoid, gnand=tuple(dict.fromkeys(gnand)))
        law = pg_law_infeasible(gs)
        if law is None:
            br = late_branch_pinch(gs)
            if br is not None:
                tot['branch-refuted'] += 1
                if len(branch_specimens) < 10:
                    branch_specimens.append((gs, br))
            continue
        rand_stats['refuted'] += 1
        classify(gs, law)
    print('## sweep totals (exhaustive box n<=3 + random '
          'out-of-box tier: 4000 draws at n=3/4, s<=5, w<=4, '
          f'p<=4; {rand_stats["refuted"]} refuted)', file=out)
    print(f'- {tot}', file=out)
    print(f'- refuted, by firing check: {by_check}', file=out)
    print(f'- check x derivation-tier: '
          f'{dict(sorted(crosstab.items()))}', file=out)
    print(f'- doc-vs-code calculus split on refuted cells: '
          f'{doc_code_split} (doc-only should be 0: the code '
          f'calculus subsumes the doc calculus); code-only cells '
          f'by tier: {code_only_tiers}', file=out)
    print(file=out)
    print('## DERIVED-FSR specimens (fourth-correction witnesses)',
          file=out)
    for gs, law, c1 in fsr_specimens:
        print(f'- pend={gs.pend} exact={gs.exact} avoid={gs.avoid} '
              f'gnand={gs.gnand}', file=out)
        print(f'  law: {law}', file=out)
        for step in c1:
            print(f'    {step}', file=out)
    print(file=out)
    print('## survivors (neither mirror derives)', file=out)
    for gs, law, law_doc in survivors:
        print(f'- pend={gs.pend} exact={gs.exact} avoid={gs.avoid} '
              f'gnand={gs.gnand}', file=out)
        print(f'  law: {law}   doc-law: {law_doc}', file=out)
    print(file=out)
    print('## LAW-GAP class: 13.3-feasible, LATE-BRANCH-PINCH '
          'refuted (T3-as-stated counterexample material)', file=out)
    print(f'- count: {tot["branch-refuted"]}', file=out)
    for gs, br in branch_specimens:
        print(f'- pend={gs.pend} exact={gs.exact} avoid={gs.avoid} '
              f'gnand={gs.gnand}', file=out)
        print(f'  {br}', file=out)
    print(file=out)
    if fine_check:
        semantic_recheck(survivors + [(g, b, None)
                                      for g, b in branch_specimens],
                         fsr_specimens, out)
    return tot, survivors, fsr_specimens


def semantic_recheck(survivors, fsr_specimens, out):
    """Every survivor and a DERIVED-FSR sample must be
    FAMILY-REFUSED at fine grids (they are law-infeasible, T2 is
    proved sound): masked-SAT here is a loud alarm."""
    print('## semantic re-check (winged family, fine grids)',
          file=out)
    alarms = 0
    batch = [gs for gs, *_ in survivors[:12]] + \
            [gs for gs, *_ in fsr_specimens[:6]]
    for gs in batch:
        n = len([1 for _ in gs.pend])
        verdicts = []
        for m in range(1, n + 3):
            r = family_probe(gs, m)
            verdicts.append((m, r))
            if r == 'SAT':
                alarms += 1
        vs = ', '.join(f'm={m}:{r}' for m, r in verdicts)
        print(f'- pend={gs.pend} exact={gs.exact} avoid={gs.avoid} '
              f'gnand={gs.gnand}: {vs}', file=out)
    print(f'- ALARMS (masked-SAT on law-infeasible): {alarms} '
          f'{"!! CALCULUS SOUNDNESS" if alarms else "(clean)"}',
          file=out)
    print(file=out)
    return alarms == 0


def soundness_control(out, rounds=400, seed=485):
    """derive() must not fire on any family-SAT core."""
    from family import random_pg_core
    rng = random.Random(seed)
    fired = checked = 0
    for i in range(rounds):
        gs = random_pg_core(rng, i)
        if pg_law_infeasible(gs) is not None or screen(gs):
            continue
        n = len(gs.pend)
        sat = any(family_probe(gs, m) == 'SAT'
                  for m in range(1, n + 2))
        if not sat:
            continue
        checked += 1
        for fsr in (False, True):
            if derive(gs, use_fsr=fsr):
                fired += 1
                print(f'!! derive(fsr={fsr}) fired on family-SAT '
                      f'core pend={gs.pend} gnand={gs.gnand}',
                      file=out)
        if late_branch_pinch(gs):
            fired += 1
            print(f'!! late_branch_pinch fired on family-SAT core '
                  f'pend={gs.pend} exact={gs.exact} '
                  f'avoid={gs.avoid} gnand={gs.gnand}', file=out)
    print('## soundness control (derive + branch-pinch silent on '
          'family-SAT cores)', file=out)
    print(f'- {checked} family-SAT cores checked, {fired} false '
          f'fires {"(clean)" if fired == 0 else "!! ALARM"}',
          file=out)
    print(file=out)
    return fired == 0


def nested_hand(out) -> bool:
    """Nested hand cases: the two branch-refuted witnesses must fall
    to the nested engine (the witness-level branch-twin, mechanized:
    the lawgap derivation closes at depth 1 via nested FS-R --
    verify it does)."""
    ok = True
    print('## nested hand cases', file=out)
    gap = GSpec(name='lawgap-hand', atoms=(0, 1, 2),
                pend=((0, 2), (1, 4), (2, 4)), exact=(0,),
                gnand=((0, 2, 1, 1), (0, 2, 2, 1), (1, 3, 2, 3)))
    nat = GSpec(name='lawgap-natural (random-tier find)',
                atoms=(0, 1, 2), pend=((0, 5), (1, 5), (2, 3)),
                exact=(1,), avoid=((0, 2), (2, 2)),
                gnand=((1, 3, 0, 4), (1, 2, 2, 4), (0, 1, 2, 4)))
    for gs in (gap, nat):
        pair = derive(gs, use_fsr=True)
        c0 = derive_ext(gs)
        tier = ('pair-mirror' if pair else 'nested' if c0
                else 'STUCK')
        good = tier != 'STUCK'
        ok &= good
        print(f'- {gs.name}: {tier}'
              + (' !! expected a derivation' if not good else ''),
              file=out)
        c = pair or c0
        if c and len(c) > 1:
            print(f'    {c[1][:300]}', file=out)
    print(file=out)
    return ok


# ---------------------------------------------------------------------------
# the last two deduction-side slivers: cross-pair descent + cycle
# schema
#
# (1) THE CROSS-PAIR DESCENT.  The iterative-class residual case
# dissolves with NO new machinery: iterated single-cutoff FSR-TIGHTEN
# steps -- each already in derive()'s move set -- provably reach every
# code-calculus tighten value nv = max(E_b - W, 1) (W = the largest
# b-side window over the pair's gnands) whenever some gnand kills the
# b-first cell at a's current bound (the ban).  Construction:
#   bridge  -- while E_a > E_b >= 2: cutoff c = E_b - 1; the residual
#              (E_a - c, 1) dies via the ban gnand (a-side E_a <= D1,
#              monotone under shrink; b-side 1 <= any window):
#              E_a <- E_b - 1.  (E_b = 1: plain FS_2 at s* = 1, the
#              b-cell dies via the ban, FS-TIGHTEN gives E_a <- 1.)
#   descent -- while nv < E_a <= E_b: cutoff c = E_a - 1; the residual
#              (1, E_b - E_a + 1) dies via the max-window gnand
#              (a-side 1 <= its window; b-side E_b - E_a + 1 <= W iff
#              E_a - 1 >= E_b - W, true while E_a > nv): E_a <- E_a-1.
# Terminates at exactly nv.  derive() takes minimal dying cutoffs,
# which descend at least as fast -- so the CODED mirror realizes every
# cross-pair tighten: the exhaustive box's 0-survivor result upgrades
# from corroboration to theorem.

def descent_steps(Ea, Eb, gnand):
    """Verify the descent construction step by step on the pair {0, 1}
    (a = 0, b = 1): every step a checked FS/FS-R instance.  Returns
    (bound, trace): bound == nv on success, 0 when all three
    disjuncts die (D outright), None with the failure in the trace --
    the descent lemma's per-configuration machine face."""
    def bwin(g):
        x, d1, y, d2 = g
        return d2 if x == 0 else d1
    W = max(bwin(g) for g in gnand)
    nv = max(Eb - W, 1)
    trace = []
    E = Ea
    if nv >= E:
        return E, trace
    guard = 0
    while E > nv:
        guard += 1
        if guard > 200:
            return None, trace + ['!! descent did not terminate']
        cb = _dead({1}, {0: E}, gnand)
        if not cb:
            return None, trace + [f'!! ban lost at E_a={E}']
        ca = _dead({0}, {1: Eb}, gnand)
        if ca:
            trace.append(f'a-cell also dies ({ca}); with C_b dead '
                         f'({cb}): FS_2 + R6 + D3: D')
            return 0, trace
        if min(E, Eb) == 1:
            trace.append(f'plain FS_2 (s*=1): C_b dies ({cb}); '
                         f'FS-TIGHTEN: E_a <- 1')
            E = 1
            continue
        c = Eb - 1 if E > Eb else E - 1
        if not 0 < c < min(E, Eb):
            return None, trace + [f'!! invalid cutoff {c} at '
                                  f'E_a={E}']
        r = _dead(set(), {0: E - c, 1: Eb - c}, gnand)
        if not r:
            return None, trace + [f'!! residual survives at c={c}, '
                                  f'E_a={E}']
        trace.append(f'FSR-TIGHTEN(c={c}): C_b dies ({cb}), R dies '
                     f'({r}): E_a <- {c}')
        E = c
    return E, trace


def crosspair_cmd(out) -> bool:
    """16.1's machine faces.  (a) Abstract configuration sweep: every
    strict cross-pair tighten config's descent construction verified
    step-by-step, with the ITERATIVE-class census (single-shot stuck
    above nv -- the exact case the single-shot analysis left open;
    must be nonempty).
    (b) The coded mirror reaches nv on every config (artifact pair
    for (a)).  (c) Concrete code-only-refuted cores (doc calculus
    silent, code calculus fires, stages/windows OUTSIDE the
    exhaustive box) all derive D; sample family-corroborated REFUSED;
    family-SAT pair cores leave the engine silent."""
    ok = True
    print("## cross-pair descent: abstract configuration sweep "
          "(E_a,E_b,D1,D2' in 1..8; D1',D2 in 1..3; ban E_a <= D1)",
          file=out)
    n_cfg = n_iter = n_d = 0
    gaps = []
    for Ea, Eb, D1, D1p, D2, D2p in itertools.product(
            range(1, 9), range(1, 9), range(1, 9), range(1, 4),
            range(1, 4), range(1, 9)):
        if Ea > D1:
            continue
        gn = ((0, D1, 1, D1p), (0, D2, 1, D2p))
        nv = max(Eb - max(D1p, D2p), 1)
        if nv >= Ea:
            continue
        n_cfg += 1
        # the 14.2 single-shot value: minimal dying cutoff, one round
        v1 = Ea
        if _dead({1}, {0: Ea}, gn):
            for c in range(1, min(Ea, Eb)):
                if _dead(set(), {0: Ea - c, 1: Eb - c}, gn):
                    v1 = min(v1, c)
                    break
        if v1 > nv:
            n_iter += 1
        v, trace = descent_steps(Ea, Eb, gn)
        if v == 0:
            n_d += 1
        elif v != nv:
            gaps.append(('descent', Ea, Eb, D1, D1p, D2, D2p, nv, v,
                         trace[-1:]))
        gs = GSpec(name='xp', atoms=(0, 1), pend=((0, Ea), (1, Eb)),
                   exact=(), avoid=(), gnand=gn)
        E = {}
        cert = derive(gs, use_fsr=True, state_out=E)
        if not cert and E.get(0, 99) > nv:
            gaps.append(('coded-mirror', Ea, Eb, D1, D1p, D2, D2p,
                         nv, E.get(0)))
    print(f'- {n_cfg} configs with a strict cross-pair tighten; '
          f'{n_iter} ITERATIVE-class (single-shot stuck above nv -- '
          f"14.2's open residual case, nonempty and covered), "
          f'{n_d} land D outright; gaps: {len(gaps)}', file=out)
    for g in gaps[:8]:
        print(f'  !! GAP {g}', file=out)
    ok &= not gaps and n_iter > 0
    print(file=out)
    print('## concrete code-only cores (doc-silent, code-fires; '
          'stages 3..8, windows to 8 -- out-of-box)', file=out)
    rng = random.Random(4851901)
    found = derived = 0
    fam_checked = fam_bad = 0
    sat_checked = sat_fired = 0
    stuck = []
    for i in range(20000):
        Ea = rng.randint(3, 7)
        Eb = rng.randint(3, 8)
        D1 = rng.randint(Ea, 8)
        D1p = rng.randint(1, 2)
        D2 = rng.randint(1, 2)
        D2p = min(8, rng.randint(D1p + 1, 8))
        gs = GSpec(name=f'xp{i}', atoms=(0, 1),
                   pend=((0, Ea), (1, Eb)), exact=(0,), avoid=(),
                   gnand=((0, D1, 1, D1p), (0, D2, 1, D2p)))
        code = pg_law_infeasible(gs)
        if code is None:
            if sat_checked < 40 and not screen(gs) \
                    and family_probe(gs, 3) == 'SAT':
                sat_checked += 1
                if derive(gs, use_fsr=True) or derive_ext(gs):
                    sat_fired += 1
                    print(f'  !! engine fired on family-SAT pair '
                          f'core pend={gs.pend} gnand={gs.gnand}',
                          file=out)
            continue
        if pg_law_infeasible_doc(gs) is not None:
            continue
        found += 1
        if derive(gs, use_fsr=True):
            derived += 1
        elif len(stuck) < 5:
            stuck.append((Ea, Eb, D1, D1p, D2, D2p, code))
        if fam_checked < 25:
            fam_checked += 1
            if any(family_probe(gs, m) == 'SAT' for m in (1, 2, 3)):
                fam_bad += 1
                print(f'  !! ALARM family-SAT on code-refuted '
                      f'pend={gs.pend} gnand={gs.gnand}', file=out)
    print(f'- code-only refuted cores: {found}; derived '
          f'{derived}/{found}; family corroboration {fam_checked} '
          f'sampled, {fam_bad} alarms; family-SAT silence control '
          f'{sat_checked} checked, {sat_fired} false fires',
          file=out)
    for s in stuck:
        print(f'  !! STUCK {s}', file=out)
    ok &= derived == found and fam_bad == 0 and sat_fired == 0 \
        and found > 100
    print(file=out)
    return ok


# (2) THE CYCLE-MODE BRANCH-TWIN (16.2).  For a late fact (a, L),
# branch set X, and a CYCLE in the forced-order digraph (prec edges +
# singly-pinched-side-first edges): run the mirror to its fixpoint
# (WLOG every E_u > L -- otherwise the 16.1 descent along the prec
# chain drives the LATE/GB endgames); drop to X; FS-R over
# {A_{E_u}[u] : u in X} at cutoff c = L.  Every non-a cell dies
# pointwise via its in-prec ban gnand (every X-atom but a has one,
# by X's construction); the a-cell forces (a, L); and the residual
# subtree -- where every carried budget is <= E_u - L, so every
# pinch-edge death fires by D1 (budget <= eff_u - L <= window) -- is
# DEAD: a service violating a digraph edge dies pointwise via the
# edge's witness gnand, cycle atoms always have an open in-neighbor
# (services strictly ordered; the first cycle atom served violates
# its in-edge), non-cycle services shrink the profile, residual
# descents shrink budgets to the plain-FS floor.  FORCES composition
# (15.4) yields A_L[a]; PC against the late fact lands D.

def _cycle_data(gs: GSpec, E):
    """Forced-order digraphs with witnesses, per late fact: rows
    (a, L, kind, X, edges) where edges[(u, v)] = (kind, gnand) means
    u must precede v on the late branch, and serving v with u open
    dies pointwise via the witness gnand."""
    eff, prec = pg_effective(gs)
    stages = dict(gs.pend)
    rows = []
    lates = [(x, stages[x] - 1, 'exact') for x in gs.exact
             if x in stages] + \
            [(z, h, 'avoid') for z, h in gs.avoid if z in stages]
    for a, L, kind in lates:
        X = _prec_desc(prec, a)
        edges = {}
        for u, v in prec:
            if u in X and v in X and (u, v) not in edges:
                for x, d1, y, d2 in gs.gnand:
                    for p, dp, q, dq in ((x, d1, y, d2),
                                         (y, d2, x, d1)):
                        if (p, q) == (u, v) and \
                                eff.get(p, 10**9) <= dp:
                            edges[(u, v)] = ('prec',
                                             (x, d1, y, d2))
                            break
                    if (u, v) in edges:
                        break
        for x, d1, y, d2 in gs.gnand:
            if x in X and y in X and x in eff and y in eff:
                if eff[x] - d1 <= L:
                    edges.setdefault((x, y),
                                     ('pinch', (x, d1, y, d2)))
                if eff[y] - d2 <= L:
                    edges.setdefault((y, x),
                                     ('pinch', (x, d1, y, d2)))
        rows.append((a, L, kind, X, edges))
    return rows


def _find_cycle(nodes, edges):
    """A directed cycle's node set, or None."""
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
    color = {u: 0 for u in nodes}
    stack, cyc = [], []

    def dfs(u):
        color[u] = 1
        stack.append(u)
        for w in adj.get(u, ()):
            if w not in color:
                continue
            if color[w] == 1:
                cyc.extend(stack[stack.index(w):])
                return True
            if color[w] == 0 and dfs(w):
                return True
        color[u] = 2
        stack.pop()
        return False

    for u in sorted(nodes):
        if color[u] == 0 and dfs(u):
            return frozenset(cyc)
    return None


def _subtree_dead(open_set, budgets_t, C, edges, memo):
    """The 16.2 induction, mechanized: a position (open obligations,
    carried budgets) inside the top-level residual subtree is dead.
    Service cells: a service of u with an open in-neighbor v dies
    pointwise via the edge's witness gnand alone (checked); cycle
    atoms always have one; other services recurse on the smaller
    profile carrying this instance's budgets (FS-R service cells);
    the unit-cutoff residual recurses with decremented budgets while
    min budget > 1 (at the floor, plain FS has service cells only).
    Returns (dead, why)."""
    key = (open_set, budgets_t)
    if key in memo:
        return memo[key]
    memo[key] = (False, 'cycle-guard')
    if not C <= open_set:
        memo[key] = (False, f'cycle atom served: C={sorted(C)}')
        return memo[key]
    B = dict(budgets_t)
    for u in sorted(open_set):
        died = None
        for (v, u2), (_, g) in edges.items():
            if u2 == u and v in open_set and v != u:
                d = _dead({u}, {v: B[v]}, (g,))
                if d:
                    died = d
                    break
        if died:
            continue
        if u in C:
            memo[key] = (False, f'cycle atom {u} cell survived')
            return memo[key]
        sub = frozenset(open_set - {u})
        subB = tuple(kv for kv in budgets_t if kv[0] != u)
        dead, why = _subtree_dead(sub, subB, C, edges, memo)
        if not dead:
            memo[key] = (False, f'serve({u}) -> {why}')
            return memo[key]
    if min(B.values()) > 1:
        dead, why = _subtree_dead(
            open_set, tuple((k, b - 1) for k, b in budgets_t),
            C, edges, memo)
        if not dead:
            memo[key] = (False, f'residual -> {why}')
            return memo[key]
    memo[key] = (True, '')
    return memo[key]


def cycle_schema_cert(gs: GSpec):
    """Mechanize the 16.2 construction; every cited death checked by
    _dead against the witness gnand alone.  Returns
    ('MIRROR-ENDGAME', cert), ('CYCLE-SCHEMA', steps), or None."""
    E = {}
    cert = derive(gs, use_fsr=True, state_out=E)
    if cert:
        return ('MIRROR-ENDGAME', cert)
    for a, L, kind, X, edges in _cycle_data(gs, E):
        C = _find_cycle(X, edges)
        if C is None or L < 1:
            continue
        if any(E[u] <= L for u in X):
            print(f'!! cycle schema on {gs.name}: some E_u <= L '
                  f'with the mirror silent (16.1 descent should '
                  f'have landed D)')
            return None
        steps = [f'drop to X={sorted(X)}; FS-R at c=L={L}, '
                 f'E={ {u: E[u] for u in sorted(X)} }']
        all_die = True
        for b in sorted(X - {a}):
            wit = None
            for (u, v), (ek, g) in edges.items():
                if v == b and ek == 'prec' and u in X:
                    d = _dead({b}, {u: E[u]}, (g,))
                    if d:
                        wit = (g, d)
                        break
            if wit is None:
                all_die = False
                break
            steps.append(f'  {b}-cell dies via prec ban {wit[0]} '
                         f'({wit[1]})')
        if not all_die:
            print(f'!! cycle schema on {gs.name}: a non-a cell '
                  f'survived its in-prec check')
            return None
        memo = {}
        B0 = tuple(sorted((u, E[u] - L) for u in X))
        dead, why = _subtree_dead(frozenset(X), B0, C, edges, memo)
        if not dead:
            print(f'!! cycle schema on {gs.name}: residual subtree '
                  f'NOT dead: {why}')
            return None
        steps.append(f'  residual subtree DEAD (cycle {sorted(C)}; '
                     f'{len(memo)} positions checked)')
        steps.append(f'  FORCES (15.4): A_{L}[{a}]; PC vs '
                     f'~A_{L}[{a}] ({kind}): D')
        return ('CYCLE-SCHEMA', steps)
    return None


def random_cycle_core(rng: random.Random, i: int):
    """Targeted generator for the CYCLE mode (~9/1000 in the
    branch-engine population -- too thin to sweep): a late root banned
    before its followers, follower-follower gnands pinching a
    directed cycle (each singly pinched; doubly-pinched pairs would
    fire mode 2 first), follower stages > L + 1 so the deadline mode
    stays silent."""
    k = rng.randint(2, 3)
    extra = rng.randint(0, 1)
    nf = k + extra
    s0 = rng.randint(3, 4)
    if rng.random() < 0.5:
        exact, avoid, L = (0,), (), s0 - 1
    else:
        h = rng.randint(1, s0 - 1)
        exact, avoid, L = (), ((0, h),), h
    pend = [(0, s0)]
    for u in range(1, nf + 1):
        pend.append((u, L + rng.randint(2, 4)))
    stages = dict(pend)
    gnand = []
    for u in range(1, nf + 1):
        d0 = s0 + rng.randint(0, 2)
        du = rng.randint(1, max(1, stages[u] - L - 1))
        gnand.append((0, d0, u, du))
    cyc = list(range(1, k + 1))
    rng.shuffle(cyc)
    for j in range(k):
        u, v = cyc[j], cyc[(j + 1) % k]
        du = rng.randint(max(1, stages[u] - L), stages[u] - 1)
        dv = rng.randint(1, max(1, stages[v] - L - 1))
        gnand.append((u, du, v, dv))
    if extra and rng.random() < 0.6:
        u, v = nf, rng.choice(cyc)
        gnand.append((u, rng.randint(1, stages[u]), v,
                      rng.randint(1, stages[v])))
    return GSpec(name=f'cy{i}', atoms=tuple(range(nf + 1)),
                 pend=tuple(pend), exact=exact, avoid=avoid,
                 gnand=tuple(dict.fromkeys(gnand)))


def cycle_cmd(out, want=200, tries=60000, seed=485019) -> bool:
    """16.2's machine faces: targeted cycle population; every
    specimen must certify under the SCHEMA construction and derive
    under the coded engine; a sample must be family-REFUSED at every
    probed grid; and family-SAT broken-cycle variants must leave
    schema and engine silent."""
    rng = random.Random(seed)
    pop, seen = [], set()
    drawn = 0
    for i in range(tries):
        if len(pop) >= want:
            break
        gs = random_cycle_core(rng, i)
        drawn += 1
        if screen(gs) or pg_law_infeasible(gs) is not None:
            continue
        br = late_branch_pinch(gs)
        if br is None or 'cycle' not in br:
            continue
        key = _canon(gs)
        if key in seen:
            continue
        seen.add(key)
        pop.append((gs, br))
    print(f'## cycle-mode schema sweep (targeted generator, seed '
          f'{seed}): {len(pop)} distinct cycle-refuted cores from '
          f'{drawn} draws', file=out)
    tiers = {'CYCLE-SCHEMA': 0, 'MIRROR-ENDGAME': 0, 'FAIL': 0}
    eng = {'derived': 0, 'stuck': 0}
    fails = []
    for gs, br in pop:
        r = cycle_schema_cert(gs)
        if r is None:
            tiers['FAIL'] += 1
            if len(fails) < 8:
                fails.append((gs, br))
        else:
            tiers[r[0]] += 1
        if derive(gs, use_fsr=True) or derive_ext(gs):
            eng['derived'] += 1
        else:
            eng['stuck'] += 1
    print(f'- schema tiers: {tiers}; engine: {eng}', file=out)
    for gs, br in fails:
        print(f'  !! SCHEMA FAIL pend={gs.pend} exact={gs.exact} '
              f'avoid={gs.avoid} gnand={gs.gnand}: {br}', file=out)
    ok = tiers['FAIL'] == 0 and eng['stuck'] == 0 and len(pop) >= 50
    alarms = 0
    sample = pop[:16]
    for gs, br in sample:
        n = len(gs.pend)
        if any(family_probe(gs, m) == 'SAT'
               for m in range(1, n + 2)):
            alarms += 1
            print(f'  !! ALARM family-SAT on cycle-refuted '
                  f'{gs.name}: pend={gs.pend} gnand={gs.gnand}',
                  file=out)
    print(f'- family corroboration: {len(sample)} specimens, '
          f'{alarms} alarms{" (clean)" if alarms == 0 else ""}',
          file=out)
    ok &= alarms == 0
    ctrl_checked = ctrl_bad = 0
    for gs, br in pop:
        if ctrl_checked >= 20:
            break
        ff = [g for g in gs.gnand if g[0] != 0 and g[2] != 0]
        if not ff:
            continue
        v = GSpec(name=gs.name + 'b', atoms=gs.atoms, pend=gs.pend,
                  exact=gs.exact, avoid=gs.avoid,
                  gnand=tuple(g for g in gs.gnand if g != ff[0]))
        if screen(v) or pg_law_infeasible(v) is not None \
                or late_branch_pinch(v) is not None:
            continue
        n = len(v.pend)
        if not any(family_probe(v, m) == 'SAT'
                   for m in range(1, n + 2)):
            continue
        ctrl_checked += 1
        if cycle_schema_cert(v) is not None \
                or derive(v, use_fsr=True) or derive_ext(v):
            ctrl_bad += 1
            print(f'  !! CONTROL fired on family-SAT broken-cycle '
                  f'variant of {gs.name}: pend={v.pend} '
                  f'gnand={v.gnand}', file=out)
    print(f'- broken-cycle control: {ctrl_checked} family-SAT '
          f'variants, {ctrl_bad} false fires'
          f'{" (clean)" if ctrl_bad == 0 else ""}', file=out)
    ok &= ctrl_bad == 0
    print(file=out)
    return ok


def coverage_hand(out) -> bool:
    """Coverage hand cases: the descent on an iterative-class
    configuration, and the cycle schema on a dissected sweep
    specimen."""
    ok = True
    print('## coverage hand cases (descent + cycle schema)', file=out)
    gn = ((0, 6, 1, 1), (0, 1, 1, 2))
    v, trace = descent_steps(6, 4, gn)
    print(f'- descent (E_a=6, E_b=4, W=2 -> nv=2; single-shot '
          f'sticks at 3): certified bound {v}', file=out)
    for t in trace:
        print(f'    {t}', file=out)
    ok &= v == 2
    gs = GSpec(name='xp-hand', atoms=(0, 1), pend=((0, 6), (1, 4)),
               exact=(), avoid=(), gnand=gn)
    E = {}
    cert = derive(gs, use_fsr=True, state_out=E)
    print(f'- coded mirror on the same pair: E_a = {E.get(0)} '
          f'(expect 2; derived-D: {bool(cert)})', file=out)
    ok &= not cert and E.get(0) == 2
    cyc = GSpec(name='cyc-hand', atoms=(0, 1, 2, 3),
                pend=((0, 3), (1, 5), (2, 4), (3, 5)), exact=(0,),
                avoid=(),
                gnand=((0, 3, 1, 2), (0, 4, 2, 1), (0, 3, 3, 2),
                       (1, 1, 2, 3), (1, 4, 3, 1), (2, 1, 3, 3)))
    r = cycle_schema_cert(cyc)
    tier = r[0] if r else 'FAIL'
    edrv = bool(derive_ext(cyc))
    print(f'- cycle specimen (dissected from the sweep): schema '
          f'{tier} (expect CYCLE-SCHEMA); engine '
          f'{"derived" if edrv else "STUCK"}', file=out)
    ok &= r is not None and tier == 'CYCLE-SCHEMA' and edrv
    if r and tier == 'CYCLE-SCHEMA':
        for s in r[1]:
            print(f'    {s}', file=out)
    print(file=out)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', nargs='?', default='battery',
                    choices=['battery', 'sweep', 'control', 'hand',
                             'nested', 'crosspair', 'cycle',
                             'coverage'])
    ap.add_argument('--want', type=int, default=300,
                    help='nested: branch-refuted population size')
    ap.add_argument('--tries', type=int, default=40000,
                    help='nested: generator draw budget')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    out = open(args.out, 'w') if args.out else sys.stdout
    ok = True
    print('# derivation -- the derivation-sweep instrument',
          file=out)
    print(file=out)
    if args.cmd in ('battery', 'hand'):
        # the hand-dissected wall candidate must classify DERIVED-FSR
        wall = GSpec(name='wall-hand', atoms=(0, 1),
                     pend=((0, 2), (1, 3)), exact=(0,),
                     gnand=((0, 2, 1, 2),))
        law = pg_law_infeasible(wall)
        c0 = derive(wall, use_fsr=False)
        c1 = derive(wall, use_fsr=True)
        print('## the hand candidate (pend a@2 exact, b@3, '
              'gnand(a,2,b,2))', file=out)
        print(f'- law: {law} (expect LATE-EFF on atom 0)', file=out)
        print(f'- base basis: {"DERIVED " + str(c0) if c0 else "no derivation (the telescoping wall)"}',
              file=out)
        print(f'- with FS-R: {"DERIVED" if c1 else "!! still stuck"}',
              file=out)
        if c1:
            for step in c1:
                print(f'    {step}', file=out)
        ok &= law is not None and c0 is None and c1 is not None
        print(file=out)
        # the law-gap witness: 13.3-clean, semantically UNSAT
        gap = GSpec(name='lawgap-hand', atoms=(0, 1, 2),
                    pend=((0, 2), (1, 4), (2, 4)), exact=(0,),
                    gnand=((0, 2, 1, 1), (0, 2, 2, 1), (1, 3, 2, 3)))
        law_g = pg_law_infeasible(gap)
        br_g = late_branch_pinch(gap)
        fam = [family_probe(gap, m) for m in (1, 2, 3, 4, 5)]
        print('## the law-gap witness (pend a@2 exact, u@4, v@4; '
              'gnand(a,2,u,1),(a,2,v,1),(u,3,v,3))', file=out)
        print(f'- 13.3 calculus: {law_g} (expect None -- '
              f'fixpoint-clean)', file=out)
        print(f'- LATE-BRANCH-PINCH: {br_g}', file=out)
        print(f'- family m=1..5: {fam} (UNSAT by the hand proof; '
              f'family refusals corroborate)', file=out)
        ok &= law_g is None and br_g is not None and \
            all(v == 'REFUSED' for v in fam)
        print(file=out)
    if args.cmd in ('battery', 'sweep'):
        tot, survivors, fsr = sweep(out)
        ok &= tot['derived-fsr'] + tot['derived-base'] > 0
    if args.cmd in ('battery', 'control'):
        ok &= soundness_control(out)
    if args.cmd in ('battery', 'nested'):
        ok &= nested_hand(out)
    if args.cmd == 'battery':
        ok &= coverage_hand(out)
    if args.cmd == 'nested':
        sweep_ok, tiers, stuck = nested_sweep(out, want=args.want,
                                              tries=args.tries)
        ok &= sweep_ok
        ok &= nested_soundness(out)
    if args.cmd in ('crosspair', 'coverage'):
        ok &= crosspair_cmd(out)
    if args.cmd in ('cycle', 'coverage'):
        ok &= cycle_cmd(out)
    print(f'derivation {args.cmd}: {"OK" if ok else "PROBLEMS"}',
          file=out)
    if args.out:
        out.close()
        print(f'wrote {args.out}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
