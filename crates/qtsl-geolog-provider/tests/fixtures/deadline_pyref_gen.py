#!/usr/bin/env python3
"""Frozen cross-implementation corpus generator for `qtsl_deadline_table`.

An INDEPENDENT python transcription of the deadline-table walk's WF/B/S/C
obligations (Fraction arithmetic throughout, written against the
certified-gym exact-lane checker's doc-comment spec, not against the
rust code): random small kernel/policy/table instances — exact
backward-induction tables plus adversarial perturbations — each case's
verdict DERIVED by running this checker, never asserted from knowledge
of the mutation. The rust battery replays every case through the pure
obligation core (`check_deadline`) and demands verdict agreement.

Deliberate representation differences from the rust arm (decorrelated
errors are the differential's power): dense dict kernels keyed by
(s, a) with per-destination Fraction lists; the table a dict keyed by
(t, s) rather than a flat list; obligations checked in a different
order (C's mixture first, WF last) — order must not matter, since the
verdict is a conjunction.

Regenerate with:  python3 deadline_pyref_gen.py > deadline_pyref_corpus.json
"""

import json
import random
from fractions import Fraction as F


def check(ns, deadline, goal, absorbing, kernel, policy, init, claim, table):
    """The obligations, independently transcribed. `table` is a dict
    (t, s) -> Fraction; kernel is (s, a) -> list[(d, Fraction)]
    (already reward-merged — the corpus is at the obligation grain);
    policy is (s, t) -> a; init is list[(s, Fraction)]."""
    want = (deadline + 1) * ns
    if len(table) != want:
        return False
    # (C) part 2: the claim against the init mixture, checked FIRST
    # (order independence is part of the differential).
    mix = sum((m * table[(0, s)] for s, m in init), F(0))
    if claim > mix:
        return False
    # entries in [0, 1]
    for (t, s), v in table.items():
        if v < 0 or v > 1:
            return False
    # (B)
    for s in range(ns):
        ind = F(1) if s in goal else F(0)
        if table[(deadline, s)] > ind:
            return False
    # (S)
    for t in range(deadline):
        for s in range(ns):
            if s in goal:
                continue
            if s in absorbing:
                if table[(t, s)] > table[(t + 1, s)]:
                    return False
                continue
            if (s, t) not in policy:
                return False
            a = policy[(s, t)]
            if (s, a) not in kernel:
                return False
            exp = sum((p * table[(t + 1, d)] for d, p in kernel[(s, a)]), F(0))
            if table[(t, s)] > exp:
                return False
    # (WF) groups and init masses, checked LAST.
    for (s, a), grp in kernel.items():
        tot = F(0)
        for d, p in grp:
            if p <= 0 or p > 1:
                return False
            tot += p
        if tot != 1:
            return False
    tot = F(0)
    for s, m in init:
        if m <= 0 or m > 1:
            return False
        tot += m
    return tot == 1


def rand_kernel(rng, ns, na, absorbing):
    """Every (non-absorbing s, a) gets a group with 1-3 destinations,
    denominators drawn small; probabilities sum to exactly 1."""
    kernel = {}
    for s in range(ns):
        if s in absorbing:
            continue
        for a in range(na):
            k = rng.randint(1, min(3, ns))
            dests = rng.sample(range(ns), k)
            den = rng.choice([c for c in [2, 3, 4, 6, 8, 12] if c >= k])
            cuts = sorted(rng.sample(range(1, den), k - 1)) if k > 1 else []
            weights = []
            prev = 0
            for c in cuts + [den]:
                weights.append(F(c - prev, den))
                prev = c
            kernel[(s, a)] = list(zip(dests, weights))
    return kernel


def backward_table(ns, deadline, goal, absorbing, kernel, policy):
    """The exact backward induction (V_t(s) = P[hit goal by T | X_t=s]
    under the policy) — a valid table by construction."""
    table = {}
    for s in range(ns):
        table[(deadline, s)] = F(1) if s in goal else F(0)
    for t in range(deadline - 1, -1, -1):
        for s in range(ns):
            if s in goal:
                table[(t, s)] = F(1)
            elif s in absorbing:
                table[(t, s)] = table[(t + 1, s)]
            else:
                a = policy[(s, t)]
                table[(t, s)] = sum(
                    (p * table[(t + 1, d)] for d, p in kernel[(s, a)]), F(0)
                )
    return table


def fr(x):
    return [x.numerator, x.denominator]


def main():
    rng = random.Random(0x515B4)
    cases = []
    while len(cases) < 240:
        ns = rng.randint(2, 6)
        na = rng.randint(1, 3)
        deadline = rng.randint(1, 5)
        goal = {rng.randrange(ns)}
        if rng.random() < 0.3 and ns > 2:
            goal.add(rng.randrange(ns))
        absorbing = set(goal) if rng.random() < 0.8 else set()
        if rng.random() < 0.5 and ns > len(goal) + 1:
            hole = rng.choice([s for s in range(ns) if s not in goal])
            absorbing.add(hole)
        kernel = rand_kernel(rng, ns, na, absorbing)
        policy = {
            (s, t): rng.randrange(na)
            for s in range(ns)
            if s not in absorbing
            for t in range(deadline)
        }
        table = backward_table(ns, deadline, goal, absorbing, kernel, policy)
        init_states = rng.sample(range(ns), rng.randint(1, min(2, ns)))
        if len(init_states) == 1:
            init = [(init_states[0], F(1))]
        else:
            init = [(init_states[0], F(1, 3)), (init_states[1], F(2, 3))]
        mix = sum((m * table[(0, s)] for s, m in init), F(0))
        claim = mix  # tight by construction
        # Mutations, applied blindly; the verdict comes from check().
        mode = rng.randrange(6)
        if mode == 1 and table:
            t = rng.randrange(deadline + 1)
            s = rng.randrange(ns)
            table[(t, s)] = table[(t, s)] + F(1, rng.choice([2, 3, 5, 7]))
        elif mode == 2:
            claim = claim + F(1, rng.choice([7, 11, 13]))
        elif mode == 3 and kernel:
            key = rng.choice(sorted(kernel))
            d0, p0 = kernel[key][0]
            kernel[key] = [(d0, p0 + F(1, 24))] + kernel[key][1:]
        elif mode == 4 and policy:
            del policy[rng.choice(sorted(policy))]
        elif mode == 5 and len(init) == 2:
            init = [(init[0][0], init[0][1])]  # masses no longer sum to 1
        verdict = check(ns, deadline, goal, absorbing, kernel, policy, init, claim, table)
        cases.append(
            {
                "ns": ns,
                "deadline": deadline,
                "goal": sorted(goal),
                "absorbing": sorted(absorbing),
                "kernel": [
                    [s, a, [[d, fr(p)] for d, p in grp]]
                    for (s, a), grp in sorted(kernel.items())
                ],
                "policy": [[s, t, a] for (s, t), a in sorted(policy.items())],
                "init": [[s, fr(m)] for s, m in init],
                "claim": fr(claim),
                "table": [
                    fr(table[(t, s)])
                    for t in range(deadline + 1)
                    for s in range(ns)
                    if (t, s) in table
                ],
                "table_complete": len(table) == (deadline + 1) * ns,
                "verdict": verdict,
            }
        )
    holds = sum(1 for c in cases if c["verdict"])
    out = {
        "generator": "deadline_pyref_gen.py (seed 0x515B4)",
        "note": (
            "independent python Fractions arm of the qtsl_deadline_table "
            "obligation core; verdicts derived by the python checker"
        ),
        "holds": holds,
        "fails": len(cases) - holds,
        "cases": cases,
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
