#!/usr/bin/env python3
"""Corpus generator for the ProbLog-family cross-implementation battery.

Expected verdicts are computed on python's Fraction arithmetic and its
own least-model loop — an independent transcription of the bracket
obligation semantics (a different language and exact-arithmetic stack
from the row-native evaluators, and a different codebase from the
exemplar's `problogcheck`):

  wf(prog)                 <=>  coin ids distinct, probs in [0,1],
                                facts reference declared coins,
                                dets + clause bodies strictly ascending
  derives(prog, world)     <=>  world canonical + declared, and the
                                query is in lfp(dets + world's facts)
  blocks(prog, cut)        <=>  cut canonical + declared, and the query
                                is NOT in lfp(dets + complement's facts)
  exact(prog, p)           <=>  p == sum of world masses where derives
  lower(prog, rows, lo)    <=>  every row derives, and lo ==
                                inclusion-exclusion over row UNIONS
  upper(prog, rows, hi)    <=>  every row blocks, and hi ==
                                min(1 - prod(1-p)) (empty: hi == 1)
  bonferroni(prog, rows, depth, lo)
                           <=>  every row derives, depth is EVEN, and
                                lo == the depth-limited
                                inclusion-exclusion prefix over row
                                UNIONS (Bonferroni: an even prefix
                                under-counts the union, hence a sound
                                lower bound; odd depths over-count and
                                are decided false)

All cases stay inside decided territory (coins <= 5, rows <= 4 —
except the bonferroni section, whose every fifth case carries 17-20
rows: past the full-IE relation's 16-row cap yet decided for the
truncated relation, the residue-4 point; measure-carrying cases only
on wf-clean programs); refusal behavior is battery territory, not
corpus territory. Deterministic: reseeded PRNG, frozen output; the
bonferroni generator runs LAST so the first 240 cases' bytes are
unchanged from the 6-relation corpus. Regenerate with
`python3 problog_pyref_gen.py > problog_pyref_corpus.json` only
alongside a deliberate corpus revision — replay disagreement is
stop-and-investigate, never adjust-the-corpus.
"""

import itertools
import json
import random
from fractions import Fraction

rng = random.Random(0x543)  # deterministic corpus

N_PER_RELATION = 40


# ---------------------------------------------------------------- model


def lfp(atoms, clauses):
    derived = set(atoms)
    changed = True
    while changed:
        changed = False
        for head, body in clauses:
            if head not in derived and all(b in derived for b in body):
                derived.add(head)
                changed = True
    return derived


def world_atoms(prog, true_coins):
    atoms = set(prog["dets"])
    for atom, coin in prog["facts"]:
        if coin in true_coins:
            atoms.add(atom)
    return atoms


def derives_in(prog, true_coins):
    return prog["query"] in lfp(world_atoms(prog, true_coins), prog["clauses"])


def coin_ids(prog):
    return [c[0] for c in prog["coins"]]


def probs(prog):
    return {c[0]: Fraction(c[1], c[2]) for c in prog["coins"]}


def is_canonical(xs):
    return all(a < b for a, b in zip(xs, xs[1:]))


def set_ok(prog, xs):
    declared = set(coin_ids(prog))
    return is_canonical(xs) and all(x in declared for x in xs)


def wf(prog):
    seen = set()
    for c in prog["coins"]:
        cid = c[0]
        if cid in seen:
            return False
        seen.add(cid)
        p = Fraction(c[1], c[2])
        if p < 0 or p > 1:
            return False
    if not is_canonical(prog["dets"]):
        return False
    for _, body in prog["clauses"]:
        if not is_canonical(body):
            return False
    for _, coin in prog["facts"]:
        if coin not in seen:
            return False
    return True


def exact_value(prog):
    ids = coin_ids(prog)
    pr = probs(prog)
    total = Fraction(0)
    for bits in itertools.product([False, True], repeat=len(ids)):
        true_coins = {c for c, on in zip(ids, bits) if on}
        mass = Fraction(1)
        for c, on in zip(ids, bits):
            mass *= pr[c] if on else 1 - pr[c]
        if derives_in(prog, true_coins):
            total += mass
    return total


def ie_value(prog, rows):
    pr = probs(prog)
    total = Fraction(0)
    k = len(rows)
    for mask in range(1, 1 << k):
        union = set()
        for i in range(k):
            if mask >> i & 1:
                union |= set(rows[i])
        term = Fraction(1)
        for c in union:
            term *= pr[c]
        total += term if bin(mask).count("1") % 2 == 1 else -term
    return total


def bonf_value(prog, rows, depth):
    """The depth-limited inclusion-exclusion prefix over row unions
    (same sign convention as ie_value: odd strata add, even strata
    subtract). depth >= len(rows) reproduces ie_value exactly."""
    pr = probs(prog)
    total = Fraction(0)
    k = len(rows)
    for j in range(1, min(depth, k) + 1):
        for subset in itertools.combinations(range(k), j):
            union = set()
            for i in subset:
                union |= set(rows[i])
            term = Fraction(1)
            for c in union:
                term *= pr[c]
            total += term if j % 2 == 1 else -term
    return total


def upper_value(prog, rows):
    pr = probs(prog)
    best = Fraction(1)
    for cut in rows:
        miss = Fraction(1)
        for c in cut:
            miss *= 1 - pr[c]
        best = min(best, 1 - miss)
    return best


# ------------------------------------------------------------ generator


def frac(x):
    return [x.numerator, x.denominator]


def rand_prob():
    d = rng.randint(1, 10)
    n = rng.randint(0, d)
    return Fraction(n, d)


def rand_prog():
    """A wf-clean random ground program. Atoms: coin facts get atoms
    0..n_coins-1 (atom i on coin i), dets and derived atoms above."""
    n_coins = rng.randint(1, 5)
    coins = [[i, *frac(rand_prob())] for i in range(n_coins)]
    n_dets = rng.randint(0, 3)
    dets = list(range(n_coins, n_coins + n_dets))
    facts = [[i, i] for i in range(n_coins)]
    n_atoms = n_coins + n_dets + rng.randint(1, 3)  # derived atoms above
    clauses = []
    for _ in range(rng.randint(1, 6)):
        head = rng.randint(n_coins + n_dets, n_atoms - 1)
        body_size = rng.randint(0, 3)
        body = sorted(rng.sample(range(n_atoms), min(body_size, n_atoms)))
        clauses.append([head, body])
    query = rng.randint(0, n_atoms - 1)
    return {
        "coins": coins,
        "dets": dets,
        "facts": facts,
        "clauses": clauses,
        "query": query,
    }


def rand_world(prog, allow_bad=False):
    ids = coin_ids(prog)
    world = sorted(rng.sample(ids, rng.randint(0, len(ids))))
    if allow_bad and world and rng.random() < 0.5:
        roll = rng.random()
        if roll < 0.5:
            world = list(reversed(world)) if len(world) > 1 else world + [99]
        else:
            world = world + [99]
    return world


def gen_wf(count):
    out = []
    for i in range(count):
        prog = rand_prog()
        if i % 3 == 1:
            # a designed P1 violation
            roll = rng.randrange(4)
            if roll == 0:
                prog["coins"].append([prog["coins"][0][0], 1, 2])
            elif roll == 1:
                prog["coins"][0][1:] = [7, 5]
            elif roll == 2:
                prog["facts"].append([0, 99])
            else:
                prog["clauses"].append([prog["query"], [1, 0]])
        out.append({"prog": prog, "verdict": wf(prog)})
    return out


def gen_derives(count):
    out = []
    for i in range(count):
        prog = rand_prog()
        world = rand_world(prog, allow_bad=(i % 4 == 3))
        verdict = set_ok(prog, world) and derives_in(prog, set(world))
        out.append({"prog": prog, "world": world, "verdict": verdict})
    return out


def gen_blocks(count):
    out = []
    for i in range(count):
        prog = rand_prog()
        cut = rand_world(prog, allow_bad=(i % 5 == 4))
        verdict = set_ok(prog, cut) and not derives_in(
            prog, set(coin_ids(prog)) - set(cut)
        )
        out.append({"prog": prog, "cut": cut, "verdict": verdict})
    return out


def gen_exact(count):
    out = []
    for i in range(count):
        prog = rand_prog()
        true_p = exact_value(prog)
        if i % 2 == 0:
            claim = true_p
        else:
            claim = true_p + Fraction(1, 7) if true_p <= Fraction(6, 7) else true_p / 2
        out.append(
            {"prog": prog, "p": frac(claim), "verdict": claim == true_p}
        )
    return out


def gen_lower(count):
    out = []
    made = 0
    while made < count:
        prog = rand_prog()
        ids = coin_ids(prog)
        deriving = [
            sorted(s)
            for r in range(len(ids) + 1)
            for s in itertools.combinations(ids, r)
            if derives_in(prog, set(s))
        ]
        if not deriving:
            continue
        rows = [list(rng.choice(deriving)) for _ in range(rng.randint(1, 3))]
        mode = made % 3
        if mode == 1 and len(ids) >= 1:
            # possibly-fake row: verdict recomputed below either way
            rows.append(rand_world(prog))
        true_lo = ie_value(prog, rows)
        claim = true_lo
        if mode == 2:
            claim = true_lo + Fraction(1, 11)
        all_derive = all(
            set_ok(prog, r) and derives_in(prog, set(r)) for r in rows
        )
        verdict = all_derive and claim == true_lo
        out.append(
            {"prog": prog, "rows": rows, "lo": frac(claim), "verdict": verdict}
        )
        made += 1
    return out


def gen_upper(count):
    out = []
    made = 0
    while made < count:
        prog = rand_prog()
        ids = coin_ids(prog)
        blocking = [
            sorted(s)
            for r in range(len(ids) + 1)
            for s in itertools.combinations(ids, r)
            if not derives_in(prog, set(ids) - set(s))
        ]
        mode = made % 4
        if mode == 0:
            rows = []
            claim = Fraction(1)
        elif not blocking:
            continue
        else:
            rows = [list(rng.choice(blocking)) for _ in range(rng.randint(1, 3))]
            if mode == 2:
                rows.append(rand_world(prog))  # possibly non-blocking
            claim = upper_value(prog, rows)
            if mode == 3:
                claim = claim / 2 if claim > 0 else Fraction(1, 3)
        all_block = all(
            set_ok(prog, r)
            and not derives_in(prog, set(ids) - set(r))
            for r in rows
        )
        verdict = all_block and claim == upper_value(prog, rows)
        out.append(
            {"prog": prog, "rows": rows, "hi": frac(claim), "verdict": verdict}
        )
        made += 1
    return out


def gen_bonferroni(count):
    """Residue 4: truncated lower bounds. Modes cycle through the
    designed loci — 0: honest small case; 1: ODD depth (decided false,
    the over-counting prefix); 2: a possibly-fake / possibly-bad extra
    row; 3: value tamper; 4: 17-20 rows — past the full-IE relation's
    cap, decided HERE (the residue's whole point). Runs last so the
    6-relation sections' PRNG draws (hence bytes) stay frozen."""
    out = []
    made = 0
    while made < count:
        prog = rand_prog()
        ids = coin_ids(prog)
        deriving = [
            sorted(s)
            for r in range(len(ids) + 1)
            for s in itertools.combinations(ids, r)
            if derives_in(prog, set(s))
        ]
        if not deriving:
            continue
        mode = made % 5
        k = rng.randint(17, 20) if mode == 4 else rng.randint(1, 4)
        rows = [list(rng.choice(deriving)) for _ in range(k)]
        depth = rng.choice([1, 3]) if mode == 1 else rng.choice([0, 2, 2, 4])
        if mode == 2:
            rows.append(rand_world(prog, allow_bad=True))
        # Row validation precedes the prefix (provider order): with a
        # non-canonical or undeclared row the verdict is false whatever
        # lo says, and the prefix over undeclared coins is undefined.
        rows_ok = all(set_ok(prog, r) for r in rows)
        true_lo = bonf_value(prog, rows, depth) if rows_ok else Fraction(0)
        claim = true_lo + Fraction(1, 13) if mode == 3 else true_lo
        all_derive = rows_ok and all(derives_in(prog, set(r)) for r in rows)
        verdict = depth % 2 == 0 and all_derive and claim == true_lo
        out.append(
            {
                "prog": prog,
                "rows": rows,
                "depth": depth,
                "lo": frac(claim),
                "verdict": verdict,
            }
        )
        made += 1
    return out




# --------------------------------------------- msw switch domains (residue 5)
#
# Coins may carry a 4th element: the switch domain. Coins sharing a
# domain are the mutually exclusive outcomes of one Sato-style
# multi-valued switch (exactly one true per world; probabilities sum
# to exactly 1). The model functions below are the python arm's
# independent transcription of the residue-5 semantics: world
# enumeration draws one outcome per switch; a world/explanation row
# naming two outcomes of one switch is decided false; an
# inclusion-exclusion union term naming two outcomes of one switch is
# an impossible joint event (0); the cut bound groups by domain.
# The msw generators run LAST so every earlier section's PRNG draws
# (hence bytes) stay frozen.


def coin_doms(prog):
    return {c[0]: c[3] for c in prog["coins"] if len(c) > 3}


def has_clash(prog, xs):
    doms = coin_doms(prog)
    hit = [doms[c] for c in xs if c in doms]
    return len(hit) != len(set(hit))


def wf_msw(prog):
    if not wf(prog):
        return False
    sums = {}
    for c in prog["coins"]:
        if len(c) > 3:
            sums[c[3]] = sums.get(c[3], Fraction(0)) + Fraction(c[1], c[2])
    return all(s == 1 for s in sums.values())


def world_ok_msw(prog, xs):
    return set_ok(prog, xs) and not has_clash(prog, xs)


def exact_value_msw(prog):
    doms = coin_doms(prog)
    pr = probs(prog)
    switches = {}
    free = []
    for c in coin_ids(prog):
        if c in doms:
            switches.setdefault(doms[c], []).append(c)
        else:
            free.append(c)
    axes = [[(None, 1 - pr[c]), (c, pr[c])] for c in free] + [
        [(c, pr[c]) for c in outs] for outs in switches.values()
    ]
    total = Fraction(0)
    for picks in itertools.product(*axes):
        true_coins = {c for c, _ in picks if c is not None}
        mass = Fraction(1)
        for _, m in picks:
            mass *= m
        if derives_in(prog, true_coins):
            total += mass
    return total


def ie_value_msw(prog, rows):
    pr = probs(prog)
    total = Fraction(0)
    k = len(rows)
    for mask in range(1, 1 << k):
        union = set()
        for i in range(k):
            if mask >> i & 1:
                union |= set(rows[i])
        if has_clash(prog, union):
            term = Fraction(0)
        else:
            term = Fraction(1)
            for c in union:
                term *= pr[c]
        total += term if bin(mask).count("1") % 2 == 1 else -term
    return total


def upper_value_msw(prog, rows):
    doms = coin_doms(prog)
    pr = probs(prog)
    best = Fraction(1)
    for cut in rows:
        groups = {}
        miss = Fraction(1)
        for c in cut:
            if c in doms:
                groups[doms[c]] = groups.get(doms[c], Fraction(0)) + pr[c]
            else:
                miss *= 1 - pr[c]
        for s in groups.values():
            miss *= 1 - s
        best = min(best, 1 - miss)
    return best


def rand_partition(k):
    """k exact probabilities summing to 1."""
    ws = [rng.randint(1, 5) for _ in range(k)]
    t = sum(ws)
    return [Fraction(w, t) for w in ws]


def rand_msw_prog():
    """A wf-clean random ground msw program: 1-2 switches of 2-3
    outcomes plus 0-2 free coins; atom i on coin i, derived atoms
    above."""
    coins = []
    cid = 0
    for dom in range(rng.randint(1, 2)):
        k = rng.randint(2, 3)
        for pp in rand_partition(k):
            coins.append([cid, pp.numerator, pp.denominator, dom])
            cid += 1
    for _ in range(rng.randint(0, 2)):
        pp = rand_prob()
        coins.append([cid, pp.numerator, pp.denominator])
        cid += 1
    n_coins = cid
    n_dets = rng.randint(0, 2)
    dets = list(range(n_coins, n_coins + n_dets))
    facts = [[i, i] for i in range(n_coins)]
    n_atoms = n_coins + n_dets + rng.randint(1, 3)
    clauses = []
    for _ in range(rng.randint(1, 6)):
        head = rng.randint(n_coins + n_dets, n_atoms - 1)
        body_size = rng.randint(0, 3)
        body = sorted(rng.sample(range(n_atoms), min(body_size, n_atoms)))
        clauses.append([head, body])
    query = rng.randint(0, n_atoms - 1)
    return {
        "coins": coins,
        "dets": dets,
        "facts": facts,
        "clauses": clauses,
        "query": query,
    }


def first_switch_pair(prog):
    doms = coin_doms(prog)
    by_dom = {}
    for c, dm in doms.items():
        by_dom.setdefault(dm, []).append(c)
    return sorted(next(v for v in by_dom.values() if len(v) >= 2))[:2]


def force_disjunction(prog):
    """Append a fresh atom derivable from either of two outcomes of
    one switch, and point the query at it. On this shape the
    independent-Bernoulli and msw semantics provably differ: exclusive
    events add (p_a + p_b), the independence arithmetic subtracts a
    phantom overlap (p_a * p_b > 0 — partition weights are positive).
    Returns the two outcome coins."""
    a, b = first_switch_pair(prog)
    atoms = {prog["query"]}
    atoms.update(prog["dets"])
    atoms.update(x for x, _ in prog["facts"])
    for h, body in prog["clauses"]:
        atoms.add(h)
        atoms.update(body)
    fresh = max(atoms) + 1
    prog["clauses"].append([fresh, [a]])
    prog["clauses"].append([fresh, [b]])
    prog["query"] = fresh
    return a, b


def gen_msw_wf(count):
    out = []
    for i in range(count):
        prog = rand_msw_prog()
        if i % 3 == 1:
            # the designed residue-5 P1 violation: a domain sum != 1
            victim = next(c for c in prog["coins"] if len(c) > 3)
            victim[1], victim[2] = victim[1] + victim[2], victim[2]
        out.append({"prog": prog, "verdict": wf_msw(prog)})
    return out


def gen_msw_derives(count):
    out = []
    for i in range(count):
        prog = rand_msw_prog()
        world = rand_world(prog, allow_bad=(i % 4 == 3))
        # every third case forces a same-switch clash pair
        if i % 3 == 2:
            doms = coin_doms(prog)
            by_dom = {}
            for c, dm in doms.items():
                by_dom.setdefault(dm, []).append(c)
            pair = next(v for v in by_dom.values() if len(v) >= 2)
            world = sorted(set(world) | set(pair[:2]))
        verdict = world_ok_msw(prog, world) and derives_in(prog, set(world))
        out.append({"prog": prog, "world": world, "verdict": verdict})
    return out


def gen_msw_exact(count):
    out = []
    for i in range(count):
        prog = rand_msw_prog()
        true_p = exact_value_msw(prog)
        if i % 3 == 0:
            claim = true_p
        elif i % 3 == 1:
            # the residue boundary, FORCED to bite: a same-switch
            # disjunction query, claimed at the independent-Bernoulli
            # value (which subtracts a phantom overlap term).
            force_disjunction(prog)
            true_p = exact_value_msw(prog)
            claim = exact_value(prog)
        else:
            claim = true_p + Fraction(1, 7) if true_p <= Fraction(6, 7) else true_p / 2
        out.append({"prog": prog, "p": frac(claim), "verdict": claim == true_p})
    return out


def gen_msw_lower(count):
    out = []
    made = 0
    while made < count:
        prog = rand_msw_prog()
        ids = coin_ids(prog)
        deriving = [
            sorted(s)
            for r in range(min(len(ids), 4) + 1)
            for s in itertools.combinations(ids, r)
            if not has_clash(prog, s) and derives_in(prog, set(s))
        ]
        if not deriving:
            continue
        rows = [list(rng.choice(deriving)) for _ in range(rng.randint(1, 3))]
        mode = made % 4
        if mode == 1:
            # a clash row: decided false at the row obligation
            doms = coin_doms(prog)
            by_dom = {}
            for c, dm in doms.items():
                by_dom.setdefault(dm, []).append(c)
            pair = next(v for v in by_dom.values() if len(v) >= 2)
            rows.append(sorted(pair[:2]))
        if mode == 2:
            # the residue boundary, FORCED to bite: two single-outcome
            # rows of one switch — exclusive events add, and the
            # independence arithmetic subtracts a phantom overlap.
            a, b = force_disjunction(prog)
            rows = [[a], [b]]
        true_lo = ie_value_msw(prog, rows)
        claim = true_lo
        if mode == 2:
            claim = ie_value(prog, rows)
        elif mode == 3:
            claim = true_lo + Fraction(1, 11)
        rows_ok = all(
            world_ok_msw(prog, r) and derives_in(prog, set(r)) for r in rows
        )
        verdict = rows_ok and claim == true_lo
        out.append({"prog": prog, "rows": rows, "lo": frac(claim), "verdict": verdict})
        made += 1
    return out


def gen_msw_upper(count):
    out = []
    made = 0
    while made < count:
        prog = rand_msw_prog()
        ids = coin_ids(prog)
        # cuts MAY clash (a cut denotes a disjunction) - sample any set
        blocking = [
            sorted(s)
            for r in range(min(len(ids), 4) + 1)
            for s in itertools.combinations(ids, r)
            if not derives_in(prog, set(ids) - set(s))
        ]
        mode = made % 4
        if mode == 0:
            rows = []
            claim = Fraction(1)
        elif not blocking:
            continue
        else:
            rows = [list(rng.choice(blocking)) for _ in range(rng.randint(1, 3))]
            if mode == 2:
                # the residue boundary, FORCED to bite: the cut is the
                # same-switch pair behind a forced disjunction query —
                # a legitimate cut whose grouped bound (1 - (1 - p_a -
                # p_b) = p_a + p_b) differs from the independent-coin
                # formula by the phantom overlap.
                a, b = force_disjunction(prog)
                rows = [[a, b]]
            claim = upper_value_msw(prog, rows)
            if mode == 2:
                claim = upper_value(prog, rows)
            elif mode == 3:
                claim = claim / 2 if claim > 0 else Fraction(1, 3)
        all_block = all(
            set_ok(prog, r) and not derives_in(prog, set(ids) - set(r))
            for r in rows
        )
        verdict = all_block and claim == upper_value_msw(prog, rows)
        out.append({"prog": prog, "rows": rows, "hi": frac(claim), "verdict": verdict})
        made += 1
    return out


def main():
    corpus = {
        "engine": "python Fraction arithmetic + own least-model loop "
        "(independent transcription of the bracket obligation semantics)",
        "generator": "problog_pyref_gen.py (seed 0x543)",
        "wf": gen_wf(N_PER_RELATION),
        "derives": gen_derives(N_PER_RELATION),
        "blocks": gen_blocks(N_PER_RELATION),
        "exact": gen_exact(N_PER_RELATION),
        "lower": gen_lower(N_PER_RELATION),
        "upper": gen_upper(N_PER_RELATION),
        # LAST: preserves the 6-relation sections' PRNG stream.
        "bonferroni": gen_bonferroni(N_PER_RELATION),
        # LAST AGAIN (residue 5): the msw sections run after every
        # frozen section, preserving their PRNG draws byte for byte.
        "msw_wf": gen_msw_wf(N_PER_RELATION),
        "msw_derives": gen_msw_derives(N_PER_RELATION),
        "msw_exact": gen_msw_exact(N_PER_RELATION),
        "msw_lower": gen_msw_lower(N_PER_RELATION),
        "msw_upper": gen_msw_upper(N_PER_RELATION),
    }
    print(json.dumps(corpus, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
