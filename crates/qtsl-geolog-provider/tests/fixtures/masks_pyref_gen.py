#!/usr/bin/env python3
"""Corpus generator for the mask-family cross-implementation battery.

Expected verdicts are computed on python's set algebra — an independent
transcription of the mask relations' specs (a different language and a
different set representation from the row-native evaluators):

  same_members(n, s1, s2)        <=>  set(s1) == set(s2)
  face_minus(n, s, sface, v0)    <=>  set(sface) == set(s) - {v0}
  intersection(n, s1, s2, sint)  <=>  set(sint) == set(s1) & set(s2)

All cases stay inside the spec model's representable states (every
vertex < n, one complex per case); refusal behavior is battery
territory, not corpus territory. Deterministic: reseeded PRNG, frozen
output. Regenerate with `python3 masks_pyref_gen.py > masks_pyref_corpus.json`
only alongside a deliberate corpus revision — replay disagreement is
stop-and-investigate, never adjust-the-corpus.
"""

import json
import random

rng = random.Random(0x5136)  # deterministic corpus


def rand_mask(n, allow_empty=True):
    k = rng.randint(0 if allow_empty else 1, n)
    return sorted(rng.sample(range(n), k))


def perturb(mask, n):
    """One random single-vertex edit (add or drop). With n >= 1 an edit
    always changes the set; verdicts are recomputed from the sets
    below regardless, never assumed from which branch generated them."""
    s = set(mask)
    if s and (rng.random() < 0.5 or len(s) == n):
        s.discard(rng.choice(sorted(s)))
    else:
        candidates = [v for v in range(n) if v not in s]
        if candidates:
            s.add(rng.choice(candidates))
    return sorted(s)


def gen_same_members(count):
    out = []
    for i in range(count):
        n = rng.randint(1, 9)
        s1 = rand_mask(n)
        if i % 2 == 0:
            s2 = list(s1)
            rng.shuffle(s2)  # emission order is immaterial
        else:
            s2 = perturb(s1, n)
        out.append(
            {
                "n": n,
                "s1": s1,
                "s2": sorted(s2),
                "verdict": set(s1) == set(s2),
            }
        )
    return out


def gen_face_minus(count):
    out = []
    for i in range(count):
        n = rng.randint(1, 9)
        s = rand_mask(n, allow_empty=False)
        v0 = rng.randrange(n)
        if i % 2 == 0:
            sface = sorted(set(s) - {v0})
        else:
            sface = perturb(sorted(set(s) - {v0}), n)
        out.append(
            {
                "n": n,
                "s": s,
                "sface": sface,
                "v0": v0,
                "verdict": set(sface) == set(s) - {v0},
            }
        )
    return out


def gen_intersection(count):
    out = []
    for i in range(count):
        n = rng.randint(1, 9)
        s1 = rand_mask(n)
        s2 = rand_mask(n)
        if i % 2 == 0:
            sint = sorted(set(s1) & set(s2))
        else:
            sint = perturb(sorted(set(s1) & set(s2)), n)
        out.append(
            {
                "n": n,
                "s1": s1,
                "s2": s2,
                "sint": sint,
                "verdict": set(sint) == set(s1) & set(s2),
            }
        )
    return out


corpus = {
    "generator": "tests/fixtures/masks_pyref_gen.py (seed 0x5136)",
    "engine": "python set algebra (independent transcription of the mask specs)",
    "same_members": gen_same_members(80),
    "face_minus": gen_face_minus(80),
    "intersection": gen_intersection(80),
}

print(json.dumps(corpus, indent=1, sort_keys=True))
