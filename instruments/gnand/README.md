# instruments/gnand — the gnand instrument battery

The machine-evidence suite behind the book's *Partial Completeness*
chapter: the instruments that accompanied the completeness theorem for
gnand cores (hard deadlines under staggering) from conjecture to
proof, migrated here from the development record so that every number
in the chapter's evidence table regenerates from this directory.

These are **instruments, not checkers**: exploratory exact-arithmetic
search and verification tools that corroborate prose mathematics,
falsify conjectures, and emit witness models. Nothing here is part of
any trust story — the chapter's proofs are prose, its three added
axiom schemata carry machine-checked Lean soundness lemmas under
`lean/qtsl`, and this battery is the population-scale empirical
regime those proofs were developed against. Everything is
deterministic (fixed seeds, exact `Fraction`/integer arithmetic, no
floats), so regenerated receipts reproduce byte-for-byte.

## The evidence table, one command per row

The chapter's table (Section "Evidence and assurance status") maps to
`make` targets as follows; each writes its receipt into `receipts/`:

| chapter row | target | receipt | headline |
|---|---|---|---|
| derivation sweep | `derivation` | `derivation-battery.md` | 64,786 refuted cells (33,974 base + 30,812 residual-split), 0 underivable |
| cross-pair sweep | `coverage` | `derivation-coverage.md` | 13,542 descent configs, 0 gaps; 4,116/4,116 out-of-box cores derived; cycle mode 200/200 |
| branch engine | `branch` | `branch-engine.md` | 1,000/1,000 branch-refuted cores derived (991 doubly-pinched, 9 cycle), 0 stuck |
| model emitter | `emitter` | `model-emitter.md` | 122/122 named + 541/541 random feasible cores emit-verified |
| soundness controls | (inside each of the above) | same files | 0 false fires on every family-SAT control population |
| six-state witness | `independence` | `independence.md`, `independence-minimality-z3.md` | S₁ (6 states) validates the whole basis and refutes FS-R(2,3;1); no witness exists at ≤ 5 states (z3, both singleton and free-set atom classes); all 9 edges load-bearing |

`make witnesses` additionally re-adjudicates the two frontier
specimens of the development sweeps, **grand533** (UNSAT — the
box-saturated-pattern collapse certificate fires, and the winged
family corroborates by refusal) and **grand554** (clocked-SAT —
settled by the mechanized forcing wings). These two are the
spos-non-monotonicity witnesses: pruning states strengthens
worst-case service facts, which can *create* positive-graded pattern
instances, so lock-pruning against patterns with positive-graded
conjuncts would be unsound exactly here. They are the converse side
of the chapter's monotone-protection lemma — the reason its
negative-side scoping is tight rather than cautious.

`make support` runs the ground-truth tier's own batteries (the
oracles, the nonstandard-time layer, the core builder, the masked
family, the F-fragment sweep). `make all` runs everything;
`make check` regenerates every receipt into `out/` and diffs against
the committed `receipts/` — the reproduction gate.

Total wall time for `make all` is a few minutes on one modern core;
nothing here needs more than a laptop.

## The modules

- `oracle.py` — validity oracle for the deadline-free qualitative
  fragment (invariance + Streett obligations over finite behavioral
  graphs); exhaustive-plus-random countermodel search.
- `timed.py` — the clocked-model oracle: deadline operators evaluated
  exactly over finite clocked models (per-location dwell bounds,
  `Fraction` interval denotations).
- `nstime.py` — the nonstandard-time layer: the timed engine run over
  the lex-ordered plane ℚ + ℚ·ε, with the germ-transfer check that
  moves NSQ verdicts to standard clocked verdicts.
- `cores.py` — graded-box specification cores (`GSpec`: the gnand
  cores of the chapter, plus escape/lock extensions beyond the
  fragment) and the branch-at-seed model builder with its three-way
  refusal classifier.
- `masked.py` — the masked-branching witness: the 57-state
  deep-branching model showing per-trajectory certificates are
  unsound over the full clocked class.
- `family.py` — the masked-family builder (grid schedule trees with
  total branching), the winged extension (forced-shadow obligations),
  the effective-stage fixpoint calculus, and the frontier witnesses
  `grand533`/`grand554`.
- `derivation.py` — the derivation searcher: every calculus move
  mirrored as a proved-lemma derivation step, plus the nested
  (branch-conditional) engine, the cross-pair descent, and the cycle
  schema.
- `emitter.py` — the model emitter: the completeness proof's schedule
  trees (earliest-deadline-first spine + delayer wings) built
  explicitly per feasible core and verified by the exact pass and the
  clocked oracle.
- `fsweep.py` — the F-fragment small-model sweep: granularity
  separations (the disjointness-forced family, the anchor-pinch
  curfew specimen) that killed the small-model conjectures.
- `canon.py` — the elimination-prototype instrument for the
  deadline-free canonical construction (consumed by `fsweep.py`'s
  loose-seed probe).
- `independence.py` — the FS-R (residual-split first-service)
  independence battery: the six-state gadget S₁, full-basis
  validation (exhaustive FS₂/FS₃ + the tier-tournament lemma for all
  n), the edge-minimality mutant sweep, and the stretched-gadget
  negative probe.
- `independence_search_z3.py` — z3 rediscovery/nonexistence search
  for independence gadgets (requires `z3-solver`; every candidate is
  verified by `independence.py`'s exhaustive checker, so z3 is never
  trusted — UNSAT results are over a necessary first-order skeleton,
  sound for nonexistence).

Dependencies: python3 (stdlib + `Fraction`), `numpy` (one vectorized
exhaustive pass in `independence.py`), `z3-solver` (only for
`independence_search_z3.py`).

## Scope honesty

A refutation here is a machine-checked countermodel over the class
each instrument names; a silence is only as strong as the theorem
behind it (the receipts say which — battery rows cite their proof
status inline). The instruments deliberately cover more than the
chapter's fragment (escapes, locks, separation windows): the extra
surface is where the fragment boundary was *found*, and the
out-of-scope guards in the batteries keep it honest.
