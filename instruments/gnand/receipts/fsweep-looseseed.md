# the loose-seed probe (schedulable-type prelude)

Armed expectation: every satisfiable unit seed is LOOSELY satisfiable (blockers `~AF<=(s-1/N)[psi]` co-satisfiable, one per pending base). A TIGHT-FORCING hit would be the fourth-correction signal and exits 1. Verdicts are search-bounded evidence, not certificates; the proof-side status lives in the development record.

## designed specimens (explicit witnesses where the family is understood; search elsewhere)
- S_2 antecedent: LOOSE by explicit witness (n = 5, seed (0, 0), residual profile [a0: 1, a1: 1] -- machine-checked)
- S_3 antecedent: LOOSE by explicit witness (n = 10, seed (0, 0), residual profile [a0: 1, a1: 1, a2: 1] -- machine-checked)
- curfew Phi (m6 witness): LOOSE by explicit witness (n = 5, seed (0, 0), residual profile [b1: 1, b2: 1] -- machine-checked)
- modal-base cascade: LOOSE (seed found at gran 2, residual profile [theta=a&AF1[b]: 1, b: 1]; loose witness at gran 2, n = 6, profile [theta=a&AF1[b]: 1, b: 2])
- adv1 row-composed: LOOSE (seed found at gran 2, residual profile [a: 1, b: 1]; loose witness at gran 2, n = 6, profile [a: 1, b: 2])
- adv2 seed-true row: LOOSE (seed found at gran 2, residual profile [a: 1, b: 1]; loose witness at gran 2, n = 5, profile [a: 1, b: 1])
- adv3 almost-service: LOOSE (seed found at gran 2, residual profile [theta=a&AF1[b]: 1, b: 2]; loose witness at gran 2, n = 3, profile [theta=a&AF1[b]: 1, b: 2])

## random unit tier (12 seeds)
- rand0: LOOSE (seed found at gran 2, residual profile [a1: 1, a0: 1]; loose witness at gran 2, n = 4, profile [a1: 1, a0: 2])
- rand1: seed formula NOT satisfied in bounds (grans [3, 6], n<=5) -- vacuous for E2, skipped
- rand2: LOOSE (seed found at gran 3, residual profile [a2: 1/3, a1: 1/3, a0: 1/3]; loose witness at gran 3, n = 3, profile [a2: 1, a1: 1, a0: 1])
- rand3: LOOSE by canon construction after random-tier miss (canonical model n = 1056, seed loc 780, clock 0; seed profile was [a2: 1, a0: 1, a1: 1]) -- the documented lesson again: random tiers miss structured witnesses; the canonical model IS the structured witness
- rand4: LOOSE (seed found at gran 3, residual profile [a0: 1, a1: 1, a2: 1]; loose witness at gran 3, n = 5, profile [a0: 1, a1: 1, a2: 1])
- rand5: LOOSE by canon construction after random-tier miss (canonical model n = 690, seed loc 444, clock 0; seed profile was [a2: 1, a1: 1, a0: 1]) -- the documented lesson again: random tiers miss structured witnesses; the canonical model IS the structured witness
- rand6: LOOSE (seed found at gran 2, residual profile [a0: 2, a2: 2]; loose witness at gran 2, n = 4, profile [a0: 2, a2: 2])
- rand7: LOOSE (seed found at gran 2, residual profile [a2: 1, a1: 1]; loose witness at gran 2, n = 6, profile [a2: 2, a1: 1])
- rand8: LOOSE (seed found at gran 3, residual profile [a2: 2, a1: 2, a0: 2]; loose witness at gran 3, n = 5, profile [a2: 2, a1: 2, a0: 2])
- rand9: LOOSE (seed found at gran 3, residual profile [a1: 1/3, a0: 1/3, a2: 1/3]; loose witness at gran 3, n = 5, profile [a1: 1, a0: 1, a2: 1])
- rand10: LOOSE by canon construction after random-tier miss (canonical model n = 648, seed loc 444, clock 0; seed profile was [a1: 2/3, a0: 1, a2: 2/3]) -- the documented lesson again: random tiers miss structured witnesses; the canonical model IS the structured witness
- rand11: LOOSE by canon construction after random-tier miss (canonical model n = 53, seed loc 19, clock 0; seed profile was [a1: 1, a2: 1/2]) -- the documented lesson again: random tiers miss structured witnesses; the canonical model IS the structured witness

- random tier: 11 loose, 0 tight-candidates, 1 unsat-in-bounds

looseseed overall: PASS (0 tight-forcing candidate(s))
