# emitter -- the model emitter (schedule trees)

## hand controls
- wall-hand extended-check: LATE-EFF(exact 0: eff 1 <= 1) (must fire)
- lawgap-hand extended-check: LATE-BRANCH(exact 0): pair (1, 3, 2, 3) doubly pinched (eff 4,4, L 1) (must fire -- the T3-as-stated refuter, caught by the branch check)
- m2-refute (three stage-1 pends: law-feasible, m=2 dead): EMIT-VERIFIED (0 wings, 5 states) | family at n+1: MASKED-SAT -- three stage-1 pends; m0 = 4 = n + 1
- chain3: EMIT-VERIFIED (5 wings, 22 states) | family at n+1: MASKED-SAT -- a tighten chain; prec spine order load-bearing
- exact-pair: EMIT-VERIFIED (2 wings, 15 states) | family at n+1: MASKED-SAT -- exact root with a gnand partner: seed wing + demand wings
- avoid-pair: EMIT-VERIFIED (2 wings, 18 states) | family at n+1: MASKED-SAT -- avoid root: the (c) case

## the family-SAT population (seed replay)
- population replay: 122 family-SAT cores (banked receipts: 122)
- emitter verdicts at m = n + 1: {'EMIT-VERIFIED': 122}

## the extended-completeness hunt (800 fresh randoms, seed 485018)
- classification: {'screened': 195, 'law-refuted': 64, 'branch-refuted': 0, 'feasible': 541}
- emitter verdicts on the feasible tier: {'EMIT-VERIFIED': 541}
- T3+ alarms (extended-feasible, family-refused at n+1): 0 (NONE: the empirical face of 14.6 at this scale)
- branch-refuted specimens banked for the derivation sweep: 0 of 0

t3_emitter all: OK
