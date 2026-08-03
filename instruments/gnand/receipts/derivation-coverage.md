# derivation -- the derivation-sweep instrument

## cross-pair descent: abstract configuration sweep (E_a,E_b,D1,D2' in 1..8; D1',D2 in 1..3; ban E_a <= D1)
- 13542 configs with a strict cross-pair tighten; 5438 ITERATIVE-class (single-shot stuck above nv -- 14.2's open residual case, nonempty and covered), 9408 land D outright; gaps: 0

## concrete code-only cores (doc-silent, code-fires; stages 3..8, windows to 8 -- out-of-box)
- code-only refuted cores: 4116; derived 4116/4116; family corroboration 25 sampled, 0 alarms; family-SAT silence control 40 checked, 0 false fires

## cycle-mode schema sweep (targeted generator, seed 485019): 200 distinct cycle-refuted cores from 234 draws
- schema tiers: {'CYCLE-SCHEMA': 200, 'MIRROR-ENDGAME': 0, 'FAIL': 0}; engine: {'derived': 200, 'stuck': 0}
- family corroboration: 16 specimens, 0 alarms (clean)
- broken-cycle control: 17 family-SAT variants, 0 false fires (clean)

derivation coverage: OK
