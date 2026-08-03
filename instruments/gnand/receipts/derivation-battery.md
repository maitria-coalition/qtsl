# derivation -- the derivation-sweep instrument

## the hand candidate (pend a@2 exact, b@3, gnand(a,2,b,2))
- law: LATE-EFF(exact 0: eff 1 <= 1) (expect LATE-EFF on atom 0)
- base basis: no derivation (the telescoping wall)
- with FS-R: DERIVED
    FSR-TIGHTEN(0|1;c=1): C_1 dies (gnand(0, 2, 1, 2)[D1(2<=2),U4]), R dies (gnand(0, 2, 1, 2)[D1(1<=2),D1(2<=2)]); R6+D4+MONO: A_1[0]
    LATE: A_1[0]-D1->A_1 vs exactness ~A_1[0]: D

## the law-gap witness (pend a@2 exact, u@4, v@4; gnand(a,2,u,1),(a,2,v,1),(u,3,v,3))
- 13.3 calculus: None (expect None -- fixpoint-clean)
- LATE-BRANCH-PINCH: LATE-BRANCH(exact 0): pair (1, 3, 2, 3) doubly pinched (eff 4,4, L 1)
- family m=1..5: ['REFUSED', 'REFUSED', 'REFUSED', 'REFUSED', 'REFUSED'] (UNSAT by the hand proof; family refusals corroborate)

## sweep totals (exhaustive box n<=3 + random out-of-box tier: 4000 draws at n=3/4, s<=5, w<=4, p<=4; 2265 refuted)
- {'feasible': 88981, 'derived-base': 33974, 'derived-fsr': 30812, 'survivor': 0, 'branch-refuted': 1}
- refuted, by firing check: {'EFF-ZERO': 35183, 'LATE-EFF': 29603}
- check x derivation-tier: {('EFF-ZERO', 'derived-base'): 32829, ('EFF-ZERO', 'derived-fsr'): 2354, ('LATE-EFF', 'derived-base'): 1145, ('LATE-EFF', 'derived-fsr'): 28458}
- doc-vs-code calculus split on refuted cells: {'both': 62763, 'code-only': 2023, 'doc-only': 0} (doc-only should be 0: the code calculus subsumes the doc calculus); code-only cells by tier: {'derived-fsr': 2023}

## DERIVED-FSR specimens (fourth-correction witnesses)
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 2),)
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 2)[D1(1<=1),D1(1<=2)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 3),)
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 3)[U4,D1(2<=3)]), R dies (gnand(0, 1, 1, 3)[D1(1<=1),D1(1<=3)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 2))
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 3))
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 3)[U4,D1(2<=3)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 2), (0, 1, 1, 3))
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 2)[D1(1<=1),D1(1<=2)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 1, 3))
  law: LATE-EFF(exact 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    LATE: A_1[1]-D1->A_1 vs exactness ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 2),)
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 2)[D1(1<=1),D1(1<=2)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 3),)
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 3)[U4,D1(2<=3)]), R dies (gnand(0, 1, 1, 3)[D1(1<=1),D1(1<=3)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 1), (0, 1, 1, 2))
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 1), (0, 1, 1, 3))
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 3)[U4,D1(2<=3)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 2), (0, 1, 1, 3))
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 2)[D1(1<=1),D1(1<=2)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D
- pend=((0, 2), (1, 2)) exact=() avoid=((1, 1),) gnand=((0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 1, 3))
  law: LATE-EFF(avoid 1: eff 1 <= 1)
    FSR-TIGHTEN(1|0;c=1): C_0 dies (gnand(0, 1, 1, 2)[U4,D1(2<=2)]), R dies (gnand(0, 1, 1, 1)[D1(1<=1),D1(1<=1)]); R6+D4+MONO: A_1[1]
    AV: A_1[1]-D1->A_1 vs avoid ~A_1[1]: D

## survivors (neither mirror derives)

## LAW-GAP class: 13.3-feasible, LATE-BRANCH-PINCH refuted (T3-as-stated counterexample material)
- count: 1
- pend=((0, 5), (1, 5), (2, 3)) exact=(1,) avoid=((0, 2), (2, 2)) gnand=((1, 3, 0, 4), (1, 2, 2, 4), (0, 1, 2, 4))
  LATE-BRANCH(avoid 2): pair (1, 3, 0, 4) doubly pinched (eff 5,5, L 2)

## semantic re-check (winged family, fine grids)
- pend=((0, 5), (1, 5), (2, 3)) exact=(1,) avoid=((0, 2), (2, 2)) gnand=((1, 3, 0, 4), (1, 2, 2, 4), (0, 1, 2, 4)): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED, m=5:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 2),): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 3),): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 2)): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 3)): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 2), (0, 1, 1, 3)): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- pend=((0, 2), (1, 2)) exact=(1,) avoid=() gnand=((0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 1, 3)): m=1:REFUSED, m=2:REFUSED, m=3:REFUSED, m=4:REFUSED
- ALARMS (masked-SAT on law-infeasible): 0 (clean)

## soundness control (derive + branch-pinch silent on family-SAT cores)
- 260 family-SAT cores checked, 0 false fires (clean)

## nested hand cases
- lawgap-hand: nested
- lawgap-natural (random-tier find): nested

## coverage hand cases (descent + cycle schema)
- descent (E_a=6, E_b=4, W=2 -> nv=2; single-shot sticks at 3): certified bound 2
    FSR-TIGHTEN(c=3): C_b dies (gnand(0, 6, 1, 1)[D1(6<=6),U4]), R dies (gnand(0, 6, 1, 1)[D1(3<=6),D1(1<=1)]): E_a <- 3
    FSR-TIGHTEN(c=2): C_b dies (gnand(0, 6, 1, 1)[D1(3<=6),U4]), R dies (gnand(0, 1, 1, 2)[D1(1<=1),D1(2<=2)]): E_a <- 2
- coded mirror on the same pair: E_a = 2 (expect 2; derived-D: False)
- cycle specimen (dissected from the sweep): schema CYCLE-SCHEMA (expect CYCLE-SCHEMA); engine derived
    drop to X=[0, 1, 2, 3]; FS-R at c=L=2, E={0: 3, 1: 5, 2: 4, 3: 5}
      1-cell dies via prec ban (0, 3, 1, 2) (gnand(0, 3, 1, 2)[D1(3<=3),U4])
      2-cell dies via prec ban (0, 4, 2, 1) (gnand(0, 4, 2, 1)[D1(3<=4),U4])
      3-cell dies via prec ban (0, 3, 3, 2) (gnand(0, 3, 3, 2)[D1(3<=3),U4])
      residual subtree DEAD (cycle [1, 2, 3]; 3 positions checked)
      FORCES (15.4): A_2[0]; PC vs ~A_2[0] (exact): D

derivation battery: OK
