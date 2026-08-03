# family: the masked-family tier

## family: the masked-family builder (the hand-built witness generalized to a mechanical tier)
- pigeon-3: MASKED-SAT (plain grid m=4; n=57) -- the hand-built witness, now emitted by the general family
  masking signature at seed (debut > window, all three atoms): confirmed
- pigeon-3/burst[0]: MASKED-SAT (plain grid m=4; n=32) -- singleton burst [0]; branch-at-seed cert: GB-PIGEON
- pigeon-3/burst[1]: MASKED-SAT (plain grid m=4; n=32) -- singleton burst [1]; branch-at-seed cert: GB-PIGEON
- pigeon-3/burst[2]: MASKED-SAT (plain grid m=4; n=32) -- singleton burst [2]; branch-at-seed cert: GB-PIGEON
- pigeon-3/burst[0, 1]: FAMILY-REFUSED (seed state hard-illegal (forced box violation or EDF-dead at time 0); n=0) -- burst [0, 1] is propositionally refuted; a SAT here would break soundness
- pigeon-3/burst[1, 2]: FAMILY-REFUSED (seed state hard-illegal (forced box violation or EDF-dead at time 0); n=0) -- burst [1, 2] is propositionally refuted; a SAT here would break soundness
- latepinch-clean (theorem control: class-UNSAT): FAMILY-REFUSED (exact-delayer-lost(0: debut 3); n=0) -- GB-LATE-PINCH premises hold; the class-soundness theorem says clocked-UNSAT -- family refusal corroborates
- lockhole: branch-at-seed certificate fires (ESC-LOCK)
- lockhole (ESC-LOCK prong-a conjunct hole): MASKED-SAT (plain grid m=4; winged: 5 spos-shadows; n=83) -- conjunct-pattern lock + exactness: the prong-(a) class-unsoundness witness -- late z-instances fail the spos conjunct, so the lock survives the late branch
- grand102-hand (chaser model, n=24): full formula HOLDS at seed -- the independent forcing-wing witness
- grand102 winged-family verdict: MASKED-SAT (plain grid m=4; winged: 10 forced-shadows; n=128) -- the forcing wing, mechanized (the unwinged refusal closed)
- jd-rebuilt (mechanical JD): MASKED-SAT (plain grid m=4; n=36) -- buildable branch-at-seed; family coverage control
- gnand-chain (stages 1,3: reorder, no branch): MASKED-SAT (plain grid m=4; n=30) -- buildable branch-at-seed; family coverage control
- pigeon-3-relaxed (stages 2,3,4): MASKED-SAT (plain grid m=4; n=128) -- buildable branch-at-seed; family coverage control
- xnand-sep (x@1, y@2, sep 1): MASKED-SAT (plain grid m=4; n=28) -- buildable branch-at-seed; family coverage control
- avoid-gnand (z avoid 2 pending 4, y@1, gap 1): MASKED-SAT (plain grid m=4; n=38) -- buildable branch-at-seed; family coverage control
- row-gnand (x fires y, y gnand z): MASKED-SAT (plain grid m=4; n=68) -- buildable branch-at-seed; family coverage control
- esc-free (z somewhere, no lock): MASKED-SAT (plain grid m=4; n=26) -- buildable branch-at-seed; family coverage control
- esc-lock (z somewhere, era ends by 2): MASKED-SAT (plain grid m=4; n=33) -- buildable branch-at-seed; family coverage control
- esc-window (z with AF<=1[y] at witness): MASKED-SAT (plain grid m=4; winged: 24 spos-shadows; n=94) -- buildable branch-at-seed; family coverage control
- esc-window-lock (witness in y-window, era ends by 1): MASKED-SAT (plain grid m=4; winged: 6 spos-shadows; n=47) -- buildable branch-at-seed; family coverage control
- esc-lock-pinch (z exact@3, lock@1): FAMILY-REFUSED (exact-delayer-lost(0: debut 3); n=0) -- bare-pattern lock pinch: class-sound (ESC-LOCK bare case) -- refusal corroborates

## witnesses: the frontier specimens + the collapse certificate
- grand533 collapse certificate: ESC-LOCK-COLLAPSE(a): lock 2 on 0, box-saturated: spos(1,2) by row; sup first-0 <= 2 <= 2 against exactness at stage 3
- grand533 winged-family verdict: FAMILY-REFUSED (exact-delayer-lost(0: debut 6)) -- corroborates the theorem (a SAT here would refute COLLAPSE)
- grand554 winged-family verdict: MASKED-SAT (plain grid m=4; winged: 402 spos-shadows; n=1291) -- clocked-SAT settled by the mechanized wings
- collapse soundness controls (14 model-confirmed specimens): no fires

## ms: pure-gnand decision-form instruments
- m2-refute: verdicts by grid {1: 'FAMILY-REFUSED', 2: 'FAMILY-REFUSED', 3: 'MASKED-SAT', 4: 'MASKED-SAT'} -- law-feasible core REFUSED at m=2, SAT at m=3: the m=2 conjecture is refuted by serialization (c=3)
- sweep (200 cores, seed 20260720): 60 screened, 122 family-SAT, 18 law-UNSAT, 0 open, 0 alarms
- m-monotonicity: SAT persists at every finer grid probed (all SAT specimens, m..8)
- minimal-m vs serialization constant (m_min, max(c, c_eff, c_branch)) -> count: {(1, 1): 48, (2, 1): 48, (2, 2): 19, (3, 1): 1, (3, 2): 3, (3, 3): 3}
- m0 = n_pending + 1 covered every family-SAT specimen (the repaired grid conjecture: every integer window is >= 1 and holds n slots strictly inside at m = n + 1; the per-atom constants c/c_eff/c_branch above are descriptive cargo -- pg62/pg84 showed per-atom counting cannot close the bound: first-of-PAIR windows are pair-level demands)
- CAP-invariant probe: 36 family-SAT cores at minimal m; 18 with exact-vs-cap divergence -- specimens [(1000, 2, 11, [((1, frozenset({(1, 8), (0, 4), (2, 8)}), 3), 0, 2, 3), ((1, frozenset({(3, 8), (1, 8), (0, 4), (2, 8)}), '.'), 0, 2, 3)]), (1002, 3, 1, [((1, frozenset({(0, 12), (1, 12), (2, 3)}), '.'), 1, 1, 11)]), (1006, 2, 1, [((0, frozenset({(1, 8), (0, 4), (2, 6)}), '.'), 2, 1, 6)]), (1014, 1, 1, [((0, frozenset({(0, 4), (1, 4)}), '.'), 0, 1, 4)])]

## sweep: 600 randoms (seed 20260720) re-classified; every certificate-refused specimen probed by the masked family
- classification: 398 built, 181 screened, 21 certificate-refused (banked receipts: 398/181/21)
- grand11 [GB-LATE-PINCH]: FAMILY-REFUSED (exact-delayer-lost(0: debut 3))
- grand23 [ESC-LOCK; 2 esc lock spos]: MASKED-SAT (plain grid m=4; winged: 36 spos-shadows; n=132)
- grand101 [ESC-LOCK; 1 esc lock]: FAMILY-REFUSED (exact-delayer-lost(0: debut 3))
- grand102 [ESC-LOCK; 1 esc lock sneg]: MASKED-SAT (plain grid m=4; winged: 10 forced-shadows; n=128)
- grand177 [ESC-LOCK; 1 esc lock sneg]: MASKED-SAT (plain grid m=4; winged: 19 forced-shadows; n=165)
- grand194 [ESC-LOCK; 1 esc lock rows]: FAMILY-REFUSED (exact-delayer-lost(1: debut 2))
- grand237 [GB-LATE-PINCH; 1 esc lock]: FAMILY-REFUSED (seed pruned (family infeasible))
- grand277 [GB-LATE-PINCH]: FAMILY-REFUSED (exact-delayer-lost(2: debut 3))
- grand300 [ESC-LOCK; 2 esc lock spos sneg]: MASKED-SAT (plain grid m=4; winged: 23 forced-shadows, 43 spos-shadows; n=324)
- grand303 [ESC-LOCK; 2 esc lock spos]: FAMILY-REFUSED (exact-delayer-lost(0: debut 3))
- grand323 [ESC-LOCK; 2 esc lock sneg]: FAMILY-REFUSED (exact-delayer-lost(2: debut 3))
- grand417 [ESC-BRANCH-INFEASIBLE (generic); 1 esc lock rows]: MASKED-SAT (plain grid m=4; n=38)
- grand471 [ESC-LOCK; 1 esc lock]: FAMILY-REFUSED (avoid-delayer-lost(1: debut 3))
- grand487 [ESC-BRANCH-INFEASIBLE (generic); 2 esc lock]: MASKED-SAT (plain grid m=4; n=59)
- grand533 [ESC-LOCK; 2 esc lock spos sneg rows]: FAMILY-REFUSED (exact-delayer-lost(0: debut 6))
- grand542 [ESC-LOCK; 2 esc lock spos sneg]: MASKED-SAT (plain grid m=4; winged: 331 forced-shadows, 136 spos-shadows; n=633)
- grand554 [ESC-BRANCH-INFEASIBLE (generic); 2 esc lock spos]: MASKED-SAT (plain grid m=4; winged: 402 spos-shadows; n=1291)
- grand572 [ESC-LOCK; 1 esc lock]: FAMILY-REFUSED (exact-delayer-lost(1: debut 7))
- grand578 [BRANCH-CORE-INFEASIBLE (generic); 1 esc lock]: FAMILY-REFUSED (seed pruned (exact box pass))
- grand580 [LATE-BRANCH-INFEASIBLE (generic); 2 esc lock spos]: FAMILY-REFUSED (exact-delayer-lost(2: debut 3))
- grand587 [BRANCH-CORE-INFEASIBLE (generic)]: FAMILY-REFUSED (seed pruned (family infeasible))
- verdict x certificate-kind table:
  BRANCH-CORE-INFEASIBLE (generic): 2 specimens -> 0 masked-SAT (reclassified), 2 family-refused
  ESC-BRANCH-INFEASIBLE (generic): 3 specimens -> 3 masked-SAT (reclassified), 0 family-refused
  ESC-LOCK: 12 specimens -> 5 masked-SAT (reclassified), 7 family-refused
  GB-LATE-PINCH: 3 specimens -> 0 masked-SAT (reclassified), 3 family-refused
  LATE-BRANCH-INFEASIBLE (generic): 1 specimens -> 0 masked-SAT (reclassified), 1 family-refused

family overall: PASS
