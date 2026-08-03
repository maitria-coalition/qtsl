# cores: the graded-box constructive tier (builder + refusal classifier)

Ground truth is the evaluator: every emitted model is cross-checked with tdenot at the seed against the FULL graded formula (positives, exactness, avoid, graded boxes, escapes, locks), plus a germ-shadow spot check.  Refusals are classified three ways: screened (deduction-backed), semantic-certificate (derivability OPEN -- the harvest), alarm (loud).

## roster: curated graded-box specimens (the Spec-grammar gap closed; JD rebuilt mechanically)
- jd-rebuilt (mechanical JD): built n=11 B=2 (+0 escape branches); seed formula PASS; germ shadow stable
- jd-relax (no exactness: chain closes): built n=6 B=1 (+0 escape branches); seed formula PASS; germ shadow stable
- gnand-chain (stages 1,3: reorder, no branch): built n=6 B=1 (+0 escape branches); seed formula PASS; germ shadow stable
- pigeon-3 (pairwise gnand, stages 2,2,2): REFUSED-SEMANTIC (GB-PIGEON: atoms (0, 1, 2) pairwise staggered, min chain span 2 >= loosest deadline 2: every trajectory refuted) -- branch-at-seed infeasibility; clocked-SAT open (masking can satisfy such specimens); builder detail: B=1 rot[0] branch 0 infeasible; B=1 rot[1] branch 0 infeasible; B=1 rot[2] branch 0 infeasible; B=2 rot[0, 1] branch 0 infeasible; B=2 rot[1, 2] branch 0 infeasible; B=2 rot[2, 0] branch 0 infeasible; B=3 rot[0, 1, 2] branch 0 infeasible
- pigeon-3-relaxed (stages 2,3,4): built n=8 B=1 (+0 escape branches); seed formula PASS; germ shadow stable
- esc-free (z somewhere, no lock): built n=9 B=1 (+1 escape branches); seed formula PASS; germ shadow stable; esc: post-busy(lazy tail)
- esc-lock (z somewhere, era ends by 2): built n=9 B=1 (+1 escape branches); seed formula PASS; germ shadow stable; esc: post-busy(lazy tail)
- esc-lock-pinch (z exact@3, lock@1): REFUSED-SEMANTIC (ESC-LOCK: lock 1 on pos atom 0 exact at stage 3: late-branch z-instance > 2 >= T (LOCK-ABS candidate)) -- branch-at-seed infeasibility; clocked-SAT open (masking can satisfy such specimens); builder detail: B=1 rot[0] branch 0 infeasible; B=2 rot[0, 0] branch 0 infeasible
- esc-window (z with AF<=1[y] at witness): built n=8 B=1 (+1 escape branches); seed formula PASS; germ shadow stable; esc: post-busy(lazy tail)
- esc-window-lock (witness in y-window, era ends by 1): built n=9 B=1 (+1 escape branches); seed formula PASS; germ shadow stable; esc: mid-schedule(unit 2)
- esc-contra (pos pair disjoint): REFUSED-SCREENED (ESC-CONTRA: escape pos contains disjoint pair (1,2))
- xnand-sep (x@1, y@2, sep 1): built n=6 B=1 (+0 escape branches); seed formula PASS; germ shadow stable
- avoid-gnand (z avoid 2 pending 4, y@1, gap 1): built n=6 B=1 (+0 escape branches); seed formula PASS; germ shadow stable
- gb-refl (both forced inside windows): REFUSED-SCREENED (GB-REFL: gnand(0,2,1,2) with both forced at seed (eff 1, 1))
- row-gnand (x fires y, y gnand z): built n=8 B=1 (+0 escape branches); seed formula PASS; germ shadow stable

## random: 200 graded-box specimens (seed 20260720); three-way classified refusals; unexplained refusal = ALARM
- 131 built and evaluator-confirmed (2 needed staggered branches), 63 screened (deduction-backed), 6 refused with semantic certificates {'GB-LATE-PINCH': 1, 'ESC-LOCK': 5}, 0 alarms
- escape-position ledger (the ESC probe): {'existing-state': 27, 'mid-schedule(unit 2)': 17, 'mid-schedule(unit 3)': 9, 'post-busy(lazy tail)': 54}

## offers: SUCC-CON-P enumerator over graded cores (roster + 200 randoms, seed 20260720); builder-closed core with an offerless obligatory context = LEMMA-FALSE alarm
- 162 built cores: every obligatory context offer-checked (per-context offers min 1 max 8); realized patterns confirmed 181 (+0 undecided-but-witnessed); 2 refused cores, 2 with an all-refusing context confirmed; refusal mechanisms {'cert:BRANCH-CORE-INFEASIBLE': 3, 'cert:GB-LATE-PINCH': 4, 'cert:GB-PIGEON': 4, 'cert:LATE-BRANCH-INFEASIBLE': 3, 'screen:AV': 178, 'screen:GB-REFL': 74}; 0 alarms

## masked: the deep-branching witness tier (per-trajectory certificates are builder-class only; SUCC-CON-P as stated is refuted)
- pigeon-3 masked witness: 57 states, full seed formula HOLDS at seed (clocked-SAT; GB-PIGEON is class-unsound)
- masking signature: worst-case debut > 1 for every atom at the seed confirmed
- branch-at-seed tier: certificate fires (GB-PIGEON) -- sound for that class, refuted as a satisfiability claim by the witness above
- pattern-form offers at the pigeon cell: 8/8 refused propositionally (4 burst, 4 boundary) -- consistent cell, all offers refused: SUCC-CON-P as stated is FALSE

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

cores overall: PASS
