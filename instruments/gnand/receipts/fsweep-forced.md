# S_k: the disjointness-forced grain family (the corrected conjecture, adjudicated)

Certificate structure: refutations are explicit witness models (machine-checked here); silences are hand-proved for ALL location counts and menus (Lemma SEQ, development record) -- the searches corroborate and would FALSIFY the proof if they hit.

## k = 2: `(((~a&AF<=1[a])&(~b&AF<=1[b]))&AG[~(a&b)]) -> D`
- (1/2,1/2)-chain refutes at denominator 2: CONFIRMED at (v0, 0)
- denominator-1 menu (exhaustive n<=2 + 2500 random n<=6): SILENT as Lemma SEQ proves (k=2 needs m>=2)

## k = 3: `((((~a&AF<=1[a])&(~b&AF<=1[b]))&(~c&AF<=1[c]))&AG[((~(a&b)&~(a&c))&~(b&c))]) -> D`
- (1/3,1/3,1/3)-chain refutes at denominator 3: CONFIRMED at (v0, 0)
- DYADIC (1/4,1/4,1/2)-chain refutes at denominator 4: CONFIRMED at (v0, 0) -- the obstruction is min-dwell <= 1/3-ish room, not parity
- denominator-1 menu (exhaustive n<=2 + 2500 random n<=6): SILENT as Lemma SEQ proves (k=3 needs m>=3)
- denominator-2 menu (exhaustive n<=2 + 2500 random n<=6): SILENT as Lemma SEQ proves (k=3 needs m>=3)
- box-off contrast (G3 bipartition model, denominator 2): boxless width-3 grain REFUTED there; S_3 antecedent satisfied NOWHERE live (the box is exactly what the bipartition escape violates)

## k = 4: `(((((~a&AF<=1[a])&(~b&AF<=1[b]))&(~c&AF<=1[c]))&(~d&AF<=1[d]))&AG[(((((~(a&b)&~(a&c))&~(a&d))&~(b&c))&~(b&d))&~(c&d))]) -> D`
- (1/4 x4)-chain refutes at denominator 4: CONFIRMED at (v0, 0)
- denominator-2 menu (random-only, 2500 rounds n<=6; the certificate is Lemma SEQ, which covers all n): SILENT
- denominator-3 menu (random-only, 2500 rounds n<=6; the certificate is Lemma SEQ, which covers all n): SILENT

## verdict on the corrected small-model conjecture
- S_3: G = 1, A-nesting depth 1, NO countermodel at denominators 1-2 (SEQ), countermodels at 3 and 4. Hypothesis c = 2: REFUTED. Hypothesis c = 2^depth (= 2 here): REFUTED.
- S_k needs some dwell bound < 1/(k-1) (denominator >= k): countermodel granularity is UNBOUNDED in formula width at fixed G and fixed nesting depth. The grid must scale with the number of graded subformulas (k of them in S_k -- the 1/k-chain shows this count is tight for the family).

## depth-2 tower probes (m = 2 witnesses asserted; m = 1 impossibility = SEQ via projection/descent)
- T2 cascade a>(c) || b: half-dwell chain witness at denominator 2: CONFIRMED at (v0, 0); denominator-1 SILENT (projected (alpha) SEQ proves all n)
- T3 width-2 inside cascade: half-dwell chain witness at denominator 2: CONFIRMED at (v0, 0); denominator-1 SILENT (descent (beta) SEQ proves all n)
- T4 shared window + cascade: half-dwell chain witness at denominator 2: CONFIRMED at (v0, 0); denominator-1 SILENT (projected (alpha) SEQ proves all n)
- verdict: no depth-driven grid refinement in these shapes; each tower grid demand equals what projection/descent expose to SEQ

forced overall: PASS
