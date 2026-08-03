# nonstandard-time layer -- NSQ engine checks, the germ transfer shadow, C_eps soundness sweep, and the E2 semantic witnesses

- algebra: NSQ order/vector/mixed-type/hash/interval laws on samples: PASS
- diff-std: 400 random standard models/formulas, Fraction engine vs NSQ(b=0) engine: 0 mismatches: PASS

## zeno: the all-eps cycle (1 location, self-loop, dwell eps)
- engine liveness fixpoint calls it live: True (clock-blind, Archimedean assumption); is_ceps refuses it: True: PASS -- the acyclicity restriction is exactly the boundary where engine and NSQ semantics agree

## witness: lazy eps-models realizing E2 semantically (gamma + ALL blockers jointly at the seed)
- S_2 lazy: gamma at seed: yes; blockers (a0@1, a1@1; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=3, edges=[(0, 1), (1, 2)], stay=[2], u=['1-e', 'e', 'oo'], val={'a': [1], 'b': [2]}, live=[0, 1, 2])]
- S_3 lazy: gamma at seed: yes; blockers (a0@1, a1@1, a2@1; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1-2e', 'e', 'e', 'oo'], val={'a': [1], 'b': [2], 'c': [3]}, live=[0, 1, 2, 3])]
- curfew lazy: gamma at seed: yes; blockers (b1@1, b2@1; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=5, edges=[(0, 1), (1, 2), (2, 3), (3, 4)], stay=[4], u=['1-e', 'e', 'e', '1/2-2e', 'oo'], val={'a': [1], 'b': [2], 'c': [4]}, live=[0, 1, 2, 3, 4])]
- cascade lazy: gamma at seed: yes; blockers (theta=a&AF1[b]@1, b@2; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1-e', 'e', '1-e', 'oo'], val={'a': [1], 'b': [3]}, live=[0, 1, 2, 3])]
- adv1 lazy: gamma at seed: yes; blockers (a@1, b@2; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1-e', 'e', '1-e', 'oo'], val={'a': [1], 'b': [3]}, live=[0, 1, 2, 3])]
- adv2 lazy: gamma at seed: yes; blockers (a@1, b@1; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1-2e', 'e', 'e', 'oo'], val={'a': [1], 'b': [2], 'c': [], 'd': [0]}, live=[0, 1, 2, 3])]
- adv3 lazy: gamma at seed: yes; blockers (theta=a&AF1[b]@1, b@2; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=3, edges=[(0, 1), (1, 2)], stay=[2], u=['1', '1-e', 'oo'], val={'a': [0, 1, 2], 'b': [2]}, live=[0, 1, 2])]
- rand5 lazy: gamma at seed: yes; blockers (a@1, b@1, c@2; N in (2, 3, 4, 6, 12)): ALL HOLD -- loose past every tested sub-stage [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1', 'e', '1-e', 'oo'], val={'a': [1], 'b': [1], 'c': [3]}, live=[0, 1, 2, 3])]

## germ: NSQ verdicts vs eps := delta ladder ('1/8', '1/64', '1/512') (Lemma T shadow)
- S_2 lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- S_3 lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- curfew lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- cascade lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- adv1 lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- adv2 lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- adv3 lazy: 1/8: differs; 1/64: agree; 1/512: agree: stabilized -- PASS
- rand5 lazy: 1/8: agree; 1/64: agree; 1/512: agree: stabilized -- PASS

## soundness: 30 valid rows over C_eps (exhaustive n<=2, menu (e, 1-e, 1, 2, INF); +1500 random rounds n<=4, menu of 10); expectation ZERO hits (Corollary S)
- swept: 30 rows; eps-cycle models skipped as class-external: 34628; hits: 0: PASS

nstime overall: PASS
