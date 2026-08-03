- interval algebra vs point sampling (600 rounds): CONFIRMED
- v0 differential, u=oo embedding (1200 rounds): CONFIRMED
- SCALE metamorphic (lam = 2, 1/3; 400 rounds): CONFIRMED

# timed oracle battery -- EQ-U rows + controls, exhaustive n<=2 (u menu (Fraction(1, 1), Fraction(2, 1), INF)) + 3000 random rounds

- **EQ-U1** (F from U: trivial safe clause): CONFIRMED (no countermodel)
- **EQ-U3** (deadline weakening T <= T'): CONFIRMED (no countermodel)
- **EQ-U3-U** (deadline weakening, U form): CONFIRMED (no countermodel)
- **EQ-U3-strict** (weakening direction is strict: T' < T refutable): countermodel found as expected: TCX(q=1, c=0, lhs>rhs, TModel(n=2, edges=[(1, 0)], stay=[0], u=['oo', '1'], val={'a': [0]}, live=[0, 1]))
- **EQ-U4** (reflexivity, even with bot safe argument): CONFIRMED (no countermodel)
- **EQ-U4-conv** (reflexivity converse control): countermodel found as expected: TCX(q=0, c=0, lhs>rhs, TModel(n=1, edges=[], stay=[], u=['1'], val={'a': [], 'b': []}, live=[]))
- **EQ-U5** (zero-deadline collapse (boundary case)): CONFIRMED (no countermodel)
- **EQ-U6** (invariant + deadline strengthen to until): CONFIRMED (no countermodel)
- **EQ-U6-conv** (until does not give invariance past the debut): countermodel found as expected: TCX(q=0, c=0, lhs>rhs, TModel(n=1, edges=[], stay=[0], u=['oo'], val={'a': [0], 'b': []}, live=[0]))
- **EQ-U7** (deadline composition): CONFIRMED (no countermodel)
- **EQ-U7-conv** (FINDING: the converse is C_0-VALID (B3-fusion proof; the once-conjectured hand-countermodel does not exist) -- EQ-U7 upgrades to an equivalence): CONFIRMED (no countermodel)
- **EQ-U7-conv-asym** (asymmetric split of the same equivalence): CONFIRMED (no countermodel)
- **EQ-U8-cd** (until pasting: valid over C_cd = this whole model class (the C_0 countermodel lives outside it)): CONFIRMED (no countermodel)
- **EQ-U8-conv** (FINDING: U-pasting converse is C_0-valid (fusion proof, a subseteq Y + safe-clause bookkeeping)): CONFIRMED (no countermodel)
- **EQ-C2** (zero-deadline closure collapse (atoms are clopen here)): CONFIRMED (no countermodel)
- **S10-F** (deadline variant of EQ-S10: one visit to a Streett-guaranteeing region suffices (tail property)): CONFIRMED (no countermodel)
- **S9-F-tight** (one visit is not now: control): countermodel found as expected: TCX(q=0, c=0, lhs>rhs, TModel(n=1, edges=[], stay=[], u=['1'], val={'a': []}, live=[]))
- **U-safety-necessity** (F does not carry the safe clause: control): countermodel found as expected: TCX(q=1, c=0, lhs>rhs, TModel(n=2, edges=[(1, 0)], stay=[0], u=['oo', '1'], val={'a': [0], 'b': []}, live=[0, 1]))
- **U-nesting-G** (EQ-G4 shadow at a timed operand (quasi-reflexivity + vacuity)): CONFIRMED (no countermodel)
- **EQ-U9** (deadline vacuity converse: AF<=T[F] == D (the F-wrapper sibling of EQ-S12; live states cannot reach bot)): CONFIRMED (no countermodel)
- **EQ-U10s** (invariant relativization of the U safe position (the graded EQ-S7)): CONFIRMED (no countermodel)
- **EQ-U10t** (invariant relativization of the U target position): CONFIRMED (no countermodel)
- **EQ-U10-noinv** (relativization without the certified invariant: control): countermodel found as expected: TCX(q=1, c=0, lhs>rhs, TModel(n=2, edges=[(1, 0)], stay=[0], u=['oo', '1'], val={'a': [0], 'b': [1]}, live=[0, 1]))

timed battery overall: PASS
