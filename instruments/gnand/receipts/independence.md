# independence battery (exit-coded)

- CHAIN control (honest discrete model): FS-R(2,3;1) holds (as it must)
- CHAIN basis roster: CLEAN
- UNREPAIRED fork control: FS_2 violated (jaw bites: ('FS2', 1, 1, 2))
- EDGE-MINIMALITY sweep on S_1 (every single-edge removal must destroy witness-hood): CLEAN -- all 9 edges load-bearing; x->u1:target-valid x->w1:target-valid u1->a*:target-valid u1->w1:basis-broken a*->w1:basis-broken w1->w2:basis-broken w2->b*:target-valid w2->a*:basis-broken b*->a*:basis-broken

## S_1 (must be a WITNESS)
# FS-R independence: the hub-cross fork gadget S_1 (6 states, horizon 5)

states: x u1 a* w1 w2 b*
  G(x) = {u1} | {w1}
  G(u1) = {a*} | {w1}
  G(a*) = {w1}
  G(w1) = {w2}
  G(w2) = {b*} | {a*}
  G(b*) = {a*}

## basis validation (must be CLEAN)
- structural roster (U4/U3/U9/MONO/U7-sanity/G-layer/U10F/REACH): CLEAN
- FS_2 exhaustive (all set pairs, deadlines <= 5): CLEAN
- FS_3 (exhaustive): CLEAN
- tier-tournament condition (Lemma TT: implies FS_n all n, all sets): CLEAN

## FS-R instance report (atoms E_a, E_b)
- FS-R(2,3;1) on (E_a,E_b): REFUTED at x  <== THE TARGET (wall-hand shape)
- FS-R(2,2;1) on (E_a,E_b): valid
- FS-R(3,3;1) on (E_a,E_b): valid
- FS-R(3,3;2) on (E_a,E_b): valid
- FS-R(3,2;1) on (E_a,E_b): valid
- census at (2,3;1): 2/4096 set pairs refute FS-R (nonzero = the schema itself fails here; the basis instances above must all HOLD for the certificate)

S_1 verdict: WITNESS (basis clean, target refuted)

## S_2 stretched-gadget probe (informational; expected NOT A WITNESS -- m >= 2 is open)
# FS-R independence: the hub-cross fork gadget S_2 (11 states, horizon 8)

states: x u1 u2 u3 a* w1 w2 w3 w4 w5 b*
  G(x) = {u1} | {w1}
  G(u1) = {u2} | {w1}
  G(u2) = {u3}
  G(u3) = {a*}
  G(a*) = {w3}
  G(w1) = {w2}
  G(w2) = {w3}
  G(w3) = {w4}
  G(w4) = {w5} | {a*}
  G(w5) = {b*}
  G(b*) = {a*}

## basis validation (must be CLEAN)
- structural roster (U4/U3/U9/MONO/U7-sanity/G-layer/U10F/REACH): CLEAN
- FS_2 exhaustive (all set pairs, deadlines <= 8): VIOLATIONS [('FS2', 1, 1, 4, 32), ('FS2', 1, 1, 4, 33), ('FS2', 1, 1, 5, 32), ('FS2', 1, 1, 5, 33), ('FS2', 1, 1, 12, 32), ('FS2', 1, 1, 12, 33), ('FS2', 1, 1, 13, 32), ('FS2', 1, 1, 13, 33), ('FS2', 1, 1, 16, 512), ('FS2', 1, 1, 16, 513), ('FS2', 1, 1, 17, 512), ('FS2', 1, 1, 17, 513)]
- FS_3 (sampled 200k): VIOLATIONS [('FS3', (1, 2, 7), 1824, 773, 609, ['u1']), ('FS3', (1, 1, 2), 796, 112, 201, ['u1']), ('FS3', (1, 3, 6), 148, 1857, 1280, ['u1']), ('FS3', (1, 2, 8), 614, 238, 1658, ['w4']), ('FS3', (1, 2, 6), 1504, 1797, 1312, ['u1']), ('FS3', (1, 2, 5), 1072, 1545, 1313, ['u1']), ('FS3', (1, 1, 2), 1579, 185, 229, ['w4']), ('FS3', (1, 2, 8), 116, 616, 1689, ['w4']), ('FS3', (1, 1, 8), 1825, 660, 1689, ['u1']), ('FS3', (3, 3, 5), 33, 1565, 1344, ['u1']), ('FS3', (1, 2, 5), 560, 277, 1676, ['u1']), ('FS3', (1, 3, 8), 216, 1101, 133, ['w4'])]
- tier-tournament condition (Lemma TT: implies FS_n all n, all sets): VIOLATIONS [('x', 2, 'untotal', 'u2', 'w2'), ('u1', 1, 'untotal', 'u2', 'w1'), ('u1', 2, 'untotal', 'u3', 'w2'), ('w4', 1, 'untotal', 'a*', 'w5')]

## FS-R instance report (atoms E_a, E_b)
- FS-R(4,6;1) on (E_a,E_b): REFUTED at x,u1
- FS-R(4,6;2) on (E_a,E_b): REFUTED at x,u1  <== THE TARGET (wall-hand shape)
- FS-R(4,6;3) on (E_a,E_b): REFUTED at x
- FS-R(4,4;1) on (E_a,E_b): valid
- FS-R(4,4;2) on (E_a,E_b): valid
- FS-R(4,4;3) on (E_a,E_b): valid
- FS-R(6,6;1) on (E_a,E_b): valid
- FS-R(6,6;2) on (E_a,E_b): valid
- FS-R(6,6;3) on (E_a,E_b): valid
- FS-R(6,6;4) on (E_a,E_b): valid
- FS-R(6,6;5) on (E_a,E_b): valid
- FS-R(6,4;1) on (E_a,E_b): valid
- FS-R(6,4;2) on (E_a,E_b): valid
- FS-R(6,4;3) on (E_a,E_b): valid
- census at (4,6;2): 60/4194304 set pairs refute FS-R (nonzero = the schema itself fails here; the basis instances above must all HOLD for the certificate)

S_2 verdict: NOT A WITNESS

battery overall: PASS (S_2 probe informational: not a witness, as recorded)
