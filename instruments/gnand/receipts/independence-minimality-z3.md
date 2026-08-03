# FS-R six-state minimality: z3 search receipts (m = 1)

Singleton-generator class (E_a = {a*}, E_b = {b*}):
# m=1, n=3
  z3: unsat at n=3 after 0 candidate(s)
# m=1, n=4
  z3: unsat at n=4 after 0 candidate(s)
# m=1, n=5
  z3: unsat at n=5 after 0 candidate(s)
# m=1, n=6
  VERIFIED witness at n=6 (candidate 1): edges=[(0, 3), (0, 5), (1, 5), (2, 1), (2, 3), (2, 4), (2, 5), (3, 1), (3, 5), (4, 1), (4, 2), (4, 3), (4, 5), (5, 4)]
states: x a* b* s3 s4 s5
  G(x) = {s3} | {s5}
  G(a*) = {s5}
  G(b*) = {a*} | {s3} | {s4} | {s5}
  G(s3) = {a*} | {s5}
  G(s4) = {a*} | {b*} | {s3} | {s5}
  G(s5) = {s4}
Ea = ['a*']  Eb = ['b*']

Free-set widening (E_a, E_b arbitrary sets, premise relaxed):
# m=1, n=3 [sets]
  z3(sets): unsat at n=3 after 0 candidate(s)
# m=1, n=4 [sets]
  z3(sets): unsat at n=4 after 0 candidate(s)
# m=1, n=5 [sets]
  z3(sets): unsat at n=5 after 0 candidate(s)
