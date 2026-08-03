# L_grain: the seed granularity conjecture, adjudicated

## width k = 2: `((~a&AF<=1[a])&(~b&AF<=1[b])) -> AF<=1[(a&b)]`
- explicit 1/2-dwell chain refutes: CONFIRMED at (v0, 0) [TModel(n=3, edges=[(0, 1), (1, 2)], stay=[2], u=['1/2', '1/2', 'oo'], val={'a': [1], 'b': [2]}, live=[0, 1, 2])]
- integer (denominator-1) menu (exhaustive n<=2 + 4000 random rounds n<=4): SILENT as the anchor-integrality proof predicts
- denominator-2 menu search (informational): countermodel rediscovered (n = 4)

## width k = 3: `(((~a&AF<=1[a])&(~b&AF<=1[b]))&(~c&AF<=1[c])) -> ((AF<=1[(a&b)]|AF<=1[(a&c)])|AF<=1[(b&c)])`
- explicit 1/3-dwell chain refutes: CONFIRMED at (v0, 0) [TModel(n=4, edges=[(0, 1), (1, 2), (2, 3)], stay=[3], u=['1/3', '1/3', '1/3', 'oo'], val={'a': [1], 'b': [2], 'c': [3]}, live=[0, 1, 2, 3])]
- integer (denominator-1) menu (exhaustive n<=2 + 4000 random rounds n<=5): SILENT as the anchor-integrality proof predicts
- denominator-2 menu (informational): no countermodel in budget (NOT a validity claim; the k=3 case has a hand-built m=2 witness the random tier misses -- see (iv))
- denominator-3 menu search (informational): random tier missed the chain shape; certificate is the explicit witness in (i)

## (iv) bipartition witness: k = 3 at denominator 2
- explicit 5-location half-dwell model [TModel(n=5, edges=[(0, 1), (0, 2), (1, 4), (2, 3)], stay=[3, 4], u=['1/2', '1/2', '1/2', 'oo', 'oo'], val={'a': [1, 2], 'b': [1, 3], 'c': [3, 4]}, live=[0, 1, 2, 3, 4])]: REFUTES k=3 L_grain at (v, c) for c in [0,1/2) -- width pressure collapses under valuation overlap

grain overall: PASS
