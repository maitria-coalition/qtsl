# F-fragment small-model sweep (seed=2026)

- corpus: 29 refuted pairs profiled, 1 apparently-valid, 0 filtered as propositional-skeleton tautologies (the R6 filter, first tooth)

## minimality profiles of refuted pairs

| pair | size | lcm base | n_min | n exact? | gran mult | clock den |
|---|---|---|---|---|---|---|
| `(F&a)` vs `AF<=2[T]` | 5 | 1 | 1 | yes | x1 | 1 |
| `AF<=2[AF<=2[(a&a)]]` vs `~AF<=2[a]` | 8 | 1 | 1 | yes | x1 | 1 |
| `(AF<=3/2[T]&AF<=1/2[a])` vs `((~b&~b)|(~T|AG[T]))` | 16 | 2 | 1 | yes | x1 | 1 |
| `(AF<=2[b]|AF<=2[a])` vs `(~~a&AG[(a|T)])` | 13 | 1 | 1 | yes | x1 | 1 |
| `AG[b]` vs `AF<=3/2[AG[AG[b]]]` | 6 | 2 | 2 | yes | x1 | 1 |
| `((a&b)|AF<=2[a])` vs `AG[(T|b)]` | 10 | 1 | 1 | yes | x1 | 1 |
| `AG[~(a&b)]` vs `AF<=1[AF<=2[F]]` | 8 | 1 | 1 | yes | x1 | 1 |
| `AF<=3/2[~(b&a)]` vs `(AG[AF<=3/2[a]]&AF<=3/2[(a|a)])` | 13 | 2 | 1 | yes | x1 | 1 |
| `~~T` vs `AF<=3/2[F]` | 5 | 2 | 1 | yes | x1 | 1 |
| `(F&a)` vs `AF<=1[(a|a)]` | 7 | 1 | 1 | yes | x1 | 1 |
| `AF<=1[~AF<=2[b]]` vs `(a|b)` | 7 | 1 | 1 | yes | x1 | 1 |
| `(~b&~T)` vs `AF<=1[(F&T)]` | 9 | 1 | 1 | yes | x1 | 1 |
| `(AG[AF<=1[F]]&(~a&~a))` vs `((AG[b]&~a)&AG[AF<=1[a]])` | 18 | 1 | 2 | yes | x1 | 1 |
| `AG[b]` vs `AF<=1/2[AF<=3/2[b]]` | 5 | 2 | 2 | yes | x1 | 1 |
| `AF<=1/2[AG[T]]` vs `AF<=3/2[(AF<=3/2[b]|AF<=3/2[b])]` | 9 | 2 | 1 | yes | x1 | 1 |
| `AF<=1/2[((a|b)&(a&a))]` vs `~b` | 10 | 2 | 1 | yes | x1 | 1 |
| `(b|a)` vs `AG[AF<=1[b]]` | 6 | 1 | 1 | yes | x1 | 1 |
| `AF<=1[~b]` vs `((F&a)&AG[b])` | 9 | 1 | 1 | yes | x1 | 1 |
| `AG[AF<=3/2[a]]` vs `AF<=2[~(a&F)]` | 8 | 2 | 1 | yes | x1 | 1 |
| `AG[(T&b)]` vs `AF<=3/2[(b&T)]` | 8 | 2 | 2 | yes | x1 | 1 |
| `AG[(AG[a]&AF<=2[T])]` vs `~(AG[a]&AF<=1/2[b])` | 12 | 2 | 1 | yes | x1 | 1 |
| `(~AG[T]&~(b&b))` vs `AF<=1/2[T]` | 10 | 2 | 1 | yes | x1 | 1 |
| `((AF<=1[a]|~a)|~~a)` vs `~(a&b)` | 13 | 1 | 1 | yes | x1 | 1 |
| `~AF<=1/2[b]` vs `~((a|T)|AG[b])` | 10 | 2 | 1 | yes | x1 | 1 |
| `~F` vs `AF<=3/2[AF<=1[b]]` | 5 | 2 | 1 | yes | x1 | 1 |
| `AG[(AF<=2[a]&(b&T))]` vs `(AF<=2[b]|AF<=1[b])` | 12 | 1 | 1 | yes | x1 | 1 |
| `(T&a)` vs `AG[(AF<=1/2[b]&AG[b])]` | 9 | 2 | 1 | yes | x1 | 1 |
| `(~AF<=2[F]|AF<=1[(a|F)])` vs `~(AG[b]&AF<=2[T])` | 14 | 1 | 1 | yes | x1 | 1 |
| `((~a|~b)|((b|T)|AG[b]))` vs `AF<=2[(a|a)]` | 16 | 1 | 1 | yes | x1 | 1 |

- pairs needing granularity strictly finer than the deadline lcm: **0** of 29
- (the hand specimen L_grain, `grain` subcommand, shows the finer-than-lcm class is nonempty by construction; the sweep measures how often random pairs land in it)

## apparently-valid candidates (post-filter)
- `AF<=3/2[AF<=1/2[T]]`  ==  `AG[(AG[a]|AF<=1[T])]`
