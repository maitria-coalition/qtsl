# Program route: measured behavior (2026-07-22)

The package exists as the positive control for the reflection route's
scaling measurements: same Lean-defined decode and check functions,
kernel removed, Lean's code generator trusted (README). These runs
answer one question — is the reflection ladder's ≈3.6-power law the
kernel's cost or the checking logic's? — and the answer is: **the
checking logic's.** The program route, an independent binary with a
single clean evaluation per certificate, reproduces the law.

Host: the same dedicated 16-thread AMD EPYC 7B13 / 126 GiB box as the
reflection-route ladder run, same 15-rung sealed-container ladder
(603 B – 126,216 B), same 600 s budget, 2 passes per rung. `t_check`
is the program's own monotonic timing of `acceptBytesSealed` (stderr);
the sequent render is separately timed and never exceeded 12 ms.

## The two laws, side by side

Fitted on the identical 9-rung domain (919 – 24,686 container bytes,
accepted rungs, log-log OLS):

| route | law (seconds) | exponent 95% CI | r² |
|---|---|---|---|
| reflection, compiled (staged runner, morning run) | exp(−30.207) · bytes^3.577 | [3.24, 3.92] | 0.989 |
| program (`qtslab_lean`), this run | exp(−29.851) · bytes^3.532 | [3.22, 3.85] | 0.990 |

Statistically the same law. The kernel contributes nothing to the
exponent because the kernel was never in either binary; its cost is a
separate regime, not a slope — the reflection route's `decide`
receipts cost ≈3×10⁵× the compiled time at 919 B with ~124–233 GiB
peak RSS, and admit nothing at all on a 126 GiB host (see the
reflection package's `MEASUREMENTS.md`). What grows at the 3.5–3.6
power is the shared checking logic itself, dominated by the
purely-functional reader (chosen for kernel evaluability, not speed).

Over the program route's own full accepted range (10 rungs,
919 – 43,401 B): exp(−28.147) · bytes^3.321, CI [2.93, 3.72],
r² 0.979 — the wider domain lowers the point estimate because the
largest accepted rung (a neural-network certificate) is cheap for its
size; family-to-family scatter around the law is real (±e in either
direction) and bytes is a proxy regressor, not a cost model.

## Per-rung (t_check ms, mean of passes; timeout = not finished in budget)

| certificate | bytes | program | reflection compiled (same box) |
|---|---:|---:|---:|
| enclosure_v1_golden_cos6 | 603 | refuse (0.4) | refuse |
| ctmc_sis_gen | 919 | 2.8 | 2.4 |
| ctmc_fk_mid | 1,793 | 47.7 | 50.7 |
| micro2_stable | 2,184 | 107.5 | 119.0 |
| cartpole_core_decrease_s0001 | 4,068 | 399.3 | 431.7 |
| rode_uniform_decrease | 7,652 | 2,815 | 2,850 |
| cartpole_dp_core_decrease | 9,336 | 10,436 | 9,607 |
| dp_composite_syzygy | 17,591 | 98,159 | 99,264 |
| dp_composite_eigenrate | 22,056 | 429,325 | 442,575 |
| lti_sampled_flow | 24,686 | 369,632 | 481,217 |
| acasx4_init_s0000 | 43,401 | 452,820 | timeout |
| dp_composite_smallgain | 46,015 | timeout | timeout |
| acasx4_promise_closedloop | 57,779 | timeout | timeout |
| rode_nest_shell | 119,217 | timeout | timeout |
| rode_hold_flow | 126,216 | timeout | timeout |

Two rungs moved against the earlier run: `lti_sampled_flow` ran ≈23%
faster here, and `acasx4_init_s0000` — a reflection-run timeout —
accepted at ≈453 s. Neither is a property of the route. The direct
control: a same-day rebuild of the *reflection* binary re-ran
`acasx4_init_s0000` and accepted it in 451.6 s end-to-end (438.6 s of
it in the reader) — indistinguishable from the program route's
452.8 s — and ran the small rungs 10–30% faster than its own morning
numbers. So the verdict flip is build/run variance at the budget
line, and the observed 10-minute admission horizon is best stated as
a band, ≈28–33 KB, fuzzed by that variance and dominated by content
scatter (a 43.4 KB neural certificate passes with room to spare while
a 46.0 KB dp_composite does not). The exponent, not the coefficient
or any single verdict, is what transfers.

## What the sequent print costs

Rendering the accepted sequent (fully parenthesized, exact rationals,
region atoms with their whole complex) never exceeded 12 ms or 70 KB
of output on any accepted rung — four orders of magnitude below the
check at the sizes where anyone would care. The print is not a cost
axis; the check is.
