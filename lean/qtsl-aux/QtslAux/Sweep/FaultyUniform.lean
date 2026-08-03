import QtslAux.OptionalStopping
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The `FaultyUniform` benchmark row (continuous state, two-sided bounds)

Certified two-sided bounds on a fault probability for the benchmark with uniform continuous noise.
The state is `ℝ × Bool` (position, fault flag); while the flag is `false` and `1 ≤ x < 10`, the
kernel `stepK` raises the fault flag with probability `1/1000` and otherwise moves to `x + u` with
`u` uniform on `[0, 1]` (measure `eta`); all other states are absorbing. `Viol` is the set of
faulted states and `Active` the region where the dynamics act.

Two piecewise-cubic certificates with exact rational coefficients are internalized: the pieces
`p1`–`p10` (assembled into `Vr`, then `V`) form a supermartingale upper certificate, and `q1`–`q9`
(assembled into `Wr`, then `W`) form a submartingale lower certificate. Drift conditions are
discharged by exact antiderivatives (`Ap1`–`Ap10`, `Aq1`–`Aq9`; `drift_1`–`drift_9`,
`ldrift_1`–`ldrift_9`), and every polynomial sign condition is certified by an expansion with
sign-definite coefficients in the Bernstein basis on the relevant unit cell.

Main results, from initial state `(1, false)`:

* `sound_upper`: the probability of ever faulting is at most `150065 / 8087357` (about
  `0.0185555`), via `Battery.measure_reach_le`;
* `sound_lower`: it is at least about `0.0184458` (an exact rational in the statement), via the
  optional-stopping bound `OptionalStopping.measure_reach_ge` with per-step escape parameter
  `999/1000`;
* `sound_bracket`: the two bounds packaged as a conjunction;
* `published_farkas_refuted`: the fault probability strictly exceeds `181/10000`, so a
  Farkas-certificate upper bound of `0.0181` previously reported for this benchmark cannot be
  correct.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.FaultyUniform

noncomputable def p1 : ℝ → ℝ := fun x => (1395223692374691958 / 67989770008801522607 : ℝ) + ((-16507902491) / 8406920828251 : ℝ) * x ^ 1 + ((-4) / 2032313 : ℝ) * x ^ 2

noncomputable def Ap1 : ℝ → ℝ := fun x => (1395223692374691958 / 67989770008801522607 : ℝ) * x ^ 1 + ((-16507902491) / 16813841656502 : ℝ) * x ^ 2 + ((-4) / 6096939 : ℝ) * x ^ 3

noncomputable def p2 : ℝ → ℝ := fun x => (4072233538158690685629569 / 198429743739822271336250000 : ℝ) + ((-317078814294886157) / 161347885321797500000 : ℝ) * x ^ 1 + ((-47683729) / 37193785000000 : ℝ) * x ^ 2 + ((-1) / 10000000 : ℝ) * x ^ 3

noncomputable def Ap2 : ℝ → ℝ := fun x => (4072233538158690685629569 / 198429743739822271336250000 : ℝ) * x ^ 1 + ((-317078814294886157) / 322695770643595000000 : ℝ) * x ^ 2 + ((-47683729) / 111581355000000 : ℝ) * x ^ 3 + ((-1) / 40000000 : ℝ) * x ^ 4

noncomputable def p3 : ℝ → ℝ := fun x => (1842892121146437672567071 / 89776018778735789932485326 : ℝ) + ((-3368288840463565) / 1710144131821267306 : ℝ) * x ^ 1 + ((-7892819) / 49048311818058 : ℝ) * x ^ 2 + ((-1) / 5505026 : ℝ) * x ^ 3

noncomputable def Ap3 : ℝ → ℝ := fun x => (1842892121146437672567071 / 89776018778735789932485326 : ℝ) * x ^ 1 + ((-3368288840463565) / 3420288263642534612 : ℝ) * x ^ 2 + ((-7892819) / 147144935454174 : ℝ) * x ^ 3 + ((-1) / 22020104 : ℝ) * x ^ 4

noncomputable def p4 : ℝ → ℝ := fun x => (49788592698436741 / 2427539499487824769 : ℝ) + ((-894817124) / 456907242749 : ℝ) * x ^ 1 + ((-5) / 1945456 : ℝ) * x ^ 2

noncomputable def Ap4 : ℝ → ℝ := fun x => (49788592698436741 / 2427539499487824769 : ℝ) * x ^ 1 + ((-447408562) / 456907242749 : ℝ) * x ^ 2 + ((-5) / 5836368 : ℝ) * x ^ 3

noncomputable def p5 : ℝ → ℝ := fun x => (89083109809413373372501186 / 4444250497018486792718454717 : ℝ) + ((-1577809460133826493) / 920053340422800467271 : ℝ) * x ^ 1 + ((-4212600001) / 93864134891959 : ℝ) * x ^ 2 + (23 / 9411313 : ℝ) * x ^ 3

noncomputable def Ap5 : ℝ → ℝ := fun x => (89083109809413373372501186 / 4444250497018486792718454717 : ℝ) * x ^ 1 + ((-1577809460133826493) / 1840106680845600934542 : ℝ) * x ^ 2 + ((-4212600001) / 281592404675877 : ℝ) * x ^ 3 + (23 / 37645252 : ℝ) * x ^ 4

noncomputable def p6 : ℝ → ℝ := fun x => (26702597727305802136943 / 1729078416188548765385045 : ℝ) + (1084813557812647 / 3099578942800301815 : ℝ) * x ^ 1 + ((-110657956) / 314095569445 : ℝ) * x ^ 2 + (1 / 56735 : ℝ) * x ^ 3

noncomputable def Ap6 : ℝ → ℝ := fun x => (26702597727305802136943 / 1729078416188548765385045 : ℝ) * x ^ 1 + (1084813557812647 / 6199157885600603630 : ℝ) * x ^ 2 + ((-110657956) / 942286708335 : ℝ) * x ^ 3 + (1 / 226940 : ℝ) * x ^ 4

noncomputable def p7 : ℝ → ℝ := fun x => ((-7314389810938819776065) / 570311913506677694396352 : ℝ) + (17508029050835135 / 1534001979873198528 : ℝ) * x ^ 1 + ((-9017667892) / 5042874171159 : ℝ) * x ^ 2 + (341 / 4295417 : ℝ) * x ^ 3

noncomputable def Ap7 : ℝ → ℝ := fun x => ((-7314389810938819776065) / 570311913506677694396352 : ℝ) * x ^ 1 + (17508029050835135 / 3068003959746397056 : ℝ) * x ^ 2 + ((-9017667892) / 15128622513477 : ℝ) * x ^ 3 + (341 / 17181668 : ℝ) * x ^ 4

noncomputable def p8 : ℝ → ℝ := fun x => ((-259265866236876957957494) / 2214591288276800101250285 : ℝ) + (11231805963589071 / 235730663966330395 : ℝ) * x ^ 1 + ((-123296088867) / 20687201752201 : ℝ) * x ^ 2 + (2046 / 8585009 : ℝ) * x ^ 3

noncomputable def Ap8 : ℝ → ℝ := fun x => ((-259265866236876957957494) / 2214591288276800101250285 : ℝ) * x ^ 1 + (11231805963589071 / 471461327932660790 : ℝ) * x ^ 2 + ((-41098696289) / 20687201752201 : ℝ) * x ^ 3 + (1023 / 17170018 : ℝ) * x ^ 4

noncomputable def p9 : ℝ → ℝ := fun x => (14468960144364444280362143 / 51138417589432598261540762 : ℝ) + ((-264042652470397146) / 3403551169751184209 : ℝ) * x ^ 1 + (51561383827 / 7203564943286 : ℝ) * x ^ 2 + ((-1691) / 7619679 : ℝ) * x ^ 3

noncomputable def Ap9 : ℝ → ℝ := fun x => (14468960144364444280362143 / 51138417589432598261540762 : ℝ) * x ^ 1 + ((-132021326235198573) / 3403551169751184209 : ℝ) * x ^ 2 + (51561383827 / 21610694829858 : ℝ) * x ^ 3 + ((-1691) / 30478716 : ℝ) * x ^ 4

noncomputable def p10 : ℝ → ℝ := fun x => (0 : ℝ) + (0 : ℝ) * x ^ 1 + (0 : ℝ) * x ^ 2 + (0 : ℝ) * x ^ 3

noncomputable def Ap10 : ℝ → ℝ := fun x => (0 : ℝ) + (0 : ℝ) * x ^ 1 + (0 : ℝ) * x ^ 2 + (0 : ℝ) * x ^ 3 + (0 : ℝ) * x ^ 4

noncomputable def q1 : ℝ → ℝ := fun x => (297128594555764925 / 14562538337111819197 : ℝ) + ((-6982344559) / 3570007781582 : ℝ) * x ^ 1 + ((-15) / 7642118 : ℝ) * x ^ 2

noncomputable def Aq1 : ℝ → ℝ := fun x => (297128594555764925 / 14562538337111819197 : ℝ) * x ^ 1 + ((-6982344559) / 7140015563164 : ℝ) * x ^ 2 + ((-5) / 7642118 : ℝ) * x ^ 3

noncomputable def q2 : ℝ → ℝ := fun x => (1020500666855047196 / 50015972048399079315 : ℝ) + ((-10219071277) / 5225232451035 : ℝ) * x ^ 1 + ((-5) / 2513019 : ℝ) * x ^ 2

noncomputable def Aq2 : ℝ → ℝ := fun x => (1020500666855047196 / 50015972048399079315 : ℝ) * x ^ 1 + ((-10219071277) / 10450464902070 : ℝ) * x ^ 2 + ((-5) / 7539057 : ℝ) * x ^ 3

noncomputable def q3 : ℝ → ℝ := fun x => (5692702145064992493514827 / 279060526729026475990000000 : ℝ) + ((-63388855984969179) / 32469614826230000000 : ℝ) * x ^ 1 + ((-28561907) / 9513230000000 : ℝ) * x ^ 2 + (1 / 10000000 : ℝ) * x ^ 3

noncomputable def Aq3 : ℝ → ℝ := fun x => (5692702145064992493514827 / 279060526729026475990000000 : ℝ) * x ^ 1 + ((-63388855984969179) / 64939229652460000000 : ℝ) * x ^ 2 + ((-28561907) / 28539690000000 : ℝ) * x ^ 3 + (1 / 40000000 : ℝ) * x ^ 4

noncomputable def q4 : ℝ → ℝ := fun x => (31006761299055001099555153 / 1521831088435138886195186604 : ℝ) + ((-1353768967074474383) / 699128972572974005868 : ℝ) * x ^ 1 + ((-528402350) / 83830786167687 : ℝ) * x ^ 2 + (3 / 9355487 : ℝ) * x ^ 3

noncomputable def Aq4 : ℝ → ℝ := fun x => (31006761299055001099555153 / 1521831088435138886195186604 : ℝ) * x ^ 1 + ((-1353768967074474383) / 1398257945145948011736 : ℝ) * x ^ 2 + ((-528402350) / 251492358503061 : ℝ) * x ^ 3 + (3 / 37421948 : ℝ) * x ^ 4

noncomputable def q5 : ℝ → ℝ := fun x => (43284550441897845851521065 / 2136682619593188309089560004 : ℝ) + ((-643134953081334787) / 343275329809864102396 : ℝ) * x ^ 1 + ((-622549871) / 35733975814892 : ℝ) * x ^ 2 + (7 / 7251788 : ℝ) * x ^ 3

noncomputable def Aq5 : ℝ → ℝ := fun x => (43284550441897845851521065 / 2136682619593188309089560004 : ℝ) * x ^ 1 + ((-643134953081334787) / 686550659619728204792 : ℝ) * x ^ 2 + ((-622549871) / 107201927444676 : ℝ) * x ^ 3 + (7 / 29007152 : ℝ) * x ^ 4

noncomputable def q6 : ℝ → ℝ := fun x => (2160972509147275109431111 / 115615673898624078852766558 : ℝ) + ((-19132008903069274) / 16748316761405068439 : ℝ) * x ^ 1 + ((-759535654) / 5816349750927 : ℝ) * x ^ 2 + (50 / 7386903 : ℝ) * x ^ 3

noncomputable def Aq6 : ℝ → ℝ := fun x => (2160972509147275109431111 / 115615673898624078852766558 : ℝ) * x ^ 1 + ((-9566004451534637) / 16748316761405068439 : ℝ) * x ^ 2 + ((-759535654) / 17449049252781 : ℝ) * x ^ 3 + (25 / 14773806 : ℝ) * x ^ 4

noncomputable def q7 : ℝ → ℝ := fun x => (1450797220249839716 / 823225591571273909667 : ℝ) + (6008979118625749 / 1056772261323843273 : ℝ) * x ^ 1 + ((-418578133) / 400502028267 : ℝ) * x ^ 2 + (469 / 9891137 : ℝ) * x ^ 3

noncomputable def Aq7 : ℝ → ℝ := fun x => (1450797220249839716 / 823225591571273909667 : ℝ) * x ^ 1 + (6008979118625749 / 2113544522647686546 : ℝ) * x ^ 2 + ((-418578133) / 1201506084801 : ℝ) * x ^ 3 + (469 / 39564548 : ℝ) * x ^ 4

noncomputable def q8 : ℝ → ℝ := fun x => ((-915628915145509543957177) / 20038035551301576706873941 : ℝ) + (856803642146560571 / 37685102113885569567 : ℝ) * x ^ 1 + ((-37020948502) / 12058194707043 : ℝ) * x ^ 2 + (550 / 4336317 : ℝ) * x ^ 3

noncomputable def Aq8 : ℝ → ℝ := fun x => ((-915628915145509543957177) / 20038035551301576706873941 : ℝ) * x ^ 1 + (856803642146560571 / 75370204227771139134 : ℝ) * x ^ 2 + ((-37020948502) / 36174584121129 : ℝ) * x ^ 3 + (275 / 8672634 : ℝ) * x ^ 4

noncomputable def q9 : ℝ → ℝ := fun x => (359800696925351319491961 / 1065135312455955859577224 : ℝ) + ((-1071533859453710345) / 11306008715906250168 : ℝ) * x ^ 1 + (69000054801 / 7708798234264 : ℝ) * x ^ 2 + ((-2197) / 7732488 : ℝ) * x ^ 3

noncomputable def Aq9 : ℝ → ℝ := fun x => (359800696925351319491961 / 1065135312455955859577224 : ℝ) * x ^ 1 + ((-1071533859453710345) / 22612017431812500336 : ℝ) * x ^ 2 + (23000018267 / 7708798234264 : ℝ) * x ^ 3 + ((-2197) / 30929952 : ℝ) * x ^ 4

lemma p1_integral (a b : ℝ) : ∫ t in a..b, p1 t = Ap1 b - Ap1 a := by
  unfold p1 Ap1
  have i0 : IntervalIntegrable (fun _t : ℝ => (1395223692374691958 / 67989770008801522607 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-16507902491) / 8406920828251 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-4) / 2032313 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p2_integral (a b : ℝ) : ∫ t in a..b, p2 t = Ap2 b - Ap2 a := by
  unfold p2 Ap2
  have i0 : IntervalIntegrable (fun _t : ℝ => (4072233538158690685629569 / 198429743739822271336250000 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-317078814294886157) / 161347885321797500000 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-47683729) / 37193785000000 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => ((-1) / 10000000 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p3_integral (a b : ℝ) : ∫ t in a..b, p3 t = Ap3 b - Ap3 a := by
  unfold p3 Ap3
  have i0 : IntervalIntegrable (fun _t : ℝ => (1842892121146437672567071 / 89776018778735789932485326 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-3368288840463565) / 1710144131821267306 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-7892819) / 49048311818058 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => ((-1) / 5505026 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p4_integral (a b : ℝ) : ∫ t in a..b, p4 t = Ap4 b - Ap4 a := by
  unfold p4 Ap4
  have i0 : IntervalIntegrable (fun _t : ℝ => (49788592698436741 / 2427539499487824769 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-894817124) / 456907242749 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-5) / 1945456 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p5_integral (a b : ℝ) : ∫ t in a..b, p5 t = Ap5 b - Ap5 a := by
  unfold p5 Ap5
  have i0 : IntervalIntegrable (fun _t : ℝ => (89083109809413373372501186 / 4444250497018486792718454717 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-1577809460133826493) / 920053340422800467271 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-4212600001) / 93864134891959 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (23 / 9411313 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p6_integral (a b : ℝ) : ∫ t in a..b, p6 t = Ap6 b - Ap6 a := by
  unfold p6 Ap6
  have i0 : IntervalIntegrable (fun _t : ℝ => (26702597727305802136943 / 1729078416188548765385045 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (1084813557812647 / 3099578942800301815 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-110657956) / 314095569445 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (1 / 56735 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p7_integral (a b : ℝ) : ∫ t in a..b, p7 t = Ap7 b - Ap7 a := by
  unfold p7 Ap7
  have i0 : IntervalIntegrable (fun _t : ℝ => ((-7314389810938819776065) / 570311913506677694396352 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (17508029050835135 / 1534001979873198528 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-9017667892) / 5042874171159 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (341 / 4295417 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p8_integral (a b : ℝ) : ∫ t in a..b, p8 t = Ap8 b - Ap8 a := by
  unfold p8 Ap8
  have i0 : IntervalIntegrable (fun _t : ℝ => ((-259265866236876957957494) / 2214591288276800101250285 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (11231805963589071 / 235730663966330395 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-123296088867) / 20687201752201 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (2046 / 8585009 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p9_integral (a b : ℝ) : ∫ t in a..b, p9 t = Ap9 b - Ap9 a := by
  unfold p9 Ap9
  have i0 : IntervalIntegrable (fun _t : ℝ => (14468960144364444280362143 / 51138417589432598261540762 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-264042652470397146) / 3403551169751184209 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => (51561383827 / 7203564943286 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => ((-1691) / 7619679 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p10_integral (a b : ℝ) : ∫ t in a..b, p10 t = Ap10 b - Ap10 a := by
  unfold p10 Ap10
  simp

lemma q1_integral (a b : ℝ) : ∫ t in a..b, q1 t = Aq1 b - Aq1 a := by
  unfold q1 Aq1
  have i0 : IntervalIntegrable (fun _t : ℝ => (297128594555764925 / 14562538337111819197 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-6982344559) / 3570007781582 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-15) / 7642118 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q2_integral (a b : ℝ) : ∫ t in a..b, q2 t = Aq2 b - Aq2 a := by
  unfold q2 Aq2
  have i0 : IntervalIntegrable (fun _t : ℝ => (1020500666855047196 / 50015972048399079315 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-10219071277) / 5225232451035 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-5) / 2513019 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q3_integral (a b : ℝ) : ∫ t in a..b, q3 t = Aq3 b - Aq3 a := by
  unfold q3 Aq3
  have i0 : IntervalIntegrable (fun _t : ℝ => (5692702145064992493514827 / 279060526729026475990000000 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-63388855984969179) / 32469614826230000000 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-28561907) / 9513230000000 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (1 / 10000000 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q4_integral (a b : ℝ) : ∫ t in a..b, q4 t = Aq4 b - Aq4 a := by
  unfold q4 Aq4
  have i0 : IntervalIntegrable (fun _t : ℝ => (31006761299055001099555153 / 1521831088435138886195186604 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-1353768967074474383) / 699128972572974005868 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-528402350) / 83830786167687 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (3 / 9355487 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q5_integral (a b : ℝ) : ∫ t in a..b, q5 t = Aq5 b - Aq5 a := by
  unfold q5 Aq5
  have i0 : IntervalIntegrable (fun _t : ℝ => (43284550441897845851521065 / 2136682619593188309089560004 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-643134953081334787) / 343275329809864102396 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-622549871) / 35733975814892 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (7 / 7251788 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q6_integral (a b : ℝ) : ∫ t in a..b, q6 t = Aq6 b - Aq6 a := by
  unfold q6 Aq6
  have i0 : IntervalIntegrable (fun _t : ℝ => (2160972509147275109431111 / 115615673898624078852766558 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-19132008903069274) / 16748316761405068439 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-759535654) / 5816349750927 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (50 / 7386903 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q7_integral (a b : ℝ) : ∫ t in a..b, q7 t = Aq7 b - Aq7 a := by
  unfold q7 Aq7
  have i0 : IntervalIntegrable (fun _t : ℝ => (1450797220249839716 / 823225591571273909667 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (6008979118625749 / 1056772261323843273 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-418578133) / 400502028267 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (469 / 9891137 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q8_integral (a b : ℝ) : ∫ t in a..b, q8 t = Aq8 b - Aq8 a := by
  unfold q8 Aq8
  have i0 : IntervalIntegrable (fun _t : ℝ => ((-915628915145509543957177) / 20038035551301576706873941 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (856803642146560571 / 37685102113885569567 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => ((-37020948502) / 12058194707043 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (550 / 4336317 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma q9_integral (a b : ℝ) : ∫ t in a..b, q9 t = Aq9 b - Aq9 a := by
  unfold q9 Aq9
  have i0 : IntervalIntegrable (fun _t : ℝ => (359800696925351319491961 / 1065135312455955859577224 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => ((-1071533859453710345) / 11306008715906250168 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => (69000054801 / 7708798234264 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => ((-2197) / 7732488 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma p1_nonneg : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ p1 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 := pow_nonneg hxl _
  have key : p1 x
      = (150065 / 8087357 : ℝ) * ((2 - x) ^ 3) + (1796465793642 / 33454379324839 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 2) + (3517074033156149591 / 67989770008801522607 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 1) + (1127677820773681960 / 67989770008801522607 : ℝ) * ((x - 1) ^ 3) := by
    unfold p1; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p1_cap : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ 1 - p1 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 := pow_nonneg hxl _
  have key : 1 - p1 x
      = (7937292 / 8087357 : ℝ) * ((2 - x) ^ 3) + (98566672180875 / 33454379324839 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 2) + (200452235993248418230 / 67989770008801522607 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 1) + (66862092188027840647 / 67989770008801522607 : ℝ) * ((x - 1) ^ 3) := by
    unfold p1; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p2_nonneg : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ p2 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 := pow_nonneg hxl _
  have key : p2 x
      = (163183 / 9838604 : ℝ) * ((3 - x) ^ 3) + (4079070602363 / 85360387490468 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 2) + (29090156583658841299 / 634975179967431268276 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 1) + (23196427193764035854682931 / 1587437949918578170690000000 : ℝ) * ((x - 2) ^ 3) := by
    unfold p2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p2_cap : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ 1 - p2 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 := pow_nonneg hxl _
  have key : 1 - p2 x
      = (9675421 / 9838604 : ℝ) * ((3 - x) ^ 3) + (252002091869041 / 85360387490468 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 2) + (1875835383318634963529 / 634975179967431268276 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 1) + (1564241522724814134835317069 / 1587437949918578170690000000 : ℝ) * ((x - 2) ^ 3) := by
    unfold p2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p3_nonneg : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ p3 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 := pow_nonneg hxl _
  have key : p3 x
      = (109586 / 7499453 : ℝ) * ((4 - x) ^ 3) + (1609077387657 / 38437538917687 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 2) + (1951328770784812352 / 48924029847671449653 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 1) + (486140654420589384763711 / 38475436619458195685350854 : ℝ) * ((x - 3) ^ 3) := by
    unfold p3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p3_cap : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ 1 - p3 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 := pow_nonneg hxl _
  have key : 1 - p3 x
      = (7389867 / 7499453 : ℝ) * ((4 - x) ^ 3) + (113703539365404 / 38437538917687 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 2) + (144820760772229536607 / 48924029847671449653 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 1) + (37989295965037606300587143 / 38475436619458195685350854 : ℝ) * ((x - 3) ^ 3) := by
    unfold p3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p4_nonneg : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ p4 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 := pow_nonneg hxl _
  have key : p4 x
      = (67130 / 5312981 : ℝ) * ((5 - x) ^ 3) + (1434522148007 / 39929591819918 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 2) + (1318435102118018637 / 38840631991805196304 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 1) + (413790173423311461 / 38840631991805196304 : ℝ) * ((x - 4) ^ 3) := by
    unfold p4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p4_cap : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ 1 - p4 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 := pow_nonneg hxl _
  have key : 1 - p4 x
      = (5245851 / 5312981 : ℝ) * ((5 - x) ^ 3) + (118354253311747 / 39929591819918 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 2) + (115203460873297570275 / 38840631991805196304 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 1) + (38426841818381884843 / 38840631991805196304 : ℝ) * ((x - 4) ^ 3) := by
    unfold p4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p5_nonneg : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ p5 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 := pow_nonneg hxl _
  have key : p5 x
      = (51461 / 4830427 : ℝ) * ((6 - x) ^ 3) + (1419489131203 / 47347695710763 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 2) + (13218251714359261931 / 472224279122210343309 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 1) + (38519711017631074985057764 / 4444250497018486792718454717 : ℝ) * ((x - 5) ^ 3) := by
    unfold p5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p5_cap : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ 1 - p5 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 := pow_nonneg hxl _
  have key : 1 - p5 x
      = (4778966 / 4830427 : ℝ) * ((6 - x) ^ 3) + (140623598001086 / 47347695710763 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 2) + (1403454585652271767996 / 472224279122210343309 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 1) + (4405730786000855717733396953 / 4444250497018486792718454717 : ℝ) * ((x - 5) ^ 3) := by
    unfold p5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p6_nonneg : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ p6 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 := pow_nonneg hxl _
  have key : p6 x
      = (4835 / 557843 : ℝ) * ((7 - x) ^ 3) + (132271873352 / 5504943668081 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 2) + (671050243075009789 / 30476397570962347147 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 1) + (11542966744817741071947 / 1729078416188548765385045 : ℝ) * ((x - 6) ^ 3) := by
    unfold p6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p6_cap : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ 1 - p6 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 := pow_nonneg hxl _
  have key : 1 - p6 x
      = (553008 / 557843 : ℝ) * ((7 - x) ^ 3) + (16382559130891 / 5504943668081 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 2) + (90758142469812031652 / 30476397570962347147 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 1) + (1717535449443731024313098 / 1729078416188548765385045 : ℝ) * ((x - 6) ^ 3) := by
    unfold p6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p7_nonneg : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ p7 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 := pow_nonneg hxl _
  have key : p7 x
      = (34747 / 5204926 : ℝ) * ((8 - x) ^ 3) + (42928930805 / 2374945274688 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 2) + (52056661844125903 / 3252918606252571872 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 1) + (18693341420917787092801 / 3992183394546743860774464 : ℝ) * ((x - 7) ^ 3) := by
    unfold p7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p7_cap : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ 1 - p7 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 := pow_nonneg hxl _
  have key : 1 - p7 x
      = (5170179 / 5204926 : ℝ) * ((8 - x) ^ 3) + (7081906893259 / 2374945274688 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 2) + (9706699156913589713 / 3252918606252571872 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 1) + (3973490053125826073681663 / 3992183394546743860774464 : ℝ) * ((x - 7) ^ 3) := by
    unfold p7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p8_nonneg : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ p8 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 := pow_nonneg hxl _
  have key : p8 x
      = (43990 / 9394583 : ℝ) * ((9 - x) ^ 3) + (350795411913 / 29010895060235 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 2) + (691799514299954199 / 69907234706802616915 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 1) + (6034588212971746780258 / 2214591288276800101250285 : ℝ) * ((x - 8) ^ 3) := by
    unfold p8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p8_cap : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ 1 - p8 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 := pow_nonneg hxl _
  have key : 1 - p8 x
      = (9350593 / 9394583 : ℝ) * ((9 - x) ^ 3) + (86681889768792 / 29010895060235 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 2) + (209029904606107896546 / 69907234706802616915 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 1) + (2208556700063828354470027 / 2214591288276800101250285 : ℝ) * ((x - 8) ^ 3) := by
    unfold p8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p9_nonneg : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ p9 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 := pow_nonneg hxl _
  have key : p9 x
      = (20471 / 7512509 : ℝ) * ((10 - x) ^ 3) + (39101490039 / 7099043042167 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 2) + (242031696229110127 / 60402250318536172502 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 1) + (461166249853577650298867 / 460245758304893384353866858 : ℝ) * ((x - 9) ^ 3) := by
    unfold p9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p9_cap : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ 1 - p9 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 := pow_nonneg hxl _
  have key : 1 - p9 x
      = (7492038 / 7512509 : ℝ) * ((10 - x) ^ 3) + (21258027636462 / 7099043042167 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 2) + (180964719259379407379 / 60402250318536172502 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 1) + (459784592055039806703567991 / 460245758304893384353866858 : ℝ) * ((x - 9) ^ 3) := by
    unfold p9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma p10_nonneg : ∀ x : ℝ, (10:ℝ) ≤ x → x ≤ 11 → 0 ≤ p10 x := by
  intro x h0 h1
  have key : p10 x = (0 : ℝ) := by
    unfold p10; ring
  linarith

lemma p10_cap : ∀ x : ℝ, (10:ℝ) ≤ x → x ≤ 11 → 0 ≤ 1 - p10 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 10 := by linarith
  have hxr : (0:ℝ) ≤ 11 - x := by linarith
  have hT0 : (0:ℝ) ≤ (11 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 10) ^ 1 * (11 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 10) ^ 2 * (11 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 10) ^ 3 := pow_nonneg hxl _
  have key : 1 - p10 x
      = (1 : ℝ) * ((11 - x) ^ 3) + (3 : ℝ) * ((x - 10) ^ 1 * (11 - x) ^ 2) + (3 : ℝ) * ((x - 10) ^ 2 * (11 - x) ^ 1) + (1 : ℝ) * ((x - 10) ^ 3) := by
    unfold p10; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q1_cap : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ 1 - q1 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 := pow_nonneg hxl _
  have key : 1 - q1 x
      = (8007781 / 8158267 : ℝ) * ((2 - x) ^ 3) + (22459899105091 / 7622252541566 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 2) + (85877734946480415857 / 29125076674223638394 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 1) + (14322487907542497015 / 14562538337111819197 : ℝ) * ((x - 1) ^ 3) := by
    unfold q1; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q1_floor : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ q1 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 := pow_nonneg hxl _
  have key : q1 x + 1
      = (8308753 / 8158267 : ℝ) * ((2 - x) ^ 3) + (23273616144305 / 7622252541566 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 2) + (88872725098861414507 / 29125076674223638394 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 1) + (14802588766681141379 / 14562538337111819197 : ℝ) * ((x - 1) ^ 3) := by
    unfold q1; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q2_cap : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ 1 - q2 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 := pow_nonneg hxl _
  have key : 1 - q2 x
      = (9414223 / 9572009 : ℝ) * ((3 - x) ^ 3) + (58763075671032 / 19902743293385 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 2) + (147771040270558585726 / 50015972048399079315 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 1) + (49289818131697490923 / 50015972048399079315 : ℝ) * ((x - 2) ^ 3) := by
    unfold q2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q2_floor : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ q2 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 := pow_nonneg hxl _
  have key : q2 x + 1
      = (9729795 / 9572009 : ℝ) * ((3 - x) ^ 3) + (60653384089278 / 19902743293385 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 2) + (152324792019835890164 / 50015972048399079315 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 1) + (50742125965100667707 / 50015972048399079315 : ℝ) * ((x - 2) ^ 3) := by
    unfold q2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q3_cap : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ 1 - q3 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 := pow_nonneg hxl _
  have key : 1 - q3 x
      = (8469734 / 8594513 : ℝ) * ((4 - x) ^ 3) + (173563778414907 / 58667881829626 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 2) + (82612572842699104741 / 27906052672902647599 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 1) + (275558629316539837522352401 / 279060526729026475990000000 : ℝ) * ((x - 3) ^ 3) := by
    unfold q3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q3_floor : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ q3 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 := pow_nonneg hxl _
  have key : q3 x + 1
      = (8719292 / 8594513 : ℝ) * ((4 - x) ^ 3) + (178443512562849 / 58667881829626 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 2) + (84823743194716780853 / 27906052672902647599 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 1) + (282562424141513114457647599 / 279060526729026475990000000 : ℝ) * ((x - 3) ^ 3) := by
    unfold q3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q4_cap : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ 1 - q4 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 := pow_nonneg hxl _
  have key : 1 - q4 x
      = (8597749 / 8707012 : ℝ) * ((5 - x) ^ 3) + (13453296547375 / 4538401576573 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 2) + (482519571315558347797 / 162667222821766401492 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 1) + (752868620217643763596409473 / 760915544217569443097593302 : ℝ) * ((x - 4) ^ 3) := by
    unfold q4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q4_floor : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ q4 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 := pow_nonneg hxl _
  have key : q4 x + 1
      = (8816275 / 8707012 : ℝ) * ((5 - x) ^ 3) + (13777112912063 / 4538401576573 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 2) + (493483765615040061155 / 162667222821766401492 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 1) + (768962468217495122598777131 / 760915544217569443097593302 : ℝ) * ((x - 4) ^ 3) := by
    unfold q4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q5_cap : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ 1 - q5 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 := pow_nonneg hxl _
  have key : 1 - q5 x
      = (6158574 / 6224399 : ℝ) * ((6 - x) ^ 3) + (177603530200610 / 59794147470787 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 2) + (1751487282871670058235 / 589284358448754516566 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 1) + (2118311435725852011056988293 / 2136682619593188309089560004 : ℝ) * ((x - 5) ^ 3) := by
    unfold q5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q5_floor : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ q5 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 := pow_nonneg hxl _
  have key : q5 x + 1
      = (6290224 / 6224399 : ℝ) * ((6 - x) ^ 3) + (181161354624112 / 59794147470787 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 2) + (1784218867820857041161 / 589284358448754516566 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 1) + (2155053803460524607122131715 / 2136682619593188309089560004 : ℝ) * ((x - 5) ^ 3) := by
    unfold q5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q6_cap : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ 1 - q6 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 := pow_nonneg hxl _
  have key : 1 - q6 x
      = (6843769 / 6903122 : ℝ) * ((7 - x) ^ 3) + (177479127597277 / 59633109518662 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 2) + (1258542185892522294661 / 422588897574917408422 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 1) + (3100965301249560795201049729 / 3121623195262850129024697066 : ℝ) * ((x - 6) ^ 3) := by
    unfold q6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q6_floor : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ q6 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 := pow_nonneg hxl _
  have key : q6 x + 1
      = (6962475 / 6903122 : ℝ) * ((7 - x) ^ 3) + (180319529514695 / 59633109518662 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 2) + (1276991199556982155871 / 422588897574917408422 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 1) + (3142281089276139462848344403 / 3121623195262850129024697066 : ℝ) * ((x - 6) ^ 3) := by
    unfold q6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q7_cap : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ 1 - q7 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 := pow_nonneg hxl _
  have key : 1 - q7 x
      = (6562978 / 6606699 : ℝ) * ((8 - x) ^ 3) + (202280287400 / 67830978633 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 2) + (248366444089196 / 83228610782691 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 1) + (819405683946719288647 / 823225591571273909667 : ℝ) * ((x - 7) ^ 3) := by
    unfold q7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q7_floor : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ q7 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 := pow_nonneg hxl _
  have key : q7 x + 1
      = (6650420 / 6606699 : ℝ) * ((8 - x) ^ 3) + (204705584398 / 67830978633 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 2) + (251005220606950 / 83228610782691 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 1) + (827045499195828530687 / 823225591571273909667 : ℝ) * ((x - 7) ^ 3) := by
    unfold q7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q8_cap : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ 1 - q8 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 := pow_nonneg hxl _
  have key : 1 - q8 x
      = (1234930 / 1240687 : ℝ) * ((9 - x) ^ 3) + (1655193552449 / 553925802829 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 2) + (13817539982322901138 / 4620980327614788473 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 1) + (19983809221744199997791665 / 20038035551301576706873941 : ℝ) * ((x - 8) ^ 3) := by
    unfold q8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q8_floor : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ q8 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 := pow_nonneg hxl _
  have key : q8 x + 1
      = (1246444 / 1240687 : ℝ) * ((9 - x) ^ 3) + (1668361264525 / 553925802829 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 2) + (13908341983365829700 / 4620980327614788473 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 1) + (20092261880858953415956217 / 20038035551301576706873941 : ℝ) * ((x - 8) ^ 3) := by
    unfold q8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q9_cap : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ 1 - q9 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 := pow_nonneg hxl _
  have key : 1 - q9 x
      = (5355419 / 5369951 : ℝ) * ((10 - x) ^ 3) + (23584658823424 / 7875768824787 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 2) + (7428500327928103789 / 2479465292957092914 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 1) + (3192216922242343343661539 / 3195405937367867578731672 : ℝ) * ((x - 9) ^ 3) := by
    unfold q9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma q9_floor : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ q9 x + 1 := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 3 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 := pow_nonneg hxl _
  have key : q9 x + 1
      = (5384483 / 5369951 : ℝ) * ((10 - x) ^ 3) + (23669954125298 / 7875768824787 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 2) + (7448291429814453695 / 2479465292957092914 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 1) + (3198594952493391813801805 / 3195405937367867578731672 : ℝ) * ((x - 9) ^ 3) := by
    unfold q9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3]

lemma drift_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ p1 x - (1 / 1000 + 999 / 1000 * ((Ap1 2 - Ap1 x) + (Ap2 (x + 1) - Ap2 2))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 1) ^ 4 := pow_nonneg hxl _
  have key : p1 x - (1 / 1000 + 999 / 1000 * ((Ap1 2 - Ap1 x) + (Ap2 (x + 1) - Ap2 2)))
      = (271914461805792513 / 135979540017603045214000 : ℝ) * ((2 - x) ^ 4) + (214020696618207042672021 / 26756976926706987821092825120 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 3) + (69719246137696571477184219157069 / 5803633113339097892599634099010076000 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 2) + (345374585156529169601580351541833248281 / 43171816447283007822260776351449895915532000 : ℝ) * ((x - 1) ^ 3 * (2 - x) ^ 1) + (868166720148034088291657227579287548794904117 / 431718164472830078222607763514498959155320000000000 : ℝ) * ((x - 1) ^ 4) := by
    unfold p1 Ap1 Ap2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ p2 x - (1 / 1000 + 999 / 1000 * ((Ap2 3 - Ap2 x) + (Ap3 (x + 1) - Ap3 3))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 2) ^ 4 := pow_nonneg hxl _
  have key : p2 x - (1 / 1000 + 999 / 1000 * ((Ap2 3 - Ap2 x) + (Ap3 (x + 1) - Ap3 3)))
      = (12760736376240652429251931 / 6349751799674312682760000000000 : ℝ) * ((3 - x) ^ 4) + (1615948594734840998444179138877 / 201778242302215776574841230000000000 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 3) + (1471473907399895756080481611827759410791 / 122034415958817230577595213891988060000000000 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 2) + (207102631715932353384426780570790921684990981 / 25887953881047631434424027091797725090190000000000 : ℝ) * ((x - 2) ^ 3 * (3 - x) ^ 1) + (139762489016792385166944488460322750459681126503 / 71256929600984059142460782082525431681174147470000000 : ℝ) * ((x - 2) ^ 4) := by
    unfold p2 Ap2 Ap3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ p3 x - (1 / 1000 + 999 / 1000 * ((Ap3 4 - Ap3 x) + (Ap4 (x + 1) - Ap4 4))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 3) ^ 4 := pow_nonneg hxl _
  have key : p3 x - (1 / 1000 + 999 / 1000 * ((Ap3 4 - Ap3 x) + (Ap4 (x + 1) - Ap4 4)))
      = (718208149980626075069157 / 359104075114943159729941304000 : ℝ) * ((4 - x) ^ 4) + (152633050527588233025014164977 / 19079131281082658237251432792672240 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 3) + (2473850576228929280232645439951289963 / 206810756829935385812858543685298241727000 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 2) + (41843487943351621539724978444604588839368739 / 5230435960611404087245226902529732490044152656000 : ℝ) * ((x - 3) ^ 3 * (4 - x) ^ 1) + (1488976354446234389453778490944027381882113 / 747205137230200583892175271789961784292021808000 : ℝ) * ((x - 3) ^ 4) := by
    unfold p3 Ap3 Ap4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ p4 x - (1 / 1000 + 999 / 1000 * ((Ap4 5 - Ap4 x) + (Ap5 (x + 1) - Ap5 5))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 4) ^ 4 := pow_nonneg hxl _
  have key : p4 x - (1 / 1000 + 999 / 1000 * ((Ap4 5 - Ap4 x) + (Ap5 (x + 1) - Ap5 5)))
      = (77398802224571019 / 38840631991805196304000 : ℝ) * ((5 - x) ^ 4) + (402838625747900671435189 / 46904209367569899741785452000 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 3) + (3664654924095124041234330084763 / 306502404126953175068059336769992000 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 2) + (48910816369033847176667609740347624211 / 6113829814327089901055635443653992643312000 : ℝ) * ((x - 4) ^ 3 * (5 - x) ^ 1) + (29188445677644931651818516295178652067357351 / 14384791502841031859493403893530397116476647164000 : ℝ) * ((x - 4) ^ 4) := by
    unfold p4 Ap4 Ap5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ p5 x - (1 / 1000 + 999 / 1000 * ((Ap5 6 - Ap5 x) + (Ap6 (x + 1) - Ap6 6))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 5) ^ 4 := pow_nonneg hxl _
  have key : p5 x - (1 / 1000 + 999 / 1000 * ((Ap5 6 - Ap5 x) + (Ap6 (x + 1) - Ap6 6)))
      = (11851334691975067015082729 / 5925667329357982390291272956000 : ℝ) * ((6 - x) ^ 4) + (29233884384936546619064971359503 / 2479194030008283727910440934695431000 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 3) + (559207981475607824865833937349452169 / 46600664062719535311953491869150622453480 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 2) + (180593000311184814702647090419666501199315979 / 22574124175347069153506813300427270493525607066500 : ℝ) * ((x - 5) ^ 3 * (6 - x) ^ 1) + (8782237501363533288177987129474880792946459940287 / 4391118634588511891740145323199112656400601086575580000 : ℝ) * ((x - 5) ^ 4) := by
    unfold p5 Ap5 Ap6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ p6 x - (1 / 1000 + 999 / 1000 * ((Ap6 7 - Ap6 x) + (Ap7 (x + 1) - Ap7 7))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 6) ^ 4 := pow_nonneg hxl _
  have key : p6 x - (1 / 1000 + 999 / 1000 * ((Ap6 7 - Ap6 x) + (Ap7 (x + 1) - Ap7 7)))
      = (13832627349323137686477 / 6916313664754195061540180000 : ℝ) * ((7 - x) ^ 4) + (210817148998714865678412633167 / 8999725204458598371220520731670000 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 3) + (32818912782669301383045400797731 / 2734909499894775180557754887520640000 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 2) + (11805433291835203180845305918747221301 / 1475679221222473686336318641291843005760000 : ℝ) * ((x - 6) ^ 3 * (7 - x) ^ 1) + (1593719642248082175212263122534294962393121 / 796859814254211620545812558873608325611412812800 : ℝ) * ((x - 6) ^ 4) := by
    unfold p6 Ap6 Ap7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ p7 x - (1 / 1000 + 999 / 1000 * ((Ap7 8 - Ap7 x) + (Ap8 (x + 1) - Ap8 8))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 7) ^ 4 := pow_nonneg hxl _
  have key : p7 x - (1 / 1000 + 999 / 1000 * ((Ap7 8 - Ap7 x) + (Ap8 (x + 1) - Ap8 8)))
      = (354860750547912486173 / 177430373090966393812198400 : ℝ) * ((8 - x) ^ 4) + (27102479091083663762507462491 / 568256034110471705754335550432000 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 3) + (252691231863053119293847617562533197 / 21057602458256059183153765498005425280000 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 2) + (202969093415812394934335631276962287869673 / 25371136505016292498497307014561597618768960000 : ℝ) * ((x - 7) ^ 3 * (8 - x) ^ 1) + (200933059258751844582138831112431114665737307 / 100466529167801391257487023614287106370622735480000 : ℝ) * ((x - 7) ^ 4) := by
    unfold p7 Ap7 Ap8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ p8 x - (1 / 1000 + 999 / 1000 * ((Ap8 9 - Ap8 x) + (Ap9 (x + 1) - Ap9 9))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 8) ^ 4 := pow_nonneg hxl _
  have key : p8 x - (1 / 1000 + 999 / 1000 * ((Ap8 9 - Ap8 x) + (Ap9 (x + 1) - Ap9 9)))
      = (2214591297305064252847 / 1107295644138400050625142500 : ℝ) * ((9 - x) ^ 4) + (133097095451265949052543871769 / 16637136984501055251843677315065000 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 3) + (72574279279708265992676576518936461 / 571690140955820751779925703515482458000 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 2) + (1070130350657675941192124956384878498399361 / 133766297347744781539710234517681848636663070000 : ℝ) * ((x - 8) ^ 3 * (9 - x) ^ 1) + (18120110198793722230198341414084005300273176013 / 9060055527185480971179713244795160095448535329373600 : ℝ) * ((x - 8) ^ 4) := by
    unfold p8 Ap8 Ap9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma drift_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ p9 x - (1 / 1000 + 999 / 1000 * ((Ap9 10 - Ap9 x) + (Ap10 (x + 1) - Ap10 10))) := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 9) ^ 4 := pow_nonneg hxl _
  have key : p9 x - (1 / 1000 + 999 / 1000 * ((Ap9 10 - Ap9 x) + (Ap10 (x + 1) - Ap10 10)))
      = (40910733455688241070469 / 20455367035773039304616304800 : ℝ) * ((10 - x) ^ 4) + (810874508461522646304453 / 12784604397358149565385190500 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 3) + (613661011549802418182641 / 51138417589432598261540762000 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 2) + (736393224321932724812887 / 92049151660978676870773371600 : ℝ) * ((x - 9) ^ 3 * (10 - x) ^ 1) + (460245774342132972500071 / 230122879152446692176933429000 : ℝ) * ((x - 9) ^ 4) := by
    unfold p9 Ap9 Ap10; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x ≤ 2 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq1 2 - Aq1 x) + (Aq2 (x + 1) - Aq2 2)) - q1 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 1 := by linarith
  have hxr : (0:ℝ) ≤ 2 - x := by linarith
  have hT0 : (0:ℝ) ≤ (2 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 1) ^ 1 * (2 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 1) ^ 2 * (2 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 1) ^ 3 * (2 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 1) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq1 2 - Aq1 x) + (Aq2 (x + 1) - Aq2 2)) - q1 x
      = (116520993507556657 / 58250153348447276788000 : ℝ) * ((2 - x) ^ 4) + (222998181628234668637881 / 27878549605135873472011354600 : ℝ) * ((x - 1) ^ 1 * (2 - x) ^ 3) + (1070348036130204774980998784961 / 89179834530342833776587214188260000 : ℝ) * ((x - 1) ^ 2 * (2 - x) ^ 2) + (44142992053093267916412915865623493 / 5517875078960036044180436585905625833750 : ℝ) * ((x - 1) ^ 3 * (2 - x) ^ 1) + (969411897452998674868238486672049447 / 485573006948483171887878419559695073370000 : ℝ) * ((x - 1) ^ 4) := by
    unfold q1 Aq1 Aq2; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x ≤ 3 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq2 3 - Aq2 x) + (Aq3 (x + 1) - Aq3 3)) - q2 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 2 := by linarith
  have hxr : (0:ℝ) ≤ 3 - x := by linarith
  have hT0 : (0:ℝ) ≤ (3 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 2) ^ 1 * (3 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 2) ^ 2 * (3 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 2) ^ 3 * (3 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 2) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq2 3 - Aq2 x) + (Aq3 (x + 1) - Aq3 3)) - q2 x
      = (66616300913643251 / 33343981365599386210000 : ℝ) * ((3 - x) ^ 4) + (1142865897175987209237941 / 143287640659200838786932865000 : ℝ) * ((x - 2) ^ 1 * (3 - x) ^ 3) + (14069654457877882788544341614767 / 1173732455091741700954846436314476000 : ℝ) * ((x - 2) ^ 2 * (3 - x) ^ 2) + (22331998383589176045344285100598004929 / 2791496700938102475443668440834990629370000 : ℝ) * ((x - 2) ^ 3 * (3 - x) ^ 1) + (22511226300833477723304753545740297513874063 / 11165986803752409901774673763339962517480000000000 : ℝ) * ((x - 2) ^ 4) := by
    unfold q2 Aq2 Aq3; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x ≤ 4 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq3 4 - Aq3 x) + (Aq4 (x + 1) - Aq4 4)) - q3 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 3 := by linarith
  have hxr : (0:ℝ) ≤ 4 - x := by linarith
  have hT0 : (0:ℝ) ≤ (4 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 3) ^ 1 * (4 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 3) ^ 2 * (4 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 3) ^ 3 * (4 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 3) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq3 4 - Aq3 x) + (Aq4 (x + 1) - Aq4 4)) - q3 x
      = (2240798069663995394951401 / 1116242106916105903960000000000 : ℝ) * ((4 - x) ^ 4) + (4839662243497775295297314480953 / 607445838738988568690660470000000000 : ℝ) * ((x - 3) ^ 1 * (4 - x) ^ 3) + (30508924391716708298728356161682886319 / 2532977468932611130788948661964540000000000 : ℝ) * ((x - 3) ^ 2 * (4 - x) ^ 2) + (30262554390129606552697751003386755783015191 / 3782833406849170705193097361558019848090000000000 : ℝ) * ((x - 3) ^ 3 * (4 - x) ^ 1) + (1884461767120832443931685626695245979010108291 / 956493209755219661978779860967306876609404590000000 : ℝ) * ((x - 3) ^ 4) := by
    unfold q3 Aq3 Aq4; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x ≤ 5 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq4 5 - Aq4 x) + (Aq5 (x + 1) - Aq5 5)) - q4 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 4 := by linarith
  have hxr : (0:ℝ) ≤ 5 - x := by linarith
  have hT0 : (0:ℝ) ≤ (5 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 4) ^ 1 * (5 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 4) ^ 2 * (5 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 4) ^ 3 * (5 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 4) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq4 5 - Aq4 x) + (Aq5 (x + 1) - Aq5 5)) - q4 x
      = (54840760090872480932761 / 27420379971804304255769128000 : ℝ) * ((5 - x) ^ 4) + (18080077702423742370068246291 / 2306424130758361346017636548028000 : ℝ) * ((x - 4) ^ 1 * (5 - x) ^ 3) + (1595265311438829238345267323294297907 / 132938776519384933758487931785507821384000 : ℝ) * ((x - 4) ^ 2 * (5 - x) ^ 2) + (372886174485258642333997165192147624827653 / 46610772173382048730674945163717717650425118600 : ℝ) * ((x - 4) ^ 3 * (5 - x) ^ 1) + (175765946225347955502923304814720479161940523318141 / 87882973962593123704136187802115606863632678190134768000 : ℝ) * ((x - 4) ^ 4) := by
    unfold q4 Aq4 Aq5; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x ≤ 6 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq5 6 - Aq5 x) + (Aq6 (x + 1) - Aq6 6)) - q5 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 5 := by linarith
  have hxr : (0:ℝ) ≤ 6 - x := by linarith
  have hT0 : (0:ℝ) ≤ (6 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 5) ^ 1 * (6 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 5) ^ 2 * (6 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 5) ^ 3 * (6 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 5) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq5 6 - Aq5 x) + (Aq6 (x + 1) - Aq6 6)) - q5 x
      = (17093460957254863880687667 / 8546730478372753236358240016000 : ℝ) * ((6 - x) ^ 4) + (308895933044398530458359052891 / 38611991618668505933557438832284000 : ℝ) * ((x - 5) ^ 1 * (6 - x) ^ 3) + (8972169124206790218155080519676584057 / 667104862098545627941914435861684852328000 : ℝ) * ((x - 5) ^ 2 * (6 - x) ^ 2) + (18909703762010962389582289485975793420252623 / 2363712965134481860021722876679774167005088884000 : ℝ) * ((x - 5) ^ 3 * (6 - x) ^ 1) + (40417866791194307905926252094121281002096728208 / 20208933325568054925046348128373210455523601958896125 : ℝ) * ((x - 5) ^ 4) := by
    unfold q5 Aq5 Aq6; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x ≤ 7 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq6 7 - Aq6 x) + (Aq7 (x + 1) - Aq7 7)) - q6 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 6 := by linarith
  have hxr : (0:ℝ) ≤ 7 - x := by linarith
  have hT0 : (0:ℝ) ≤ (7 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 6) ^ 1 * (7 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 6) ^ 2 * (7 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 6) ^ 3 * (7 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 6) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq6 7 - Aq6 x) + (Aq7 (x + 1) - Aq7 7)) - q6 x
      = (57807837031612279475287 / 28903918474656019713191639500 : ℝ) * ((7 - x) ^ 4) + (2922383389141023751147778653 / 365297923065693832201097066462000 : ℝ) * ((x - 6) ^ 1 * (7 - x) ^ 3) + (1412364399406046121607796813616149 / 63758734193963135778547280883211018000 : ℝ) * ((x - 6) ^ 2 * (7 - x) ^ 2) + (5632701697709850406563072610989787207 / 704087701703934908402497622793299271774000 : ℝ) * ((x - 6) ^ 3 * (7 - x) ^ 1) + (5571382638241794282292418792914561778001197 / 2785691167027501447236622051689138311646746815200 : ℝ) * ((x - 6) ^ 4) := by
    unfold q6 Aq6 Aq7; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x ≤ 8 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq7 8 - Aq7 x) + (Aq8 (x + 1) - Aq8 8)) - q7 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 7 := by linarith
  have hxr : (0:ℝ) ≤ 8 - x := by linarith
  have hT0 : (0:ℝ) ≤ (8 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 7) ^ 1 * (8 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 7) ^ 2 * (8 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 7) ^ 3 * (8 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 7) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq7 8 - Aq7 x) + (Aq8 (x + 1) - Aq8 8)) - q7 x
      = (439053668738621107 / 219526824419006375911200 : ℝ) * ((8 - x) ^ 4) + (907880295334997381663923 / 113485032169976568129224581000 : ℝ) * ((x - 7) ^ 1 * (8 - x) ^ 3) + (2903392736916934409220339068519 / 91201179344099271197310919809588600 : ℝ) * ((x - 7) ^ 2 * (8 - x) ^ 2) + (760821820224853404286761650854092634 / 95102731595997583981905181967447871712275 : ℝ) * ((x - 7) ^ 3 * (8 - x) ^ 1) + (1832869028109495339451081951041992854481359 / 916434648369247678621473628785639228266127091500 : ℝ) * ((x - 7) ^ 4) := by
    unfold q7 Aq7 Aq8; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x ≤ 9 → 0 ≤ 1 / 1000 + 999 / 1000 * ((Aq8 9 - Aq8 x) + (Aq9 (x + 1) - Aq9 9)) - q8 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 8 := by linarith
  have hxr : (0:ℝ) ≤ 9 - x := by linarith
  have hT0 : (0:ℝ) ≤ (9 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 8) ^ 1 * (9 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 8) ^ 2 * (9 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 8) ^ 3 * (9 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 8) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * ((Aq8 9 - Aq8 x) + (Aq9 (x + 1) - Aq9 9)) - q8 x
      = (2226448406129867061577 / 1113224197294532039270774500 : ℝ) * ((9 - x) ^ 4) + (1322774965858980048643460496237 / 11955918782971939237628269594099000 : ℝ) * ((x - 8) ^ 1 * (9 - x) ^ 3) + (3506998588977541437570550388480029 / 292249880935026934127623540544676251050 : ℝ) * ((x - 8) ^ 2 * (9 - x) ^ 2) + (26497927414121582590951715255662759970281 / 3312240912566173780413361138128818401490271600 : ℝ) * ((x - 8) ^ 3 * (9 - x) ^ 1) + (170745753941863191660490930415728178275100807713 / 85372877031756626543203166800824769145675690879136000 : ℝ) * ((x - 8) ^ 4) := by
    unfold q8 Aq8 Aq9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

lemma ldrift_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x ≤ 10 → 0 ≤ 1 / 1000 + 999 / 1000 * (Aq9 10 - Aq9 x) - q9 x := by
  intro x h0 h1
  have hxl : (0:ℝ) ≤ x - 9 := by linarith
  have hxr : (0:ℝ) ≤ 10 - x := by linarith
  have hT0 : (0:ℝ) ≤ (10 - x) ^ 4 := pow_nonneg hxr _
  have hT1 : (0:ℝ) ≤ (x - 9) ^ 1 * (10 - x) ^ 3 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT2 : (0:ℝ) ≤ (x - 9) ^ 2 * (10 - x) ^ 2 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT3 : (0:ℝ) ≤ (x - 9) ^ 3 * (10 - x) ^ 1 := mul_nonneg (pow_nonneg hxl _) (pow_nonneg hxr _)
  have hT4 : (0:ℝ) ≤ (x - 9) ^ 4 := pow_nonneg hxl _
  have key : 1 / 1000 + 999 / 1000 * (Aq9 10 - Aq9 x) - q9 x
      = (8521082550993404507293 / 4260541249823823438308896000 : ℝ) * ((10 - x) ^ 4) + (25563247605915971670583 / 3195405937367867578731672000 : ℝ) * ((x - 9) ^ 1 * (10 - x) ^ 3) + (176728188169491951550607 / 2130270624911911719154448000 : ℝ) * ((x - 9) ^ 2 * (10 - x) ^ 2) + (5112649486222350202511 / 639081187473573515746334400 : ℝ) * ((x - 9) ^ 3 * (10 - x) ^ 1) + (399425740227031787417 / 199712871085491723670729500 : ℝ) * ((x - 9) ^ 4) := by
    unfold q9 Aq9; ring
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4]

noncomputable def Vr : ℝ → ℝ := fun x =>
  if x < 1 then 0
  else if x < 2 then p1 x
  else if x < 3 then p2 x
  else if x < 4 then p3 x
  else if x < 5 then p4 x
  else if x < 6 then p5 x
  else if x < 7 then p6 x
  else if x < 8 then p7 x
  else if x < 9 then p8 x
  else if x < 10 then p9 x
  else if x < 11 then p10 x
  else 0

noncomputable def Wr : ℝ → ℝ := fun x =>
  if x < 1 then 0
  else if x < 2 then q1 x
  else if x < 3 then q2 x
  else if x < 4 then q3 x
  else if x < 5 then q4 x
  else if x < 6 then q5 x
  else if x < 7 then q6 x
  else if x < 8 then q7 x
  else if x < 9 then q8 x
  else if x < 10 then q9 x
  else 0

lemma Vr_below : ∀ x : ℝ, x < 1 → Vr x = 0 := by
  intro x h
  simp only [Vr]
  rw [if_pos h]

lemma Vr_on_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x < 2 → Vr x = p1 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x < 3 → Vr x = p2 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x < 4 → Vr x = p3 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x < 5 → Vr x = p4 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x < 6 → Vr x = p5 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x < 7 → Vr x = p6 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x < 8 → Vr x = p7 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x < 9 → Vr x = p8 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x < 10 → Vr x = p9 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (9:ℝ) ≤ x)), if_pos h1]

lemma Vr_on_10 : ∀ x : ℝ, (10:ℝ) ≤ x → x < 11 → Vr x = p10 x := by
  intro x h0 h1
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (9:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (10:ℝ) ≤ x)), if_pos h1]

lemma Vr_above : ∀ x : ℝ, (11:ℝ) ≤ x → Vr x = 0 := by
  intro x h
  simp only [Vr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (9:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (10:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (11:ℝ) ≤ x))]

lemma Wr_below : ∀ x : ℝ, x < 1 → Wr x = 0 := by
  intro x h
  simp only [Wr]
  rw [if_pos h]

lemma Wr_on_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x < 2 → Wr x = q1 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x < 3 → Wr x = q2 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x < 4 → Wr x = q3 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x < 5 → Wr x = q4 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x < 6 → Wr x = q5 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x < 7 → Wr x = q6 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x < 8 → Wr x = q7 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x < 9 → Wr x = q8 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_pos h1]

lemma Wr_on_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x < 10 → Wr x = q9 x := by
  intro x h0 h1
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (9:ℝ) ≤ x)), if_pos h1]

lemma Wr_above : ∀ x : ℝ, (10:ℝ) ≤ x → Wr x = 0 := by
  intro x h
  simp only [Wr]
  rw [if_neg (not_lt.2 (by linarith : (1:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (2:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (3:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (4:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (5:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (6:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (7:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (8:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (9:ℝ) ≤ x)), if_neg (not_lt.2 (by linarith : (10:ℝ) ≤ x))]

lemma Vr_nonneg : ∀ x : ℝ, 0 ≤ Vr x := by
  intro x
  simp only [Vr]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · exact le_rfl
  · exact p1_nonneg x (not_lt.1 h1) h2.le
  · exact p2_nonneg x (not_lt.1 h2) h3.le
  · exact p3_nonneg x (not_lt.1 h3) h4.le
  · exact p4_nonneg x (not_lt.1 h4) h5.le
  · exact p5_nonneg x (not_lt.1 h5) h6.le
  · exact p6_nonneg x (not_lt.1 h6) h7.le
  · exact p7_nonneg x (not_lt.1 h7) h8.le
  · exact p8_nonneg x (not_lt.1 h8) h9.le
  · exact p9_nonneg x (not_lt.1 h9) h10.le
  · exact p10_nonneg x (not_lt.1 h10) h11.le
  · exact le_rfl

lemma Vr_le_one : ∀ x : ℝ, Vr x ≤ 1 := by
  intro x
  simp only [Vr]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · exact zero_le_one
  · have := p1_cap x (not_lt.1 h1) h2.le; linarith
  · have := p2_cap x (not_lt.1 h2) h3.le; linarith
  · have := p3_cap x (not_lt.1 h3) h4.le; linarith
  · have := p4_cap x (not_lt.1 h4) h5.le; linarith
  · have := p5_cap x (not_lt.1 h5) h6.le; linarith
  · have := p6_cap x (not_lt.1 h6) h7.le; linarith
  · have := p7_cap x (not_lt.1 h7) h8.le; linarith
  · have := p8_cap x (not_lt.1 h8) h9.le; linarith
  · have := p9_cap x (not_lt.1 h9) h10.le; linarith
  · have := p10_cap x (not_lt.1 h10) h11.le; linarith
  · exact zero_le_one

lemma Wr_le_one : ∀ x : ℝ, Wr x ≤ 1 := by
  intro x
  simp only [Wr]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact zero_le_one
  · have := q1_cap x (not_lt.1 h1) h2.le; linarith
  · have := q2_cap x (not_lt.1 h2) h3.le; linarith
  · have := q3_cap x (not_lt.1 h3) h4.le; linarith
  · have := q4_cap x (not_lt.1 h4) h5.le; linarith
  · have := q5_cap x (not_lt.1 h5) h6.le; linarith
  · have := q6_cap x (not_lt.1 h6) h7.le; linarith
  · have := q7_cap x (not_lt.1 h7) h8.le; linarith
  · have := q8_cap x (not_lt.1 h8) h9.le; linarith
  · have := q9_cap x (not_lt.1 h9) h10.le; linarith
  · exact zero_le_one

lemma Wr_ge_negone : ∀ x : ℝ, -1 ≤ Wr x := by
  intro x
  simp only [Wr]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · norm_num
  · have := q1_floor x (not_lt.1 h1) h2.le; linarith
  · have := q2_floor x (not_lt.1 h2) h3.le; linarith
  · have := q3_floor x (not_lt.1 h3) h4.le; linarith
  · have := q4_floor x (not_lt.1 h4) h5.le; linarith
  · have := q5_floor x (not_lt.1 h5) h6.le; linarith
  · have := q6_floor x (not_lt.1 h6) h7.le; linarith
  · have := q7_floor x (not_lt.1 h7) h8.le; linarith
  · have := q8_floor x (not_lt.1 h8) h9.le; linarith
  · have := q9_floor x (not_lt.1 h9) h10.le; linarith
  · norm_num

lemma Vr_measurable : Measurable Vr := by
  unfold Vr
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p1 by unfold p1; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p2 by unfold p2; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p3 by unfold p3; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p4 by unfold p4; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p5 by unfold p5; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p6 by unfold p6; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p7 by unfold p7; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p8 by unfold p8; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p9 by unfold p9; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous p10 by unfold p10; continuity).measurable ?_
  exact measurable_const

lemma Wr_measurable : Measurable Wr := by
  unfold Wr
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q1 by unfold q1; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q2 by unfold q2; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q3 by unfold q3; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q4 by unfold q4; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q5 by unfold q5; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q6 by unfold q6; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q7 by unfold q7; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q8 by unfold q8; continuity).measurable ?_
  refine Measurable.ite measurableSet_Iio
    (show Continuous q9 by unfold q9; continuity).measurable ?_
  exact measurable_const

lemma Vr_intervalIntegrable (a b : ℝ) : IntervalIntegrable Vr volume a b := by
  constructor <;>
  · refine (integrable_const (1:ℝ)).mono' Vr_measurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Vr_nonneg s)]
    exact Vr_le_one s

lemma Wr_intervalIntegrable (a b : ℝ) : IntervalIntegrable Wr volume a b := by
  constructor <;>
  · refine (integrable_const (1:ℝ)).mono' Wr_measurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨Wr_ge_negone s, Wr_le_one s⟩

lemma Vr_ieval_1 {a b : ℝ} (ha : (1:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (2:ℝ)) :
    ∫ s in a..b, Vr s = Ap1 b - Ap1 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p1 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((2:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (1:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (2:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_1 s hs1 hs2
  rw [hcong, p1_integral]

lemma Vr_ieval_2 {a b : ℝ} (ha : (2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (3:ℝ)) :
    ∫ s in a..b, Vr s = Ap2 b - Ap2 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p2 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((3:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (2:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (3:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_2 s hs1 hs2
  rw [hcong, p2_integral]

lemma Vr_ieval_3 {a b : ℝ} (ha : (3:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (4:ℝ)) :
    ∫ s in a..b, Vr s = Ap3 b - Ap3 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p3 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((4:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (3:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (4:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_3 s hs1 hs2
  rw [hcong, p3_integral]

lemma Vr_ieval_4 {a b : ℝ} (ha : (4:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (5:ℝ)) :
    ∫ s in a..b, Vr s = Ap4 b - Ap4 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p4 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((5:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (4:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (5:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_4 s hs1 hs2
  rw [hcong, p4_integral]

lemma Vr_ieval_5 {a b : ℝ} (ha : (5:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (6:ℝ)) :
    ∫ s in a..b, Vr s = Ap5 b - Ap5 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p5 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((6:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (5:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (6:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_5 s hs1 hs2
  rw [hcong, p5_integral]

lemma Vr_ieval_6 {a b : ℝ} (ha : (6:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (7:ℝ)) :
    ∫ s in a..b, Vr s = Ap6 b - Ap6 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p6 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((7:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (6:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (7:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_6 s hs1 hs2
  rw [hcong, p6_integral]

lemma Vr_ieval_7 {a b : ℝ} (ha : (7:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (8:ℝ)) :
    ∫ s in a..b, Vr s = Ap7 b - Ap7 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p7 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((8:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (7:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (8:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_7 s hs1 hs2
  rw [hcong, p7_integral]

lemma Vr_ieval_8 {a b : ℝ} (ha : (8:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (9:ℝ)) :
    ∫ s in a..b, Vr s = Ap8 b - Ap8 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p8 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((9:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (8:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (9:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_8 s hs1 hs2
  rw [hcong, p8_integral]

lemma Vr_ieval_9 {a b : ℝ} (ha : (9:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (10:ℝ)) :
    ∫ s in a..b, Vr s = Ap9 b - Ap9 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p9 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((10:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (9:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (10:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_9 s hs1 hs2
  rw [hcong, p9_integral]

lemma Vr_ieval_10 {a b : ℝ} (ha : (10:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (11:ℝ)) :
    ∫ s in a..b, Vr s = Ap10 b - Ap10 a := by
  have hcong : ∫ s in a..b, Vr s = ∫ s in a..b, p10 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((11:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (10:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (11:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Vr_on_10 s hs1 hs2
  rw [hcong, p10_integral]

lemma Wr_ieval_1 {a b : ℝ} (ha : (1:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (2:ℝ)) :
    ∫ s in a..b, Wr s = Aq1 b - Aq1 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q1 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((2:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (1:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (2:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_1 s hs1 hs2
  rw [hcong, q1_integral]

lemma Wr_ieval_2 {a b : ℝ} (ha : (2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (3:ℝ)) :
    ∫ s in a..b, Wr s = Aq2 b - Aq2 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q2 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((3:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (2:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (3:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_2 s hs1 hs2
  rw [hcong, q2_integral]

lemma Wr_ieval_3 {a b : ℝ} (ha : (3:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (4:ℝ)) :
    ∫ s in a..b, Wr s = Aq3 b - Aq3 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q3 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((4:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (3:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (4:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_3 s hs1 hs2
  rw [hcong, q3_integral]

lemma Wr_ieval_4 {a b : ℝ} (ha : (4:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (5:ℝ)) :
    ∫ s in a..b, Wr s = Aq4 b - Aq4 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q4 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((5:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (4:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (5:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_4 s hs1 hs2
  rw [hcong, q4_integral]

lemma Wr_ieval_5 {a b : ℝ} (ha : (5:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (6:ℝ)) :
    ∫ s in a..b, Wr s = Aq5 b - Aq5 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q5 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((6:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (5:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (6:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_5 s hs1 hs2
  rw [hcong, q5_integral]

lemma Wr_ieval_6 {a b : ℝ} (ha : (6:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (7:ℝ)) :
    ∫ s in a..b, Wr s = Aq6 b - Aq6 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q6 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((7:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (6:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (7:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_6 s hs1 hs2
  rw [hcong, q6_integral]

lemma Wr_ieval_7 {a b : ℝ} (ha : (7:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (8:ℝ)) :
    ∫ s in a..b, Wr s = Aq7 b - Aq7 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q7 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((8:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (7:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (8:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_7 s hs1 hs2
  rw [hcong, q7_integral]

lemma Wr_ieval_8 {a b : ℝ} (ha : (8:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (9:ℝ)) :
    ∫ s in a..b, Wr s = Aq8 b - Aq8 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q8 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((9:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (8:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (9:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_8 s hs1 hs2
  rw [hcong, q8_integral]

lemma Wr_ieval_9 {a b : ℝ} (ha : (9:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (10:ℝ)) :
    ∫ s in a..b, Wr s = Aq9 b - Aq9 a := by
  have hcong : ∫ s in a..b, Wr s = ∫ s in a..b, q9 s := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((10:ℝ))} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (9:ℝ) ≤ s := le_trans ha (le_of_lt hsI.1)
    have hs2 : s < (10:ℝ) := lt_of_le_of_ne (le_trans hsI.2 hb) (by simpa using hs)
    exact Wr_on_9 s hs1 hs2
  rw [hcong, q9_integral]

lemma chop_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x < 2 →
    ∫ s in x..(x + 1), Vr s
      = (Ap1 2 - Ap1 x) + (Ap2 (x + 1) - Ap2 2) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(2:ℝ), Vr s) + (∫ s in (2:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_1 h0 h1.le le_rfl,
    Vr_ieval_2 le_rfl (by linarith) (by linarith)]

lemma chop_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x < 3 →
    ∫ s in x..(x + 1), Vr s
      = (Ap2 3 - Ap2 x) + (Ap3 (x + 1) - Ap3 3) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(3:ℝ), Vr s) + (∫ s in (3:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_2 h0 h1.le le_rfl,
    Vr_ieval_3 le_rfl (by linarith) (by linarith)]

lemma chop_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x < 4 →
    ∫ s in x..(x + 1), Vr s
      = (Ap3 4 - Ap3 x) + (Ap4 (x + 1) - Ap4 4) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(4:ℝ), Vr s) + (∫ s in (4:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_3 h0 h1.le le_rfl,
    Vr_ieval_4 le_rfl (by linarith) (by linarith)]

lemma chop_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x < 5 →
    ∫ s in x..(x + 1), Vr s
      = (Ap4 5 - Ap4 x) + (Ap5 (x + 1) - Ap5 5) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(5:ℝ), Vr s) + (∫ s in (5:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_4 h0 h1.le le_rfl,
    Vr_ieval_5 le_rfl (by linarith) (by linarith)]

lemma chop_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x < 6 →
    ∫ s in x..(x + 1), Vr s
      = (Ap5 6 - Ap5 x) + (Ap6 (x + 1) - Ap6 6) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(6:ℝ), Vr s) + (∫ s in (6:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_5 h0 h1.le le_rfl,
    Vr_ieval_6 le_rfl (by linarith) (by linarith)]

lemma chop_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x < 7 →
    ∫ s in x..(x + 1), Vr s
      = (Ap6 7 - Ap6 x) + (Ap7 (x + 1) - Ap7 7) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(7:ℝ), Vr s) + (∫ s in (7:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_6 h0 h1.le le_rfl,
    Vr_ieval_7 le_rfl (by linarith) (by linarith)]

lemma chop_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x < 8 →
    ∫ s in x..(x + 1), Vr s
      = (Ap7 8 - Ap7 x) + (Ap8 (x + 1) - Ap8 8) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(8:ℝ), Vr s) + (∫ s in (8:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_7 h0 h1.le le_rfl,
    Vr_ieval_8 le_rfl (by linarith) (by linarith)]

lemma chop_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x < 9 →
    ∫ s in x..(x + 1), Vr s
      = (Ap8 9 - Ap8 x) + (Ap9 (x + 1) - Ap9 9) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(9:ℝ), Vr s) + (∫ s in (9:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_8 h0 h1.le le_rfl,
    Vr_ieval_9 le_rfl (by linarith) (by linarith)]

lemma chop_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x < 10 →
    ∫ s in x..(x + 1), Vr s
      = (Ap9 10 - Ap9 x) + (Ap10 (x + 1) - Ap10 10) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(10:ℝ), Vr s) + (∫ s in (10:ℝ)..(x + 1), Vr s)
      = ∫ s in x..(x + 1), Vr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Vr_intervalIntegrable _ _) (Vr_intervalIntegrable _ _)
  rw [← hsplit, Vr_ieval_9 h0 h1.le le_rfl,
    Vr_ieval_10 le_rfl (by linarith) (by linarith)]

lemma lchop_1 : ∀ x : ℝ, (1:ℝ) ≤ x → x < 2 →
    ∫ s in x..(x + 1), Wr s
      = (Aq1 2 - Aq1 x) + (Aq2 (x + 1) - Aq2 2) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(2:ℝ), Wr s) + (∫ s in (2:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_1 h0 h1.le le_rfl,
    Wr_ieval_2 le_rfl (by linarith) (by linarith)]

lemma lchop_2 : ∀ x : ℝ, (2:ℝ) ≤ x → x < 3 →
    ∫ s in x..(x + 1), Wr s
      = (Aq2 3 - Aq2 x) + (Aq3 (x + 1) - Aq3 3) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(3:ℝ), Wr s) + (∫ s in (3:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_2 h0 h1.le le_rfl,
    Wr_ieval_3 le_rfl (by linarith) (by linarith)]

lemma lchop_3 : ∀ x : ℝ, (3:ℝ) ≤ x → x < 4 →
    ∫ s in x..(x + 1), Wr s
      = (Aq3 4 - Aq3 x) + (Aq4 (x + 1) - Aq4 4) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(4:ℝ), Wr s) + (∫ s in (4:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_3 h0 h1.le le_rfl,
    Wr_ieval_4 le_rfl (by linarith) (by linarith)]

lemma lchop_4 : ∀ x : ℝ, (4:ℝ) ≤ x → x < 5 →
    ∫ s in x..(x + 1), Wr s
      = (Aq4 5 - Aq4 x) + (Aq5 (x + 1) - Aq5 5) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(5:ℝ), Wr s) + (∫ s in (5:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_4 h0 h1.le le_rfl,
    Wr_ieval_5 le_rfl (by linarith) (by linarith)]

lemma lchop_5 : ∀ x : ℝ, (5:ℝ) ≤ x → x < 6 →
    ∫ s in x..(x + 1), Wr s
      = (Aq5 6 - Aq5 x) + (Aq6 (x + 1) - Aq6 6) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(6:ℝ), Wr s) + (∫ s in (6:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_5 h0 h1.le le_rfl,
    Wr_ieval_6 le_rfl (by linarith) (by linarith)]

lemma lchop_6 : ∀ x : ℝ, (6:ℝ) ≤ x → x < 7 →
    ∫ s in x..(x + 1), Wr s
      = (Aq6 7 - Aq6 x) + (Aq7 (x + 1) - Aq7 7) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(7:ℝ), Wr s) + (∫ s in (7:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_6 h0 h1.le le_rfl,
    Wr_ieval_7 le_rfl (by linarith) (by linarith)]

lemma lchop_7 : ∀ x : ℝ, (7:ℝ) ≤ x → x < 8 →
    ∫ s in x..(x + 1), Wr s
      = (Aq7 8 - Aq7 x) + (Aq8 (x + 1) - Aq8 8) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(8:ℝ), Wr s) + (∫ s in (8:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_7 h0 h1.le le_rfl,
    Wr_ieval_8 le_rfl (by linarith) (by linarith)]

lemma lchop_8 : ∀ x : ℝ, (8:ℝ) ≤ x → x < 9 →
    ∫ s in x..(x + 1), Wr s
      = (Aq8 9 - Aq8 x) + (Aq9 (x + 1) - Aq9 9) := by
  intro x h0 h1
  have hsplit : (∫ s in x..(9:ℝ), Wr s) + (∫ s in (9:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  rw [← hsplit, Wr_ieval_8 h0 h1.le le_rfl,
    Wr_ieval_9 le_rfl (by linarith) (by linarith)]

lemma lchop_9 : ∀ x : ℝ, (9:ℝ) ≤ x → x < 10 →
    ∫ s in x..(x + 1), Wr s = Aq9 10 - Aq9 x := by
  intro x h0 h1
  have hsplit : (∫ s in x..(10:ℝ), Wr s) + (∫ s in (10:ℝ)..(x + 1), Wr s)
      = ∫ s in x..(x + 1), Wr s :=
    intervalIntegral.integral_add_adjacent_intervals
      (Wr_intervalIntegrable _ _) (Wr_intervalIntegrable _ _)
  have hz : ∫ s in (10:ℝ)..(x + 1), Wr s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun s hs => by
      rw [Set.uIcc_of_le (by linarith : (10:ℝ) ≤ x + 1)] at hs
      exact Wr_above s hs.1)]
    simp
  rw [← hsplit, Wr_ieval_9 h0 h1.le le_rfl, hz, add_zero]

noncomputable def eta : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance : IsProbabilityMeasure eta := by
  constructor
  simp only [eta, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]
  norm_num

def Viol : Set (ℝ × Bool) := {s | s.2 = true}

lemma Viol_measurableSet : MeasurableSet Viol :=
  measurable_snd (measurableSet_singleton true)

def Active : Set (ℝ × Bool) := {s | s.2 = false ∧ 1 ≤ s.1 ∧ s.1 < 10}

lemma Active_measurableSet : MeasurableSet Active := by
  have h : Active = (Prod.snd ⁻¹' {false})
      ∩ ((Prod.fst ⁻¹' Set.Ici (1:ℝ)) ∩ (Prod.fst ⁻¹' Set.Iio (10:ℝ))) := by
    ext s
    simp [Active]
  rw [h]
  exact (measurable_snd (measurableSet_singleton false)).inter
    ((measurable_fst measurableSet_Ici).inter (measurable_fst measurableSet_Iio))

noncomputable def step : ℝ × Bool → Measure (ℝ × Bool) := fun s =>
  if s.2 = false ∧ 1 ≤ s.1 ∧ s.1 < 10 then
    ENNReal.ofReal (1/1000) • Measure.dirac (s.1, true)
      + ENNReal.ofReal (999/1000) • Measure.map (fun u => (s.1 + u, false)) eta
  else Measure.dirac s

lemma step_prob : ∀ s, IsProbabilityMeasure (step s) := by
  intro s
  unfold step
  split_ifs
  · have hprob : IsProbabilityMeasure
        (Measure.map (fun u : ℝ => (s.1 + u, false)) eta) :=
      Measure.isProbabilityMeasure_map
        ((measurable_const_add s.1).prodMk measurable_const).aemeasurable
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · infer_instance

lemma step_measurable : Measurable step := by
  rw [Measure.measurable_measure]
  intro B hB
  have hsplit : (fun s => step s B)
      = fun s => if s.2 = false ∧ 1 ≤ s.1 ∧ s.1 < 10
          then (ENNReal.ofReal (1/1000) • Measure.dirac (s.1, true)
            + ENNReal.ofReal (999/1000)
              • Measure.map (fun u => (s.1 + u, false)) eta) B
          else Measure.dirac s B := by
    funext s
    unfold step
    exact apply_ite (fun μ : Measure (ℝ × Bool) => μ B) _ _ _
  rw [hsplit]
  refine Measurable.ite Active_measurableSet ?_ ?_
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Measurable.add ?_ ?_
    · refine Measurable.const_mul ?_ _
      have h : (fun s : ℝ × Bool => Measure.dirac (s.1, true) B)
          = fun s : ℝ × Bool => B.indicator (fun _ => (1:ℝ≥0∞)) (s.1, true) := by
        funext s
        exact Measure.dirac_apply' _ hB
      rw [h]
      exact (measurable_one.indicator hB).comp (measurable_fst.prodMk measurable_const)
    · refine Measurable.const_mul ?_ _
      have hmap : ∀ s : ℝ × Bool, (Measure.map (fun u => (s.1 + u, false)) eta) B
          = ∫⁻ u, B.indicator (fun _ => (1:ℝ≥0∞)) (s.1 + u, false) ∂eta := by
        intro s
        rw [Measure.map_apply ((measurable_const_add s.1).prodMk measurable_const) hB,
          ← lintegral_indicator_one
            (((measurable_const_add s.1).prodMk measurable_const) hB)]
        congr 1
      simp only [hmap]
      have hjoint : Measurable fun p : (ℝ × Bool) × ℝ =>
          B.indicator (fun _ => (1:ℝ≥0∞)) (p.1.1 + p.2, false) :=
        (measurable_one.indicator hB).comp
          (((measurable_fst.comp measurable_fst).add measurable_snd).prodMk
            measurable_const)
      exact hjoint.lintegral_prod_right'
  · have h : (fun s : ℝ × Bool => Measure.dirac s B)
        = B.indicator (fun _ => (1:ℝ≥0∞)) := by
      funext s
      exact Measure.dirac_apply' s hB
    rw [h]
    exact measurable_one.indicator hB

noncomputable def stepK : Kernel (ℝ × Bool) (ℝ × Bool) := ⟨step, step_measurable⟩

instance : IsMarkovKernel stepK := ⟨fun s => step_prob s⟩

@[simp] lemma stepK_apply (s : ℝ × Bool) : stepK s = step s := rfl

noncomputable def V : ℝ × Bool → ℝ := fun s => if s.2 = true then 1 else Vr s.1

noncomputable def W : ℝ × Bool → ℝ := fun s => if s.2 = true then 1 else Wr s.1

lemma V_measurable : Measurable V :=
  Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
    (Vr_measurable.comp measurable_fst)

lemma W_measurable : Measurable W :=
  Measurable.ite (measurable_snd (measurableSet_singleton true)) measurable_const
    (Wr_measurable.comp measurable_fst)

lemma V_nonneg : ∀ s, 0 ≤ V s := by
  intro s
  unfold V
  split_ifs
  · exact zero_le_one
  · exact Vr_nonneg s.1

lemma V_le_one : ∀ s, V s ≤ 1 := by
  intro s
  unfold V
  split_ifs
  · exact le_rfl
  · exact Vr_le_one s.1

lemma W_le_one : ∀ s, W s ≤ 1 := by
  intro s
  unfold W
  split_ifs
  · exact le_rfl
  · exact Wr_le_one s.1

lemma W_ge_negone : ∀ s, -1 ≤ W s := by
  intro s
  unfold W
  split_ifs
  · norm_num
  · exact Wr_ge_negone s.1

lemma V_barrier : ∀ s ∈ Viol, 1 ≤ V s := by
  intro s hs
  have h : s.2 = true := hs
  unfold V
  rw [if_pos h]

lemma step_integral_V {x : ℝ} (h1 : 1 ≤ x) (h10 : x < 10) :
    ∫ z, V z ∂(step (x, false)) = 1 / 1000 + 999 / 1000 * ∫ s in x..(x + 1), Vr s := by
  rw [show step ((x : ℝ), false) = ENNReal.ofReal (1/1000) • Measure.dirac ((x : ℝ), true)
      + ENNReal.ofReal (999/1000) • Measure.map (fun u => (x + u, false)) eta from by
    simp [step, h1, h10]]
  have hb : ∀ z : ℝ × Bool, ‖V z‖ ≤ 1 := fun z => by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [V_nonneg z], V_le_one z⟩
  have hprob : IsProbabilityMeasure (Measure.map (fun u : ℝ => (x + u, false)) eta) :=
    Measure.isProbabilityMeasure_map
      ((measurable_const_add x).prodMk measurable_const).aemeasurable
  have hint1 : Integrable V (ENNReal.ofReal (1/1000) • Measure.dirac ((x : ℝ), true)) :=
    ((integrable_const (1:ℝ)).mono' V_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).smul_measure ENNReal.ofReal_ne_top
  have hint2 : Integrable V
      (ENNReal.ofReal (999/1000) • Measure.map (fun u : ℝ => (x + u, false)) eta) :=
    ((integrable_const (1:ℝ)).mono' V_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hint1 hint2, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/1000),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 999/1000),
    integral_dirac,
    integral_map ((measurable_const_add x).prodMk measurable_const).aemeasurable
      V_measurable.aestronglyMeasurable]
  have htrue : V ((x : ℝ), true) = 1 := by simp [V]
  have heta : ∫ u, V (x + u, false) ∂eta = ∫ s in x..(x + 1), Vr s := by
    have hu : ∀ u : ℝ, V (x + u, false) = Vr (x + u) := fun u => by simp [V]
    rw [integral_congr_ae (Filter.Eventually.of_forall hu)]
    unfold eta
    rw [show (∫ u, Vr (x + u) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
        = ∫ u in (0:ℝ)..1, Vr (x + u) from by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact integral_Icc_eq_integral_Ioc]
    rw [intervalIntegral.integral_comp_add_left (fun s => Vr s) x,
      show x + (0:ℝ) = x by ring]
  rw [htrue, heta]
  ring

lemma step_integral_W {x : ℝ} (h1 : 1 ≤ x) (h10 : x < 10) :
    ∫ z, W z ∂(step (x, false)) = 1 / 1000 + 999 / 1000 * ∫ s in x..(x + 1), Wr s := by
  rw [show step ((x : ℝ), false) = ENNReal.ofReal (1/1000) • Measure.dirac ((x : ℝ), true)
      + ENNReal.ofReal (999/1000) • Measure.map (fun u => (x + u, false)) eta from by
    simp [step, h1, h10]]
  have hb : ∀ z : ℝ × Bool, ‖W z‖ ≤ 1 := fun z => by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨W_ge_negone z, W_le_one z⟩
  have hprob : IsProbabilityMeasure (Measure.map (fun u : ℝ => (x + u, false)) eta) :=
    Measure.isProbabilityMeasure_map
      ((measurable_const_add x).prodMk measurable_const).aemeasurable
  have hint1 : Integrable W (ENNReal.ofReal (1/1000) • Measure.dirac ((x : ℝ), true)) :=
    ((integrable_const (1:ℝ)).mono' W_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).smul_measure ENNReal.ofReal_ne_top
  have hint2 : Integrable W
      (ENNReal.ofReal (999/1000) • Measure.map (fun u : ℝ => (x + u, false)) eta) :=
    ((integrable_const (1:ℝ)).mono' W_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hint1 hint2, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/1000),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 999/1000),
    integral_dirac,
    integral_map ((measurable_const_add x).prodMk measurable_const).aemeasurable
      W_measurable.aestronglyMeasurable]
  have htrue : W ((x : ℝ), true) = 1 := by simp [W]
  have heta : ∫ u, W (x + u, false) ∂eta = ∫ s in x..(x + 1), Wr s := by
    have hu : ∀ u : ℝ, W (x + u, false) = Wr (x + u) := fun u => by simp [W]
    rw [integral_congr_ae (Filter.Eventually.of_forall hu)]
    unfold eta
    rw [show (∫ u, Wr (x + u) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
        = ∫ u in (0:ℝ)..1, Wr (x + u) from by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact integral_Icc_eq_integral_Ioc]
    rw [intervalIntegral.integral_comp_add_left (fun s => Wr s) x,
      show x + (0:ℝ) = x by ring]
  rw [htrue, heta]
  ring

lemma V_drift : ∀ s : ℝ × Bool, s ∉ Viol → ∫ z, V z ∂(step s) ≤ V s := by
  intro s hs
  have he : s.2 = false := by
    simpa [Viol, Set.mem_setOf_eq, Bool.not_eq_true] using hs
  have hsplit : s = (s.1, false) := by
    rw [← he]
  by_cases hact : 1 ≤ s.1 ∧ s.1 < 10
  · obtain ⟨h1, h10⟩ := hact
    rw [hsplit, step_integral_V h1 h10, show V ((s.1 : ℝ), false) = Vr s.1 from by
      simp [V]]
    set x := s.1 with hx

    rcases lt_or_ge x 2 with hc1 | hc1
    · rw [chop_1 x h1 hc1, Vr_on_1 x h1 hc1]
      have := drift_1 x h1 (le_of_lt hc1)
      linarith
    rcases lt_or_ge x 3 with hc2 | hc2
    · rw [chop_2 x hc1 hc2, Vr_on_2 x hc1 hc2]
      have := drift_2 x hc1 (le_of_lt hc2)
      linarith
    rcases lt_or_ge x 4 with hc3 | hc3
    · rw [chop_3 x hc2 hc3, Vr_on_3 x hc2 hc3]
      have := drift_3 x hc2 (le_of_lt hc3)
      linarith
    rcases lt_or_ge x 5 with hc4 | hc4
    · rw [chop_4 x hc3 hc4, Vr_on_4 x hc3 hc4]
      have := drift_4 x hc3 (le_of_lt hc4)
      linarith
    rcases lt_or_ge x 6 with hc5 | hc5
    · rw [chop_5 x hc4 hc5, Vr_on_5 x hc4 hc5]
      have := drift_5 x hc4 (le_of_lt hc5)
      linarith
    rcases lt_or_ge x 7 with hc6 | hc6
    · rw [chop_6 x hc5 hc6, Vr_on_6 x hc5 hc6]
      have := drift_6 x hc5 (le_of_lt hc6)
      linarith
    rcases lt_or_ge x 8 with hc7 | hc7
    · rw [chop_7 x hc6 hc7, Vr_on_7 x hc6 hc7]
      have := drift_7 x hc6 (le_of_lt hc7)
      linarith
    rcases lt_or_ge x 9 with hc8 | hc8
    · rw [chop_8 x hc7 hc8, Vr_on_8 x hc7 hc8]
      have := drift_8 x hc7 (le_of_lt hc8)
      linarith
    rw [chop_9 x hc8 h10, Vr_on_9 x hc8 h10]
    have := drift_9 x hc8 (le_of_lt h10)
    linarith

  · rw [show step s = Measure.dirac s from by
      unfold step
      exact if_neg fun h => hact h.2, integral_dirac]

lemma W_drift : ∀ s : ℝ × Bool, s ∈ Active → W s ≤ ∫ z, W z ∂(step s) := by
  intro s hs
  obtain ⟨he, h1, h10⟩ := hs
  have hsplit : s = (s.1, false) := by
    rw [← he]
  rw [hsplit, step_integral_W h1 h10, show W ((s.1 : ℝ), false) = Wr s.1 from by
    simp [W]]
  set x := s.1 with hx

  rcases lt_or_ge x 2 with hc1 | hc1
  · rw [lchop_1 x h1 hc1, Wr_on_1 x h1 hc1]
    have := ldrift_1 x h1 (le_of_lt hc1)
    linarith
  rcases lt_or_ge x 3 with hc2 | hc2
  · rw [lchop_2 x hc1 hc2, Wr_on_2 x hc1 hc2]
    have := ldrift_2 x hc1 (le_of_lt hc2)
    linarith
  rcases lt_or_ge x 4 with hc3 | hc3
  · rw [lchop_3 x hc2 hc3, Wr_on_3 x hc2 hc3]
    have := ldrift_3 x hc2 (le_of_lt hc3)
    linarith
  rcases lt_or_ge x 5 with hc4 | hc4
  · rw [lchop_4 x hc3 hc4, Wr_on_4 x hc3 hc4]
    have := ldrift_4 x hc3 (le_of_lt hc4)
    linarith
  rcases lt_or_ge x 6 with hc5 | hc5
  · rw [lchop_5 x hc4 hc5, Wr_on_5 x hc4 hc5]
    have := ldrift_5 x hc4 (le_of_lt hc5)
    linarith
  rcases lt_or_ge x 7 with hc6 | hc6
  · rw [lchop_6 x hc5 hc6, Wr_on_6 x hc5 hc6]
    have := ldrift_6 x hc5 (le_of_lt hc6)
    linarith
  rcases lt_or_ge x 8 with hc7 | hc7
  · rw [lchop_7 x hc6 hc7, Wr_on_7 x hc6 hc7]
    have := ldrift_7 x hc6 (le_of_lt hc7)
    linarith
  rcases lt_or_ge x 9 with hc8 | hc8
  · rw [lchop_8 x hc7 hc8, Wr_on_8 x hc7 hc8]
    have := ldrift_8 x hc7 (le_of_lt hc8)
    linarith
  rw [lchop_9 x hc8 h10, Wr_on_9 x hc8 h10]
  have := ldrift_9 x hc8 (le_of_lt h10)
  linarith

lemma esc_bound : ∀ s : ℝ × Bool, s ∈ Active →
    step s Active ≤ ENNReal.ofReal (999/1000) := by
  intro s hs
  obtain ⟨he, h1, h10⟩ := hs
  have hsplit : s = (s.1, false) := by
    rw [← he]
  rw [hsplit, show step ((s.1 : ℝ), false)
      = ENNReal.ofReal (1/1000) • Measure.dirac ((s.1 : ℝ), true)
        + ENNReal.ofReal (999/1000) • Measure.map (fun u => (s.1 + u, false)) eta from by
    simp [step, h1, h10]]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]
  have hd : Measure.dirac ((s.1 : ℝ), true) Active = 0 := by
    rw [Measure.dirac_apply' _ Active_measurableSet]
    exact Set.indicator_of_notMem (by simp [Active]) _
  have hprob : IsProbabilityMeasure
      (Measure.map (fun u : ℝ => (s.1 + u, false)) eta) :=
    Measure.isProbabilityMeasure_map
      ((measurable_const_add s.1).prodMk measurable_const).aemeasurable
  rw [hd, mul_zero, zero_add]
  calc ENNReal.ofReal (999/1000)
        * (Measure.map (fun u : ℝ => (s.1 + u, false)) eta) Active
      ≤ ENNReal.ofReal (999/1000) * 1 := mul_le_mul_right prob_le_one _
    _ = ENNReal.ofReal (999/1000) := mul_one _

theorem sound_upper :
    Battery.pathMeasure stepK ((1 : ℝ), false) {ω | ∃ n, ω n ∈ Viol}
      ≤ ENNReal.ofReal (150065 / 8087357 : ℝ) := by
  have h := Battery.measure_reach_le (K := stepK) (f := V) (A := Viol) (C := 1)
    Viol_measurableSet V_measurable V_nonneg V_le_one V_barrier
    (fun y hy => by rw [stepK_apply]; exact V_drift y hy) ((1 : ℝ), false)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv : V ((1 : ℝ), false) = p1 1 := by
    have h1 : V ((1 : ℝ), false) = Vr 1 := by simp [V]
    rw [h1, Vr_on_1 1 (by norm_num) (by norm_num)]
  rw [hv]
  unfold p1
  norm_num

theorem sound_lower :
    ENNReal.ofReal ((429788929984053075589523987651 : ℝ) / 23300061339378910715200000000000)
      ≤ Battery.pathMeasure stepK ((1 : ℝ), false) {ω | ∃ n, ω n ∈ Viol} := by
  have hWE : ∀ s ∈ Activeᶜ, s ∉ Viol → W s ≤ 0 := by
    intro s hsE hsA
    have he : s.2 = false := by
      simpa [Viol, Set.mem_setOf_eq, Bool.not_eq_true] using hsA
    have hW : W s = Wr s.1 := by
      unfold W
      rw [if_neg (by rw [he]; exact Bool.false_ne_true)]
    have hnact : ¬(1 ≤ s.1 ∧ s.1 < 10) := fun h => hsE ⟨he, h.1, h.2⟩
    rw [hW]
    rcases not_and_or.1 hnact with h | h
    · exact le_of_eq (Wr_below s.1 (not_le.1 h))
    · exact le_of_eq (Wr_above s.1 (not_lt.1 h))
  have hWint : ∀ s : ℝ × Bool, s ∉ Activeᶜ → Integrable W (stepK s) := by
    intro s hs
    rw [stepK_apply]
    have : IsProbabilityMeasure (step s) := step_prob s
    exact (integrable_const (1:ℝ)).mono' W_measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact abs_le.2 ⟨W_ge_negone z, W_le_one z⟩)
  have hdrift : ∀ s : ℝ × Bool, s ∉ Activeᶜ → W s ≤ ∫ z, W z ∂(stepK s) := by
    intro s hs
    rw [stepK_apply]
    exact W_drift s (not_not.1 hs)
  have hesc : ∀ s : ℝ × Bool, s ∉ Activeᶜ →
      stepK s (Activeᶜ)ᶜ ≤ ENNReal.ofReal (999/1000) := by
    intro s hs
    rw [compl_compl, stepK_apply]
    exact esc_bound s (not_not.1 hs)
  have h := Qtsl.OptionalStopping.measure_reach_ge (K := stepK)
    (A := Viol) (E := Activeᶜ) (W := W) (β := 999/1000)
    Viol_measurableSet Active_measurableSet.compl W_measurable W_le_one
    hWE hWint hdrift (by norm_num) (by norm_num) hesc ((1 : ℝ), false)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have hw : W ((1 : ℝ), false) = q1 1 := by
    have h1 : W ((1 : ℝ), false) = Wr 1 := by simp [W]
    rw [h1, Wr_on_1 1 (by norm_num) (by norm_num)]
  rw [hw]
  unfold q1
  norm_num

theorem sound_bracket :
    ENNReal.ofReal ((429788929984053075589523987651 : ℝ) / 23300061339378910715200000000000)
        ≤ Battery.pathMeasure stepK ((1 : ℝ), false) {ω | ∃ n, ω n ∈ Viol}
      ∧ Battery.pathMeasure stepK ((1 : ℝ), false) {ω | ∃ n, ω n ∈ Viol}
        ≤ ENNReal.ofReal (150065 / 8087357 : ℝ) :=
  ⟨sound_lower, sound_upper⟩

theorem published_farkas_refuted :
    ENNReal.ofReal (181 / 10000 : ℝ)
      < Battery.pathMeasure stepK ((1 : ℝ), false) {ω | ∃ n, ω n ∈ Viol} :=
  lt_of_lt_of_le
    ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num))
    sound_lower

end Qtsl.Sweep.FaultyUniform
