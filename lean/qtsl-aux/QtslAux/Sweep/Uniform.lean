import QtslAux.Sweep.Discrete
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The `Repulse100Uniform` benchmark row (continuous state)

Certified reachability bound for the repulsion benchmark with uniform continuous noise: the Markov
chain on `ℝ` that, while `0 ≤ x ≤ 100`, moves to `x + u` with `u` uniform on `[-2, 1]` (kernel
`stepK`, built from the uniform measure `eta`), and is absorbed elsewhere.

The certificate is the piecewise-polynomial supermartingale
`V x = (14/3) ^ (⌊x⌋ - 100) * w (x - ⌊x⌋)` on `[-2, 100)`, equal to `0` below `-2` and to `1` from
`100` on, where `w` is a degree-six polynomial with exact rational coefficients and `A0` its
antiderivative. The drift condition for `V` is discharged by
exact interval integration of the piecewise polynomial (`w_integral`, `piece_eval`,
`chop_interior`) together with sign conditions on the defect polynomials `Dpoly` (interior cells),
`D99poly` (the last cell), and the constant `D100`; each polynomial sign condition is certified by
an expansion with sign-definite coefficients in the Bernstein basis on `[0, 1]` (`Dpoly_nonpos`,
`D99poly_nonpos`, and likewise `negw_nonpos`, `wsub_nonpos`, which pin `0 ≤ w ≤ 14/3`).

The main result `sound` states: started at `x = 10`, the probability that the chain ever exceeds
`100` is at most `(3/14) ^ 90`.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

set_option maxHeartbeats 1600000

namespace Qtsl.Sweep.Repulse100Uniform

noncomputable def w : ℝ → ℝ := fun t => (1 : ℝ) + (1693626053543 / 1099511627776 : ℝ) * t ^ 1 + (1306300341179 / 1099511627776 : ℝ) * t ^ 2 + (659660081731 / 1099511627776 : ℝ) * t ^ 3 + (35752243431 / 137438953472 : ℝ) * t ^ 4 + (5114061685 / 137438953472 : ℝ) * t ^ 5 + (45023300275 / 1099511627776 : ℝ) * t ^ 6

noncomputable def A0 : ℝ → ℝ := fun t => (1 : ℝ) * t ^ 1 + (1693626053543 / 2199023255552 : ℝ) * t ^ 2 + (1306300341179 / 3298534883328 : ℝ) * t ^ 3 + (659660081731 / 4398046511104 : ℝ) * t ^ 4 + (35752243431 / 687194767360 : ℝ) * t ^ 5 + (5114061685 / 824633720832 : ℝ) * t ^ 6 + (45023300275 / 7696581394432 : ℝ) * t ^ 7

noncomputable def Wb : ℝ := (366397830467499 / 153931627888640 : ℝ)

noncomputable def Dpoly : ℝ → ℝ := fun t => ((-3844357682689) / 30170599066173440 : ℝ) + ((-45816445615) / 484884627849216 : ℝ) * t ^ 1 + ((-7045616203181) / 3879077022793728 : ℝ) * t ^ 2 + (58296874462891 / 5818615534190592 : ℝ) * t ^ 3 + ((-32263742161423) / 1108307720798208 : ℝ) * t ^ 4 + (17344273780109 / 404070523207680 : ℝ) * t ^ 5 + ((-2854432541605) / 90915867721728 : ℝ) * t ^ 6 + (122328306847175 / 13576769579778048 : ℝ) * t ^ 7

noncomputable def D99poly : ℝ → ℝ := fun t => ((-11533073048067) / 422388386926428160 : ℝ) + ((-45816445615) / 2262794929963008 : ℝ) * t ^ 1 + ((-1551451835708391) / 6034119813234688 : ℝ) * t ^ 2 + ((-391799029081365) / 3017059906617344 : ℝ) * t ^ 3 + ((-96950164733325) / 1724034232352768 : ℝ) * t ^ 4 + ((-15357111544779) / 1885662441635840 : ℝ) * t ^ 5 + ((-829220915685) / 94283122081792 : ℝ) * t ^ 6 + ((-405209702475) / 21119419346321408 : ℝ) * t ^ 7

noncomputable def D100 : ℝ := ((-41654908778504431) / 90511797198520320 : ℝ)

noncomputable def negw : ℝ → ℝ := fun t => -(w t)

noncomputable def wsub : ℝ → ℝ := fun t => w t - 14/3

lemma w_integral (a b : ℝ) : ∫ t in a..b, w t = A0 b - A0 a := by
  unfold w A0
  have i0 : IntervalIntegrable (fun _t : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun t : ℝ => (1693626053543 / 1099511627776 : ℝ) * t ^ 1) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i2 : IntervalIntegrable (fun t : ℝ => (1306300341179 / 1099511627776 : ℝ) * t ^ 2) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i3 : IntervalIntegrable (fun t : ℝ => (659660081731 / 1099511627776 : ℝ) * t ^ 3) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i4 : IntervalIntegrable (fun t : ℝ => (35752243431 / 137438953472 : ℝ) * t ^ 4) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i5 : IntervalIntegrable (fun t : ℝ => (5114061685 / 137438953472 : ℝ) * t ^ 5) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  have i6 : IntervalIntegrable (fun t : ℝ => (45023300275 / 1099511627776 : ℝ) * t ^ 6) volume a b :=
    (Continuous.intervalIntegrable (by continuity) a b)
  rw [intervalIntegral.integral_add (((((i0.add i1).add i2).add i3).add i4).add i5) i6,
    intervalIntegral.integral_add ((((i0.add i1).add i2).add i3).add i4) i5,
    intervalIntegral.integral_add (((i0.add i1).add i2).add i3) i4,
    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma Dpoly_nonpos : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Dpoly t ≤ 0 := by
  intro t h0 h1
  have h2 : (0:ℝ) ≤ 1 - t := by linarith
  have key : Dpoly t = ((-3844357682689) / 30170599066173440 : ℝ) * ((1 - t) ^ 7) + ((-5466362113343) / 5541538603991040 : ℝ) * (t ^ 1 * (1 - t) ^ 6) + ((-196245713359613) / 38790770227937280 : ℝ) * (t ^ 2 * (1 - t) ^ 5) + ((-16423783788467) / 3324923162394624 : ℝ) * (t ^ 3 * (1 - t) ^ 4) + ((-22521929385535) / 1662461581197312 : ℝ) * (t ^ 4 * (1 - t) ^ 3) + ((-127053339016007) / 19395385113968640 : ℝ) * (t ^ 5 * (1 - t) ^ 2) + ((-7209565728221) / 2155042790440960 : ℝ) * (t ^ 6 * (1 - t) ^ 1) + ((-3830142649409) / 6465128371322880 : ℝ) * (t ^ 7) := by
    simp only [Dpoly, w]; ring
  have hT0 : (0:ℝ) ≤ (1 - t) ^ 7 := pow_nonneg h2 _
  have hT1 : (0:ℝ) ≤ t ^ 1 * (1 - t) ^ 6 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT2 : (0:ℝ) ≤ t ^ 2 * (1 - t) ^ 5 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT3 : (0:ℝ) ≤ t ^ 3 * (1 - t) ^ 4 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT4 : (0:ℝ) ≤ t ^ 4 * (1 - t) ^ 3 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT5 : (0:ℝ) ≤ t ^ 5 * (1 - t) ^ 2 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT6 : (0:ℝ) ≤ t ^ 6 * (1 - t) ^ 1 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT7 : (0:ℝ) ≤ t ^ 7 := pow_nonneg h0 _
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7]

lemma D99poly_nonpos : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → D99poly t ≤ 0 := by
  intro t h0 h1
  have h2 : (0:ℝ) ≤ 1 - t := by linarith
  have key : D99poly t = ((-11533073048067) / 422388386926428160 : ℝ) * ((1 - t) ^ 7) + ((-5466362113343) / 25860513485291520 : ℝ) * (t ^ 1 * (1 - t) ^ 6) + ((-15556448207526511) / 60341198132346880 : ℝ) * (t ^ 2 * (1 - t) ^ 5) + ((-2442416123158091) / 1724034232352768 : ℝ) * (t ^ 3 * (1 - t) ^ 4) + ((-8141334105682129) / 2586051348529152 : ℝ) * (t ^ 4 * (1 - t) ^ 3) + ((-106442593862212577) / 30170599066173440 : ℝ) * (t ^ 5 * (1 - t) ^ 2) + ((-60314350819089299) / 30170599066173440 : ℝ) * (t ^ 6 * (1 - t) ^ 1) + ((-41654866133404591) / 90511797198520320 : ℝ) * (t ^ 7) := by
    simp only [D99poly, w]; ring
  have hT0 : (0:ℝ) ≤ (1 - t) ^ 7 := pow_nonneg h2 _
  have hT1 : (0:ℝ) ≤ t ^ 1 * (1 - t) ^ 6 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT2 : (0:ℝ) ≤ t ^ 2 * (1 - t) ^ 5 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT3 : (0:ℝ) ≤ t ^ 3 * (1 - t) ^ 4 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT4 : (0:ℝ) ≤ t ^ 4 * (1 - t) ^ 3 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT5 : (0:ℝ) ≤ t ^ 5 * (1 - t) ^ 2 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT6 : (0:ℝ) ≤ t ^ 6 * (1 - t) ^ 1 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT7 : (0:ℝ) ≤ t ^ 7 := pow_nonneg h0 _
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7]

lemma negw_nonpos : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → negw t ≤ 0 := by
  intro t h0 h1
  have h2 : (0:ℝ) ≤ 1 - t := by linarith
  have key : negw t = ((-1) : ℝ) * ((1 - t) ^ 6) + ((-8290695820199) / 1099511627776 : ℝ) * (t ^ 1 * (1 - t) ^ 5) + ((-13133552512767) / 549755813888 : ℝ) * (t ^ 2 * (1 - t) ^ 4) + ((-44811354537397) / 1099511627776 : ℝ) * (t ^ 3 * (1 - t) ^ 3) + ((-43531735191785) / 1099511627776 : ℝ) * (t ^ 4 * (1 - t) ^ 2) + ((-1430145627041) / 68719476736 : ℝ) * (t ^ 5 * (1 - t) ^ 1) + ((-641381480679) / 137438953472 : ℝ) * (t ^ 6) := by
    simp only [negw, w]; ring
  have hT0 : (0:ℝ) ≤ (1 - t) ^ 6 := pow_nonneg h2 _
  have hT1 : (0:ℝ) ≤ t ^ 1 * (1 - t) ^ 5 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT2 : (0:ℝ) ≤ t ^ 2 * (1 - t) ^ 4 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT3 : (0:ℝ) ≤ t ^ 3 * (1 - t) ^ 3 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT4 : (0:ℝ) ≤ t ^ 4 * (1 - t) ^ 2 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT5 : (0:ℝ) ≤ t ^ 5 * (1 - t) ^ 1 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT6 : (0:ℝ) ≤ t ^ 6 := pow_nonneg h0 _
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4, hT5, hT6]

lemma wsub_nonpos : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → wsub t ≤ 0 := by
  intro t h0 h1
  have h2 : (0:ℝ) ≤ 1 - t := by linarith
  have key : wsub t = ((-11) / 3 : ℝ) * ((1 - t) ^ 6) + ((-22495629757529) / 1099511627776 : ℝ) * (t ^ 1 * (1 - t) ^ 5) + ((-25349354459393) / 549755813888 : ℝ) * (t ^ 2 * (1 - t) ^ 4) + ((-173429192165089) / 3298534883328 : ℝ) * (t ^ 3 * (1 - t) ^ 3) + ((-33434078752535) / 1099511627776 : ℝ) * (t ^ 4 * (1 - t) ^ 2) + ((-493999721567) / 68719476736 : ℝ) * (t ^ 5 * (1 - t) ^ 1) + ((-906571) / 412316860416 : ℝ) * (t ^ 6) := by
    simp only [wsub, w]; ring
  have hT0 : (0:ℝ) ≤ (1 - t) ^ 6 := pow_nonneg h2 _
  have hT1 : (0:ℝ) ≤ t ^ 1 * (1 - t) ^ 5 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT2 : (0:ℝ) ≤ t ^ 2 * (1 - t) ^ 4 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT3 : (0:ℝ) ≤ t ^ 3 * (1 - t) ^ 3 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT4 : (0:ℝ) ≤ t ^ 4 * (1 - t) ^ 2 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT5 : (0:ℝ) ≤ t ^ 5 * (1 - t) ^ 1 := mul_nonneg (pow_nonneg h0 _) (pow_nonneg h2 _)
  have hT6 : (0:ℝ) ≤ t ^ 6 := pow_nonneg h0 _
  rw [key]
  nlinarith [hT0, hT1, hT2, hT3, hT4, hT5, hT6]

noncomputable def V : ℝ → ℝ := fun x =>
  if x < -2 then 0
  else if x < 100 then (14/3 : ℝ) ^ (⌊x⌋ - 100) * w (x - ⌊x⌋)
  else 1

lemma rho_pos : (0:ℝ) < 14/3 := by norm_num

lemma rho_zpow_pos (n : ℤ) : (0:ℝ) < (14/3 : ℝ) ^ n := zpow_pos rho_pos n

lemma V_on_cell (k : ℤ) (hk : -2 ≤ k) (hk' : k ≤ 99) {s : ℝ}
    (hs : (k:ℝ) ≤ s) (hs' : s < (k:ℝ) + 1) :
    V s = (14/3 : ℝ) ^ (k - 100) * w (s - k) := by
  have hfl : ⌊s⌋ = k := Int.floor_eq_iff.2 ⟨hs, hs'⟩
  have h2 : ¬ s < -2 := by
    push Not
    calc (-2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      _ ≤ s := hs
  have h100 : s < 100 := by
    have : (k:ℝ) + 1 ≤ 100 := by exact_mod_cast (by omega : k + 1 ≤ (100:ℤ))
    linarith
  simp only [V, h2, if_false, h100, if_true, hfl]

lemma V_ge_of_100 {s : ℝ} (hs : (100:ℝ) ≤ s) : V s = 1 := by
  have h2 : ¬ s < -2 := by push Not; linarith
  have h100 : ¬ s < 100 := by push Not; exact hs
  simp only [V, h2, if_false, h100]

lemma fract_mem {x : ℝ} : 0 ≤ x - ⌊x⌋ ∧ x - ⌊x⌋ < 1 := by
  constructor
  · linarith [Int.floor_le x]
  · linarith [Int.lt_floor_add_one x]

lemma w_nonneg_on {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ w t := by
  have := negw_nonpos t h0 h1
  simp only [negw] at this
  linarith

lemma w_le_rho {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : w t ≤ 14/3 := by
  have := wsub_nonpos t h0 h1
  simp only [wsub] at this
  linarith

lemma V_nonneg : ∀ s : ℝ, 0 ≤ V s := by
  intro s
  by_cases h2 : s < -2
  · simp [V, h2]
  · by_cases h100 : s < 100
    · push Not at h2
      have := fract_mem (x := s)
      rw [show V s = (14/3 : ℝ) ^ (⌊s⌋ - 100) * w (s - ⌊s⌋) by
        simp only [V, not_lt.2 h2, if_false, h100, if_true]]
      exact mul_nonneg (rho_zpow_pos _).le (w_nonneg_on this.1 this.2.le)
    · simp [V, h2, h100]

lemma V_le_one : ∀ s : ℝ, V s ≤ 1 := by
  intro s
  by_cases h2 : s < -2
  · simp [V, h2]
  · by_cases h100 : s < 100
    · push Not at h2
      have hk99 : ⌊s⌋ ≤ 99 := by
        have h : (⌊s⌋ : ℝ) < 100 := lt_of_le_of_lt (Int.floor_le s) h100
        have h' : ⌊s⌋ < 100 := by exact_mod_cast h
        omega
      have hf := fract_mem (x := s)
      rw [show V s = (14/3 : ℝ) ^ (⌊s⌋ - 100) * w (s - ⌊s⌋) by
        simp only [V, not_lt.2 h2, if_false, h100, if_true]]
      calc (14/3 : ℝ) ^ (⌊s⌋ - 100) * w (s - ⌊s⌋)
          ≤ (14/3 : ℝ) ^ (⌊s⌋ - 100) * (14/3) :=
            mul_le_mul_of_nonneg_left (w_le_rho hf.1 hf.2.le) (rho_zpow_pos _).le
        _ = (14/3 : ℝ) ^ (⌊s⌋ - 100 + 1) := by
            rw [zpow_add_one₀ (by norm_num : (14/3:ℝ) ≠ 0)]
        _ ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    · simp [V, h2, h100]

lemma V_barrier : ∀ s ∈ Set.Ioi (100:ℝ), 1 ≤ V s := by
  intro s hs
  rw [V_ge_of_100 (le_of_lt hs)]

lemma V_measurable : Measurable V := by
  unfold V
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  refine Measurable.mul ?_ ?_
  · exact (Measurable.of_discrete
      (f := fun k : ℤ => (14/3 : ℝ) ^ (k - 100))).comp Int.measurable_floor
  · have hw : Continuous w := by unfold w; continuity
    have : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
    have heq : (fun x : ℝ => w (x - ⌊x⌋)) = w ∘ Int.fract := by
      funext x; simp [Int.self_sub_floor]
    rw [heq]
    exact hw.measurable.comp this

lemma V_intervalIntegrable (a b : ℝ) : IntervalIntegrable V volume a b := by
  constructor <;>
  · refine (integrable_const (1:ℝ)).mono' V_measurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (V_nonneg s)]
    exact V_le_one s

lemma piece_eval (m : ℤ) (hm : -2 ≤ m) (hm' : m ≤ 99) {a b : ℝ}
    (hma : (m:ℝ) ≤ a) (hab : a ≤ b) (hbm : b ≤ (m:ℝ) + 1) :
    ∫ s in a..b, V s = (14/3 : ℝ) ^ (m - 100) * (A0 (b - m) - A0 (a - m)) := by
  have hcong : ∫ s in a..b, V s
      = ∫ s in a..b, (14/3 : ℝ) ^ (m - 100) * w (s - m) := by
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {((m:ℝ) + 1)} = 0 := measure_singleton _
    filter_upwards [compl_mem_ae_iff.2 hnull] with s hs hsI
    rw [Set.uIoc_of_le hab] at hsI
    have hs1 : (m:ℝ) ≤ s := le_trans hma (le_of_lt hsI.1)
    have hs2 : s < (m:ℝ) + 1 :=
      lt_of_le_of_ne (le_trans hsI.2 hbm) (by simpa using hs)
    exact V_on_cell m hm hm' hs1 hs2
  rw [hcong, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun t => w t) (m:ℝ), w_integral]

noncomputable def eta : Measure ℝ :=
  ENNReal.ofReal (1/3) • volume.restrict (Set.Icc (-2) 1)

instance : IsProbabilityMeasure eta := by
  constructor
  simp only [eta, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, smul_eq_mul]
  rw [show (1:ℝ) - (-2) = 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

noncomputable def step : ℝ → Measure ℝ := fun x =>
  if 0 ≤ x ∧ x ≤ 100 then Measure.map (fun u => x + u) eta else Measure.dirac x

lemma step_prob : ∀ x, IsProbabilityMeasure (step x) := by
  intro x
  unfold step
  split_ifs
  · exact Measure.isProbabilityMeasure_map (measurable_const_add x).aemeasurable
  · infer_instance

lemma step_measurable : Measurable step := by
  rw [Measure.measurable_measure]
  intro B hB
  have hset : MeasurableSet {x : ℝ | 0 ≤ x ∧ x ≤ 100} := by
    have h : {x : ℝ | 0 ≤ x ∧ x ≤ 100} = Set.Icc 0 100 := by
      ext y
      simp [Set.mem_Icc, Set.mem_setOf_eq]
    rw [h]
    exact measurableSet_Icc
  have hsplit : (fun x => step x B)
      = fun x => if 0 ≤ x ∧ x ≤ 100
          then (Measure.map (fun u => x + u) eta) B else Measure.dirac x B := by
    funext x
    unfold step
    exact apply_ite (fun μ : Measure ℝ => μ B) _ _ _
  rw [hsplit]
  refine Measurable.ite hset ?_ ?_
  · have hmap : ∀ x : ℝ, (Measure.map (fun u => x + u) eta) B
        = ∫⁻ u, B.indicator (fun _ => (1:ℝ≥0∞)) (x + u) ∂eta := by
      intro x
      rw [Measure.map_apply (measurable_const_add x) hB,
        ← lintegral_indicator_one ((measurable_const_add x) hB)]
      congr 1
    simp only [hmap]
    have : Measurable fun p : ℝ × ℝ => B.indicator (fun _ => (1:ℝ≥0∞)) (p.1 + p.2) :=
      (measurable_one.indicator hB).comp measurable_add
    exact this.lintegral_prod_right'
  · have h : (fun x : ℝ => (Measure.dirac x) B)
        = B.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x; exact Measure.dirac_apply' x hB
    rw [h]; exact measurable_one.indicator hB

noncomputable def stepK : Kernel ℝ ℝ := ⟨step, step_measurable⟩

instance : IsMarkovKernel stepK := ⟨fun x => step_prob x⟩

@[simp] lemma stepK_apply (x : ℝ) : stepK x = step x := rfl

lemma step_integral {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 100) :
    ∫ z, V z ∂(step x) = (1/3) * ∫ s in (x-2)..(x+1), V s := by
  rw [show step x = Measure.map (fun u => x + u) eta by simp [step, h0, h1]]
  rw [integral_map (measurable_const_add x).aemeasurable
    V_measurable.aestronglyMeasurable]
  unfold eta
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
  have hIoc : ∫ u, V (x + u) ∂(volume.restrict (Set.Icc (-2:ℝ) 1))
      = ∫ u in (-2:ℝ)..1, V (x + u) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-2:ℝ) ≤ 1)]
    exact integral_Icc_eq_integral_Ioc
  rw [hIoc, intervalIntegral.integral_comp_add_left (fun s => V s) x,
    show x + (-2:ℝ) = x - 2 by ring, smul_eq_mul]

lemma chop_interior (k : ℤ) (hk0 : 0 ≤ k) (hk98 : k ≤ 98) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫ s in ((k:ℝ) + t - 2)..((k:ℝ) + t + 1), V s
      = (14/3 : ℝ) ^ (k - 100) *
        ((9/196) * (Wb - A0 t) + (3/14) * Wb + Wb + (14/3) * A0 t) := by
  have hne : (14/3 : ℝ) ≠ 0 := by norm_num
  have c1 : ((k:ℝ) + t - 2) ≤ ((k:ℝ) - 1) := by linarith
  have c2 : ((k:ℝ) - 1) ≤ (k:ℝ) := by linarith
  have c3 : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
  have c4 : (k:ℝ) + 1 ≤ (k:ℝ) + t + 1 := by linarith

  have hsplit :
      (∫ s in ((k:ℝ) + t - 2)..((k:ℝ) - 1), V s)
        + (∫ s in ((k:ℝ) - 1)..(k:ℝ), V s)
        + (∫ s in (k:ℝ)..((k:ℝ) + 1), V s)
        + (∫ s in ((k:ℝ) + 1)..((k:ℝ) + t + 1), V s)
      = ∫ s in ((k:ℝ) + t - 2)..((k:ℝ) + t + 1), V s := by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (V_intervalIntegrable _ _) (V_intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
        (V_intervalIntegrable _ _) (V_intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
        (V_intervalIntegrable _ _) (V_intervalIntegrable _ _)]
  rw [← hsplit]

  have p1 : ∫ s in ((k:ℝ) + t - 2)..((k:ℝ) - 1), V s
      = (14/3 : ℝ) ^ (k - 102) * (Wb - A0 t) := by
    have := piece_eval (k - 2) (by omega) (by omega)
      (a := (k:ℝ) + t - 2) (b := (k:ℝ) - 1)
      (by push_cast; linarith) c1 (by push_cast; linarith)
    rw [this]
    have e1 : ((k:ℝ) - 1) - ((k - 2 : ℤ) : ℝ) = 1 := by push_cast; ring
    have e2 : ((k:ℝ) + t - 2) - ((k - 2 : ℤ) : ℝ) = t := by push_cast; ring
    rw [e1, e2, show A0 1 = Wb by unfold A0 Wb; norm_num,
      show (k - 2 - 100 : ℤ) = k - 102 by ring]
  have p2 : ∫ s in ((k:ℝ) - 1)..(k:ℝ), V s = (14/3 : ℝ) ^ (k - 101) * Wb := by
    have := piece_eval (k - 1) (by omega) (by omega)
      (a := (k:ℝ) - 1) (b := (k:ℝ))
      (by push_cast; linarith) c2 (by push_cast; linarith)
    rw [this]
    have e1 : ((k:ℝ)) - ((k - 1 : ℤ) : ℝ) = 1 := by push_cast; ring
    have e2 : ((k:ℝ) - 1) - ((k - 1 : ℤ) : ℝ) = 0 := by push_cast; ring
    rw [e1, e2, show A0 1 = Wb by unfold A0 Wb; norm_num,
      show A0 0 = 0 by unfold A0; norm_num, sub_zero,
      show (k - 1 - 100 : ℤ) = k - 101 by ring]
  have p3 : ∫ s in (k:ℝ)..((k:ℝ) + 1), V s = (14/3 : ℝ) ^ (k - 100) * Wb := by
    have := piece_eval k (by omega) (by omega)
      (a := (k:ℝ)) (b := (k:ℝ) + 1) le_rfl c3 le_rfl
    rw [this]
    rw [show ((k:ℝ) + 1) - (k:ℝ) = 1 by ring, show ((k:ℝ)) - (k:ℝ) = 0 by ring,
      show A0 1 = Wb by unfold A0 Wb; norm_num, show A0 0 = 0 by unfold A0; norm_num,
      sub_zero]
  have p4 : ∫ s in ((k:ℝ) + 1)..((k:ℝ) + t + 1), V s
      = (14/3 : ℝ) ^ (k - 99) * A0 t := by
    have := piece_eval (k + 1) (by omega) (by omega)
      (a := (k:ℝ) + 1) (b := (k:ℝ) + t + 1)
      (by push_cast; linarith) c4 (by push_cast; linarith)
    rw [this]
    have e1 : ((k:ℝ) + t + 1) - ((k + 1 : ℤ) : ℝ) = t := by push_cast; ring
    have e2 : ((k:ℝ) + 1) - ((k + 1 : ℤ) : ℝ) = 0 := by push_cast; ring
    rw [e1, e2, show A0 0 = 0 by unfold A0; norm_num, sub_zero,
      show (k + 1 - 100 : ℤ) = k - 99 by ring]
  rw [p1, p2, p3, p4]

  have f1 : (14/3 : ℝ) ^ (k - 102) = (14/3 : ℝ) ^ (k - 100) * (9/196) := by
    rw [show k - 102 = (k - 100) + (-2) by ring, zpow_add₀ hne]
    norm_num [zpow_neg]
  have f2 : (14/3 : ℝ) ^ (k - 101) = (14/3 : ℝ) ^ (k - 100) * (3/14) := by
    rw [show k - 101 = (k - 100) + (-1) by ring, zpow_add₀ hne]
    norm_num [zpow_neg]
  have f3 : (14/3 : ℝ) ^ (k - 99) = (14/3 : ℝ) ^ (k - 100) * (14/3) := by
    rw [show k - 99 = (k - 100) + 1 by ring, zpow_add₀ hne]
    norm_num
  rw [f1, f2, f3]
  ring

lemma D_identity (t : ℝ) :
    (1/3) * ((9/196) * (Wb - A0 t) + (3/14) * Wb + Wb + (14/3) * A0 t) - w t
      = Dpoly t := by
  unfold Wb A0 w Dpoly; ring

lemma D99_identity (t : ℝ) :
    (1/3) * ((27/2744) * (Wb - A0 t) + (9/196) * Wb + (3/14) * Wb + t)
      - (3/14) * w t = D99poly t := by
  unfold Wb A0 w D99poly; ring

lemma D100_identity : (1/3) * ((9/196) * Wb + (3/14) * Wb + 1) - 1 = D100 := by
  unfold Wb D100; norm_num

lemma V_drift : ∀ x : ℝ, x ∉ Set.Ioi (100:ℝ) → ∫ z, V z ∂(step x) ≤ V x := by
  intro x hx
  simp only [Set.mem_Ioi, not_lt] at hx
  by_cases hact : 0 ≤ x
  swap
  · rw [show step x = Measure.dirac x by simp [step, hact], integral_dirac]
  rcases eq_or_lt_of_le hx with h100 | hlt
  ·
    rw [h100] at hact ⊢
    rw [step_integral hact le_rfl]
    have hsplit :
        (∫ s in (98:ℝ)..(99:ℝ), V s) + (∫ s in (99:ℝ)..(100:ℝ), V s)
          + (∫ s in (100:ℝ)..(101:ℝ), V s)
        = ∫ s in (98:ℝ)..(101:ℝ), V s := by
      rw [intervalIntegral.integral_add_adjacent_intervals
          (V_intervalIntegrable _ _) (V_intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
          (V_intervalIntegrable _ _) (V_intervalIntegrable _ _)]
    have q1 : ∫ s in (98:ℝ)..(99:ℝ), V s = (9/196 : ℝ) * Wb := by
      have h := piece_eval 98 (by omega) (by omega) (a := (98:ℝ)) (b := (99:ℝ))
        (by norm_num) (by norm_num) (by norm_num)
      rw [h, show ((99:ℝ) - ((98:ℤ):ℝ)) = 1 by push_cast; ring,
        show ((98:ℝ) - ((98:ℤ):ℝ)) = 0 by push_cast; ring,
        show A0 1 = Wb by unfold A0 Wb; norm_num,
        show A0 0 = 0 by unfold A0; norm_num, sub_zero,
        show (98 - 100 : ℤ) = (-2 : ℤ) by ring,
        show (14/3 : ℝ) ^ (-2 : ℤ) = 9/196 by norm_num [zpow_neg]]
    have q2 : ∫ s in (99:ℝ)..(100:ℝ), V s = (3/14 : ℝ) * Wb := by
      have h := piece_eval 99 (by omega) (by omega) (a := (99:ℝ)) (b := (100:ℝ))
        (by norm_num) (by norm_num) (by norm_num)
      rw [h, show ((100:ℝ) - ((99:ℤ):ℝ)) = 1 by push_cast; ring,
        show ((99:ℝ) - ((99:ℤ):ℝ)) = 0 by push_cast; ring,
        show A0 1 = Wb by unfold A0 Wb; norm_num,
        show A0 0 = 0 by unfold A0; norm_num, sub_zero,
        show (99 - 100 : ℤ) = (-1 : ℤ) by ring,
        show (14/3 : ℝ) ^ (-1 : ℤ) = 3/14 by norm_num [zpow_neg]]
    have q3 : ∫ s in (100:ℝ)..(101:ℝ), V s = 1 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (fun s hs => by
        rw [Set.uIcc_of_le (by norm_num : (100:ℝ) ≤ 101)] at hs
        exact V_ge_of_100 hs.1)]
      norm_num
    rw [show (100:ℝ) - 2 = 98 by norm_num, show (100:ℝ) + 1 = 101 by norm_num,
      ← hsplit, q1, q2, q3, V_ge_of_100 le_rfl]
    have hkey := D100_identity
    have hD : D100 ≤ 0 := by unfold D100; norm_num
    linarith
  ·
    have hfl := Int.floor_le x
    have hfl1 := Int.lt_floor_add_one x
    have hk0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.2 hact
    have hk99 : ⌊x⌋ ≤ 99 := by
      have h : (⌊x⌋ : ℝ) < 100 := lt_of_le_of_lt hfl hlt
      have h' : ⌊x⌋ < 100 := by exact_mod_cast h
      omega
    have hfr := fract_mem (x := x)
    have hVx : V x = (14/3 : ℝ) ^ (⌊x⌋ - 100) * w (x - ⌊x⌋) :=
      V_on_cell ⌊x⌋ (by omega) hk99 hfl hfl1
    rw [step_integral hact hx, hVx]
    rcases lt_or_ge ⌊x⌋ 99 with hk98 | hk99'
    ·
      have hchop := chop_interior ⌊x⌋ hk0 (by omega) hfr.1 hfr.2
      rw [show ((⌊x⌋:ℝ) + (x - ⌊x⌋) - 2) = x - 2 by ring,
        show ((⌊x⌋:ℝ) + (x - ⌊x⌋) + 1) = x + 1 by ring] at hchop
      rw [hchop]
      have hstep : (1/3) * ((9/196) * (Wb - A0 (x - ⌊x⌋)) + (3/14) * Wb + Wb
          + (14/3) * A0 (x - ⌊x⌋)) ≤ w (x - ⌊x⌋) := by
        have hD := Dpoly_nonpos (x - ⌊x⌋) hfr.1 hfr.2.le
        have hkey := D_identity (x - ⌊x⌋)
        linarith
      calc (1/3) * ((14/3 : ℝ) ^ (⌊x⌋ - 100) *
            ((9/196) * (Wb - A0 (x - ⌊x⌋)) + (3/14) * Wb + Wb
              + (14/3) * A0 (x - ⌊x⌋)))
          = (14/3 : ℝ) ^ (⌊x⌋ - 100) * ((1/3) * ((9/196) * (Wb - A0 (x - ⌊x⌋))
              + (3/14) * Wb + Wb + (14/3) * A0 (x - ⌊x⌋))) := by ring
        _ ≤ (14/3 : ℝ) ^ (⌊x⌋ - 100) * w (x - ⌊x⌋) :=
            mul_le_mul_of_nonneg_left hstep (rho_zpow_pos _).le
    ·
      have hk : ⌊x⌋ = 99 := by omega
      have hx99 : (99:ℝ) ≤ x := by
        have := hfl; rw [hk] at this; exact_mod_cast this
      rw [hk]
      rw [show ((99:ℤ) - 100) = (-1 : ℤ) by ring,
        show (14/3 : ℝ) ^ (-1 : ℤ) = 3/14 by norm_num [zpow_neg],
        show ((x : ℝ) - ((99:ℤ):ℝ)) = x - 99 by push_cast; ring]
      have hsplit :
          (∫ s in (x - 2)..(98:ℝ), V s) + (∫ s in (98:ℝ)..(99:ℝ), V s)
            + (∫ s in (99:ℝ)..(100:ℝ), V s) + (∫ s in (100:ℝ)..(x + 1), V s)
          = ∫ s in (x - 2)..(x + 1), V s := by
        rw [intervalIntegral.integral_add_adjacent_intervals
            (V_intervalIntegrable _ _) (V_intervalIntegrable _ _),
          intervalIntegral.integral_add_adjacent_intervals
            (V_intervalIntegrable _ _) (V_intervalIntegrable _ _),
          intervalIntegral.integral_add_adjacent_intervals
            (V_intervalIntegrable _ _) (V_intervalIntegrable _ _)]
      rw [← hsplit]
      have p1 : ∫ s in (x - 2)..(98:ℝ), V s
          = (27/2744 : ℝ) * (Wb - A0 (x - 99)) := by
        have h := piece_eval 97 (by omega) (by omega) (a := x - 2) (b := (98:ℝ))
          (by push_cast; linarith) (by linarith) (by push_cast; norm_num)
        rw [h, show ((98:ℝ) - ((97:ℤ):ℝ)) = 1 by push_cast; ring,
          show ((x - 2) - ((97:ℤ):ℝ)) = x - 99 by push_cast; ring,
          show A0 1 = Wb by unfold A0 Wb; norm_num,
          show (97 - 100 : ℤ) = (-3 : ℤ) by ring,
          show (14/3 : ℝ) ^ (-3 : ℤ) = 27/2744 by norm_num [zpow_neg]]
      have p2 : ∫ s in (98:ℝ)..(99:ℝ), V s = (9/196 : ℝ) * Wb := by
        have h := piece_eval 98 (by omega) (by omega) (a := (98:ℝ)) (b := (99:ℝ))
          (by norm_num) (by norm_num) (by norm_num)
        rw [h, show ((99:ℝ) - ((98:ℤ):ℝ)) = 1 by push_cast; ring,
          show ((98:ℝ) - ((98:ℤ):ℝ)) = 0 by push_cast; ring,
          show A0 1 = Wb by unfold A0 Wb; norm_num,
          show A0 0 = 0 by unfold A0; norm_num, sub_zero,
          show (98 - 100 : ℤ) = (-2 : ℤ) by ring,
          show (14/3 : ℝ) ^ (-2 : ℤ) = 9/196 by norm_num [zpow_neg]]
      have p3 : ∫ s in (99:ℝ)..(100:ℝ), V s = (3/14 : ℝ) * Wb := by
        have h := piece_eval 99 (by omega) (by omega) (a := (99:ℝ)) (b := (100:ℝ))
          (by norm_num) (by norm_num) (by norm_num)
        rw [h, show ((100:ℝ) - ((99:ℤ):ℝ)) = 1 by push_cast; ring,
          show ((99:ℝ) - ((99:ℤ):ℝ)) = 0 by push_cast; ring,
          show A0 1 = Wb by unfold A0 Wb; norm_num,
          show A0 0 = 0 by unfold A0; norm_num, sub_zero,
          show (99 - 100 : ℤ) = (-1 : ℤ) by ring,
          show (14/3 : ℝ) ^ (-1 : ℤ) = 3/14 by norm_num [zpow_neg]]
      have p4 : ∫ s in (100:ℝ)..(x + 1), V s = x - 99 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (fun s hs => by
          rw [Set.uIcc_of_le (by linarith : (100:ℝ) ≤ x + 1)] at hs
          exact V_ge_of_100 hs.1)]
        simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        ring
      rw [p1, p2, p3, p4]
      have hD := D99poly_nonpos (x - 99) (by linarith) (by linarith)
      have hkey := D99_identity (x - 99)
      linarith

theorem sound :
    Battery.pathMeasure stepK (10:ℝ) {ω | ∃ n, ω n ∈ Set.Ioi (100:ℝ)}
      ≤ ENNReal.ofReal ((3/14 : ℝ) ^ (90 : ℕ)) := by
  have h := Battery.measure_reach_le (K := stepK) (f := V) (A := Set.Ioi (100:ℝ))
    (C := 1) measurableSet_Ioi V_measurable V_nonneg V_le_one V_barrier
    (fun y hy => by rw [stepK_apply]; exact V_drift y hy) (10:ℝ)
  have hV10 : V 10 = (3/14 : ℝ) ^ (90 : ℕ) := by
    have h := V_on_cell 10 (by omega) (by omega) (s := (10:ℝ))
      (by norm_num) (by norm_num)
    rw [h, show ((10:ℝ) - ((10:ℤ):ℝ)) = 0 by push_cast; ring,
      show w 0 = 1 by unfold w; norm_num, mul_one,
      show ((10:ℤ) - 100) = -((90:ℕ) : ℤ) by norm_num,
      zpow_neg, zpow_natCast, ← inv_pow,
      show ((14/3:ℝ))⁻¹ = 3/14 by norm_num]
  rw [hV10] at h
  exact h

end Qtsl.Sweep.Repulse100Uniform

