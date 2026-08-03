import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Rational chart covers of the unit circle

This module covers the unit circle by two rational (Weierstrass-substitution
style) charts and proves exact coverage statements for arcs, so that
polynomial certificates stated in a chart parameter transfer to the circle.

Main definitions:

* `phiNeg s = ((s² - 1) / (1 + s²), 2s / (1 + s²))`: a rational
  parameterization of the left half-circle (`a ≤ 0`) by `s ∈ [-1, 1]`.
* `phiPos t`: the mirrored chart for the right half-circle.
* `chartB s = 2s / (1 + s²)`: the second (height) coordinate of the charts.

Main results:

* `phiNeg_mem_circle`: the chart lands on the unit circle.
* `chartB_strictMonoOn`: the height coordinate is strictly monotone on
  `[-1, 1]`, so parameter intervals correspond exactly to height intervals.
* `exists_phiNeg`, `phiNeg_covers_arc`: every point of the left half-circle
  is hit, and an arc prescribed by height bounds is covered by an explicit
  parameter interval whose endpoints dominate the heights.
* `chartPair_covers_circle`: the two charts together cover the whole circle.
* `covers_x5_arc`, `covers_x5_tube`, `covers_x5_ball_arc`: concrete
  numerically-checked arc covers with explicit rational parameter windows.
-/

noncomputable section

namespace Qtsl
namespace ChartCover

def phiNeg (s : ℝ) : ℝ × ℝ :=
  ((s ^ 2 - 1) / (1 + s ^ 2), 2 * s / (1 + s ^ 2))

def phiPos (t : ℝ) : ℝ × ℝ :=
  ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2))

def chartB (s : ℝ) : ℝ := 2 * s / (1 + s ^ 2)

theorem one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by positivity

theorem one_add_sq_ne' (s : ℝ) : 1 + s ^ 2 ≠ 0 := (one_add_sq_pos s).ne'

@[simp] theorem phiNeg_snd (s : ℝ) : (phiNeg s).2 = chartB s := rfl

theorem phiNeg_mem_circle (s : ℝ) :
    (phiNeg s).1 ^ 2 + (phiNeg s).2 ^ 2 = 1 := by
  have h := one_add_sq_ne' s
  unfold phiNeg
  field_simp
  ring

theorem phiNeg_fst_nonpos {s : ℝ} (hs : s ^ 2 ≤ 1) : (phiNeg s).1 ≤ 0 :=
  div_nonpos_iff.mpr (Or.inr ⟨by linarith, (one_add_sq_pos s).le⟩)

theorem chartB_strictMonoOn : StrictMonoOn chartB (Set.Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxy1 : (0 : ℝ) < 1 - x * y := by
    nlinarith [mul_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ 1 + x)
      (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  unfold chartB
  rw [div_lt_div_iff₀ (one_add_sq_pos x) (one_add_sq_pos y)]
  nlinarith [mul_pos (sub_pos.mpr hxy) hxy1]

theorem exists_phiNeg {a b : ℝ} (ha : a ≤ 0) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ s : ℝ, s ^ 2 ≤ 1 ∧ phiNeg s = (a, b) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1a' : (1 : ℝ) - a ≠ 0 := h1a.ne'
  have hb2 : b ^ 2 = (1 + a) * (1 - a) := by linear_combination hab
  have hd : 1 + (b / (1 - a)) ^ 2 = 2 / (1 - a) := by
    rw [div_pow, hb2]
    field_simp
    ring
  refine ⟨b / (1 - a), ?_, ?_⟩
  · rw [div_pow, div_le_one (by positivity), hb2]
    nlinarith [mul_nonneg h1a.le (neg_nonneg.mpr ha)]
  · unfold phiNeg
    refine Prod.ext ?_ ?_
    · show ((b / (1 - a)) ^ 2 - 1) / (1 + (b / (1 - a)) ^ 2) = a
      rw [hd, div_pow, hb2]
      field_simp
      ring
    · show 2 * (b / (1 - a)) / (1 + (b / (1 - a)) ^ 2) = b
      rw [hd]
      field_simp

theorem phiNeg_covers_arc (sLo sHi bLo bHi : ℝ)
    (hLo : -1 ≤ sLo) (hLoHi : sLo ≤ sHi) (hHi : sHi ≤ 1)
    (hreachLo : chartB sLo ≤ bLo) (hreachHi : bHi ≤ chartB sHi) :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → a ≤ 0 → bLo ≤ b → b ≤ bHi →
      ∃ s : ℝ, sLo ≤ s ∧ s ≤ sHi ∧ phiNeg s = (a, b) := by
  intro a b hab ha hblo hbhi
  obtain ⟨s, hs1, hphi⟩ := exists_phiNeg ha hab
  have hsIcc : s ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by nlinarith [sq_nonneg (s + 1)], by nlinarith [sq_nonneg (s - 1)]⟩
  have hBs : chartB s = b := by rw [← phiNeg_snd, hphi]
  refine ⟨s, ?_, ?_, hphi⟩
  · exact (chartB_strictMonoOn.le_iff_le ⟨hLo, hLoHi.trans hHi⟩ hsIcc).mp
      (by rw [hBs]; linarith)
  · exact (chartB_strictMonoOn.le_iff_le hsIcc ⟨hLo.trans hLoHi, hHi⟩).mp
      (by rw [hBs]; linarith)

theorem phiPos_eq_neg_fst (t : ℝ) :
    phiPos t = (-(phiNeg t).1, (phiNeg t).2) := by
  unfold phiPos phiNeg
  simp only [Prod.mk.injEq]
  exact ⟨by ring, trivial⟩

theorem chartPair_covers_circle (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∃ s : ℝ, -1 ≤ s ∧ s ≤ 1 ∧ phiNeg s = (a, b)) ∨
    (∃ t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ phiPos t = (a, b)) := by
  rcases le_total a 0 with ha | ha
  · left
    obtain ⟨s, hs1, hphi⟩ := exists_phiNeg ha hab
    exact ⟨s, by nlinarith [sq_nonneg (s + 1)],
      by nlinarith [sq_nonneg (s - 1)], hphi⟩
  · right
    have hab' : (-a) ^ 2 + b ^ 2 = 1 := by linear_combination hab
    obtain ⟨t, ht1, hphi⟩ := exists_phiNeg (neg_nonpos.mpr ha) hab'
    refine ⟨t, by nlinarith [sq_nonneg (t + 1)],
      by nlinarith [sq_nonneg (t - 1)], ?_⟩
    rw [phiPos_eq_neg_fst, hphi]
    show (-(-a), b) = (a, b)
    rw [neg_neg]

theorem covers_x5_arc :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → a ≤ 0 → -(23 / 25) ≤ b → b ≤ 1 / 12 →
      ∃ s : ℝ, -(2 / 3) ≤ s ∧ s ≤ 1 / 20 ∧ phiNeg s = (a, b) :=
  phiNeg_covers_arc (-(2 / 3)) (1 / 20) (-(23 / 25)) (1 / 12)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [chartB]) (by norm_num [chartB])

theorem covers_x5_tube :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → a ≤ 0 → -(1 / 25) ≤ b → b ≤ 1 / 25 →
      ∃ s : ℝ, -(1 / 48) ≤ s ∧ s ≤ 1 / 48 ∧ phiNeg s = (a, b) :=
  phiNeg_covers_arc (-(1 / 48)) (1 / 48) (-(1 / 25)) (1 / 25)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [chartB]) (by norm_num [chartB])

theorem covers_x5_ball_arc :
    ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → a ≤ 0 → -(13 / 20) ≤ b → b ≤ 1 / 12 →
      ∃ s : ℝ, -(3 / 8) ≤ s ∧ s ≤ 1 / 20 ∧ phiNeg s = (a, b) :=
  phiNeg_covers_arc (-(3 / 8)) (1 / 20) (-(13 / 20)) (1 / 12)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [chartB]) (by norm_num [chartB])

end ChartCover
end Qtsl
