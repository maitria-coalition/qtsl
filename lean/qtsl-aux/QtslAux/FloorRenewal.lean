import QtslAux.GaugeSmallGain

/-! # Floor lemmas for gauged p-norms and renewal-style reach bounds

Two small toolkits supporting gauge-composition arguments.

*Gauged p-norm floors* (`Qtsl.Gauge`): for the two-argument
`pnorm p a b = (a^p + b^p)^(1/p)`:

* `pnorm_comm`: symmetry in the two arguments.
* `le_pnorm_left`, `le_pnorm_right`: each coordinate is a lower bound, so a
  floor on either coordinate is a floor on the composite.
* `pnorm_jump_nonexpansive`: a jump satisfying the gauge repayment condition
  (dwell time `δ ≤ τ` and clock bound `c ≤ 1 + η * δ`) does not increase the
  gauged p-norm composite with any fixed second coordinate.

*Renewal bounds* (`Qtsl.Renewal`): for events `A k` (a hit during
the `k`-th excursion) and `R k` (the `k`-th excursion is launched):

* `renewal_geometric_bound`: if each hit probability is at most `v` times
  the launch probability and launches decay geometrically with ratio `r`,
  then `μ (⋃ k, A k) ≤ v * (1 - r)⁻¹` (in `ℝ≥0∞`).
* `renewal_reach_bound`: the variant with a separately-bounded zeroth event,
  giving `μ T ≤ q₀ + v * (1 - r)⁻¹` for any target `T` covered by the `A k`.
-/

open scoped NNReal ENNReal MeasureTheory

namespace Qtsl.Gauge

theorem pnorm_comm (p a b : ℝ) : pnorm p a b = pnorm p b a := by
  simp [pnorm, add_comm]

theorem le_pnorm_left {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ≤ pnorm p a b :=
  le_trans (le_max_left a b) (pnorm_max_le hp ha hb).1

theorem le_pnorm_right {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b ≤ pnorm p a b :=
  le_trans (le_max_right a b) (pnorm_max_le hp ha hb).1

theorem pnorm_jump_nonexpansive {p η δ τ c V V' B : ℝ} (hp : 1 ≤ p)
    (hδ : 0 < δ) (hdwell : δ ≤ τ) (hclock : c ≤ 1 + η * δ)
    (hV : 0 ≤ V) (hV' : 0 ≤ V') (hjump : V' ≤ c * V) (hB : 0 ≤ B) :
    pnorm p (ψ η δ 0 * V') B ≤ pnorm p (ψ η δ τ * V) B := by
  have h0 : 0 ≤ ψ η δ 0 * V' := by rw [ψ_zero hδ.le, one_mul]; exact hV'
  exact pnorm_mono hp h0 hB (gauge_repayment hδ hdwell hclock hV hjump) le_rfl

end Qtsl.Gauge

namespace Qtsl.Renewal

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem renewal_geometric_bound {A R : ℕ → Set Ω} {v r : ℝ≥0∞}
    (hR0 : μ (R 0) ≤ 1)
    (hhit : ∀ k, μ (A k) ≤ v * μ (R k))
    (hlaunch : ∀ k, μ (R (k + 1)) ≤ r * μ (R k)) :
    μ (⋃ k, A k) ≤ v * (1 - r)⁻¹ := by
  have hRk : ∀ k, μ (R k) ≤ r ^ k := by
    intro k
    induction k with
    | zero => simpa using hR0
    | succ n ih =>
        calc μ (R (n + 1)) ≤ r * μ (R n) := hlaunch n
          _ ≤ r * r ^ n := mul_le_mul' le_rfl ih
          _ = r ^ (n + 1) := (pow_succ' r n).symm
  calc μ (⋃ k, A k) ≤ ∑' k, μ (A k) := measure_iUnion_le A
    _ ≤ ∑' k, v * r ^ k :=
        ENNReal.tsum_le_tsum fun k =>
          le_trans (hhit k) (mul_le_mul' le_rfl (hRk k))
    _ = v * ∑' k, r ^ k := ENNReal.tsum_mul_left
    _ = v * (1 - r)⁻¹ := by rw [ENNReal.tsum_geometric]

theorem renewal_reach_bound {T : Set Ω} {A R : ℕ → Set Ω} {q₀ v r : ℝ≥0∞}
    (hcover : T ⊆ ⋃ k, A k)
    (hA0 : μ (A 0) ≤ q₀)
    (hR0 : μ (R 0) ≤ 1)
    (hhit : ∀ k, μ (A (k + 1)) ≤ v * μ (R k))
    (hlaunch : ∀ k, μ (R (k + 1)) ≤ r * μ (R k)) :
    μ T ≤ q₀ + v * (1 - r)⁻¹ := by
  have hsplit : T ⊆ A 0 ∪ ⋃ k, A (k + 1) := by
    intro ω hω
    rcases Set.mem_iUnion.1 (hcover hω) with ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ n => exact Or.inr (Set.mem_iUnion.2 ⟨n, hk⟩)
  calc μ T ≤ μ (A 0 ∪ ⋃ k, A (k + 1)) := measure_mono hsplit
    _ ≤ μ (A 0) + μ (⋃ k, A (k + 1)) := measure_union_le _ _
    _ ≤ q₀ + v * (1 - r)⁻¹ :=
        add_le_add hA0 (renewal_geometric_bound hR0 hhit hlaunch)

end Qtsl.Renewal

#print axioms Qtsl.Gauge.pnorm_comm
#print axioms Qtsl.Gauge.le_pnorm_left
#print axioms Qtsl.Gauge.le_pnorm_right
#print axioms Qtsl.Gauge.pnorm_jump_nonexpansive
#print axioms Qtsl.Renewal.renewal_geometric_bound
#print axioms Qtsl.Renewal.renewal_reach_bound
