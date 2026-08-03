import SuFunctor.Adequacy.DtmcAbsorb

/-! # Geometric templates collapse to one inequality

The checker-side warrant for template-shaped contraction certificates
on chains with structured (offset-invariant) row families: under the
geometric template `V(n) = M·γⁿ`, the per-state contraction inequality
`∑ i, wᵢ · V(n + dᵢ) ≤ c · V(n)` holds at *every* template instance
`n` as soon as the ONE collapsed rational inequality
`∑ i, wᵢ · γ^{dᵢ} ≤ c` holds — so a region whose instances are
indexed by an unbounded counter is checkable by a finite scan of
exact-rational facts.

Offsets are integers (`zpow`), so counting-up and counting-down
families both collapse.  The weights carry no sign hypothesis (a
template row may aggregate signed terms); the load-bearing side
conditions are `0 ≤ M` and `0 < γ`, and each is genuinely necessary —
a negative mass flips the factored inequality, and a negative ratio
flips sign with the parity of `n`.

Only this direction is a soundness obligation: a checker verifies the
collapsed inequality, and soundness needs every instance.  The
converse (an instance implying the collapsed form) would need
`0 < M` to divide, and is nobody's obligation. -/

namespace SuFunctor
namespace Adequacy

open Finset

/-- **Template collapse**: one verified rational inequality on the
template's profile — `∑ i, wᵢ · γ^{dᵢ} ≤ c` — yields the per-state
contraction inequality at every instance `n` of the geometric template
`V(n) = M·γⁿ`. -/
theorem genFormTemplate_collapse {ι : Type} [Fintype ι]
    (w : ι → ℚ) (d : ι → ℤ) {M γ c : ℚ} (hM : 0 ≤ M) (hγ : 0 < γ)
    (h : (∑ i, w i * γ ^ d i) ≤ c) (n : ℤ) :
    (∑ i, w i * (M * γ ^ (n + d i))) ≤ c * (M * γ ^ n) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hfac : (∑ i, w i * (M * γ ^ (n + d i))) =
      (M * γ ^ n) * ∑ i, w i * γ ^ d i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_add₀ hγ0 n (d i)]
    ring
  rw [hfac]
  have hMγ : 0 ≤ M * γ ^ n :=
    mul_nonneg hM (le_of_lt (zpow_pos hγ n))
  calc (M * γ ^ n) * ∑ i, w i * γ ^ d i
      ≤ (M * γ ^ n) * c := mul_le_mul_of_nonneg_left h hMγ
    _ = c * (M * γ ^ n) := by ring

end Adequacy
end SuFunctor
