import Qtsl.Core.ERat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.EReal.Basic

/-!
# Exact extended rationals: the semantic bridge

The bridge from `ERat` (defined in `Qtsl.Core.ERat`) to
mathlib's `EReal`: `toEReal` and its order-faithfulness — comparisons
of exact extended rationals mean exactly what their interpretations in
ℝ ∪ {±∞} mean — together with totality lemmas for the partial
arithmetic on finite lists.
-/

namespace PPLC

namespace ERat

noncomputable def toEReal : ERat → EReal
  | negInf => ⊥
  | fin q  => ((q : ℝ) : EReal)
  | posInf => ⊤

theorem toEReal_le_toEReal {a b : ERat} : toEReal a ≤ toEReal b ↔ a ≤ b := by
  cases a <;> cases b
  · exact iff_of_true le_rfl trivial
  · exact iff_of_true bot_le trivial
  · exact iff_of_true bot_le trivial
  · exact iff_of_false (fun h => EReal.coe_ne_bot _ (le_bot_iff.mp h)) (fun h => h)
  · exact EReal.coe_le_coe_iff.trans Rat.cast_le
  · exact iff_of_true le_top trivial
  · exact iff_of_false (fun h => bot_ne_top (top_le_iff.mp h)) (fun h => h)
  · exact iff_of_false (fun h => EReal.coe_ne_top _ (top_le_iff.mp h)) (fun h => h)
  · exact iff_of_true le_rfl trivial

theorem toEReal_injective : Function.Injective toEReal := by
  intro a b h
  cases a <;> cases b <;> simp only [toEReal] at h
  · rfl
  · exact absurd h.symm (EReal.coe_ne_bot _)
  · exact absurd h bot_ne_top
  · exact absurd h (EReal.coe_ne_bot _)
  · exact congrArg fin (by exact_mod_cast h)
  · exact absurd h (EReal.coe_ne_top _)
  · exact absurd h.symm bot_ne_top
  · exact absurd h.symm (EReal.coe_ne_top _)
  · rfl

noncomputable def toRealLossy : ERat → ℝ
  | negInf => 0
  | fin q  => (q : ℝ)
  | posInf => 0

theorem sum?_fin (l : List ℚ) : sum? (l.map fin) = some (fin l.sum) := by
  suffices h : ∀ (a : ℚ), (l.map fin).foldlM add? (fin a) = some (fin (a + l.sum)) by
    simpa [sum?] using h 0
  induction l with
  | nil => simp
  | cons x xs ih => intro a; simp [add?, ih, add_assoc]

theorem prod?_fin (l : List ℚ) : prod? (l.map fin) = some (fin l.prod) := by
  suffices h : ∀ (a : ℚ), (l.map fin).foldlM mul? (fin a) = some (fin (a * l.prod)) by
    simpa [prod?] using h 1
  induction l with
  | nil => simp
  | cons x xs ih => intro a; simp [mul?, ih, mul_assoc]

end ERat

end PPLC
