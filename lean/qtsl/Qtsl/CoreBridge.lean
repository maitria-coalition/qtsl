import Qtsl.Core.Prim
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Round

/-!
# Bridges between the computational core and mathlib

Equality lemmas identifying each core-Lean substitute in
`Qtsl.Core.Prim` (and each core-instance spelling used by the
`Core` modules) with the mathlib function it replaces, so proofs
written against the mathlib spellings transfer by rewriting. This
module is mathlib-side and is never linked into the executable checker.
-/

namespace PPLC.Prim

theorem nchoose_eq_choose : ∀ n k, nchoose n k = Nat.choose n k
  | n, 0 => by simp [nchoose]
  | 0, k + 1 => by simp [nchoose]
  | n + 1, k + 1 => by
    simp only [nchoose, Nat.choose_succ_succ,
      nchoose_eq_choose n k, nchoose_eq_choose n (k + 1)]

theorem clog2_eq (n : Nat) : clog2 n = Nat.clog 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [clog2]
    split
    · next h =>
      show clog2 ((n + 1) / 2) + 1 = _
      rw [ih ((n + 1) / 2) (by omega), Nat.clog_of_one_lt one_lt_two h]
      exact rfl
    · next h =>
      rw [Nat.clog_of_right_le_one (by omega)]

theorem ratFloor_eq (q : ℚ) : q.floor = ⌊q⌋ := rfl

theorem ratCeil_eq (q : ℚ) : q.ceil = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]
  show -⌊-q⌋ = ⌈q⌉
  rw [Int.floor_neg, neg_neg]

theorem ratAbs_eq (q : ℚ) : q.abs = |q| := by
  show (if 0 ≤ q then q else -q) = |q|
  split
  · next h => exact (abs_of_nonneg h).symm
  · next h => exact (abs_of_neg (lt_of_not_ge h)).symm

theorem intLog2_eq (q : ℚ) : intLog2 q = Int.log 2 q := by
  unfold intLog2
  split
  · next h =>
    rw [Int.log_of_one_le_right 2 h, Nat.log2_eq_log_two, ratFloor_eq,
      Int.floor_toNat]
  · next h =>
    rw [Int.log_of_right_le_one 2 (le_of_not_ge h), clog2_eq, ratCeil_eq,
      Int.ceil_toNat]

theorem roundNQ_eq (q : ℚ) : roundNQ q = round q := by
  rw [round_eq]
  rfl

theorem coreMaxQ_eq (a b : ℚ) : @Max.max ℚ Rat.instMax a b = max a b := by
  show (if a ≤ b then b else a) = max a b
  split
  · next h => exact (max_eq_right h).symm
  · next h => exact (max_eq_left (le_of_not_ge h)).symm

end PPLC.Prim
