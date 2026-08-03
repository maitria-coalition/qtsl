/-!
# Core-Lean substitutes for mathlib functions

Zero-import module. Each definition replaces exactly one mathlib
dependency of a computational definition — `nchoose` for `Nat.choose`,
`clog2` for `Nat.clog 2`, `intLog2` for `Int.log 2`, `roundNQ` for
rounding on ℚ, and a decidable-equality instance for functions out of
`Fin` — with the equality bridge to the mathlib original proved in
`Qtsl.CoreBridge`.
-/

namespace PPLC.Prim

def nchoose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => nchoose n k + nchoose n (k + 1)

def clog2 (n : Nat) : Nat :=
  if h : 1 < n then
    have : (n + 1) / 2 < n := by omega
    clog2 ((n + 1) / 2) + 1
  else 0

def intLog2 (q : Rat) : Int :=
  if 1 ≤ q then (Nat.log2 q.floor.toNat : Int)
  else -(clog2 q⁻¹.ceil.toNat : Int)

def roundNQ (q : Rat) : Int := (q + 1/2).floor

instance (priority := 100) decEqFinFun {n : Nat} {α : Type _} [DecidableEq α] :
    DecidableEq (Fin n → α) := fun f g =>
  decidable_of_iff (∀ i, f i = g i) ⟨funext, fun h i => congrFun h i⟩

end PPLC.Prim
