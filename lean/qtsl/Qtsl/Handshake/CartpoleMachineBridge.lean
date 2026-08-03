import Qtsl.Handshake.CartpoleControllerPinning

/-!
# Machine-code value bridge for the cart–pole controller

The Lean side of the machine-code value seam: an independently verified
five-instruction AArch64 fragment computes, for all in-range register
integers, the signed integer form `A = 81313·S + 1169·W`; this module
proves that that integer linear form is exactly the certified dyadic
control law of the pinning module in fixed-point representation.
-/

namespace PPLC.Handshake.CartpoleMachineBridge

open PPLC
open PPLC.Handshake.CartpoleCoreDecrease (Hnet f37)
open PPLC.Handshake.CartpoleControllerPinning

theorem accel_int_repr (f : ℕ) (S W : ℤ) (s ω : ℚ)
    (hs : s = (S : ℚ) / 2 ^ f) (hw : ω = (W : ℚ) / 2 ^ (f + 4)) :
    ((81313 * S + 1169 * W : ℤ) : ℚ) = accel s ω * 2 ^ (f + 12) := by
  have h2f : (2 : ℚ) ^ f ≠ 0 := by positivity
  have h2f4 : (2 : ℚ) ^ (f + 4) ≠ 0 := by positivity
  subst hs hw
  simp only [accel, K0, K1]
  push_cast
  field_simp
  ring

theorem machine_no_overflow (S W : ℤ)
    (hS : |S| ≤ 2 ^ 45) (hW : |W| ≤ 2 ^ 51) :
    |81313 * S + 1169 * W| < 2 ^ 63 := by
  rw [abs_le] at hS hW
  rw [abs_lt]
  constructor <;> linarith

theorem machine_semantics_certified (σ : Hnet.Valuation)
    (hadm : σ.Admissible) (hpre : Formula.holds σ f37)
    (s c ω : ℚ) (hq : σ.wireQ 0 = some (stateQ s c ω))
    (S W : ℤ) (hs : s = (S : ℚ) / 2 ^ 45) (hw : ω = (W : ℚ) / 2 ^ 49) :
    ((81313 * S + 1169 * W : ℤ) : ℚ) = accel s ω * 2 ^ 57 ∧
    lVdot s c ω ≤ 0 := by
  constructor
  · have h := accel_int_repr 45 S W s ω hs (by rw [hw])
    simpa using h
  · exact certified_decrease σ hadm hpre s c ω hq

#print axioms accel_int_repr
#print axioms machine_no_overflow
#print axioms machine_semantics_certified

end PPLC.Handshake.CartpoleMachineBridge
