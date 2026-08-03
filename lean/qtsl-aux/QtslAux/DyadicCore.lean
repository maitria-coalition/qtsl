/-! # Core definitions for dyadic rationals and finite floating-point values

This dependency-free module fixes the basic vocabulary shared by the dyadic
arithmetic development and by checkers that consume floating-point inputs:
the predicate `IsDyadic` on rationals, the structure `FiniteFloat` of finite
floating-point values with explicit mantissa and exponent bounds, its
instantiation `FiniteDouble` at the IEEE 754 binary64 parameters, and the
exact rational value `FiniteFloat.toRat`. All theory (ring structure,
rounding, injectivity) lives downstream in `QtslAux.Dyadic`.
-/

namespace Qtsl

/-- A rational number is dyadic when it equals `m * 2 ^ e` for some integers
`m` and `e`. -/
def IsDyadic (q : Rat) : Prop := ∃ m e : Int, q = m * 2 ^ e

namespace Dyadic

/-- A finite floating-point value with mantissa precision `prec` and exponent
range `[emin, emax]`, recorded as an integer mantissa-exponent pair. The
represented rational value is `m * 2 ^ e` (see `FiniteFloat.toRat`); the
representation is not required to be normalized, so distinct pairs may denote
the same value. -/
structure FiniteFloat (prec : Nat) (emin emax : Int) where

  /-- The integer mantissa. -/
  m : Int

  /-- The integer exponent. -/
  e : Int

  /-- The mantissa has fewer than `prec` bits: `|m| < 2 ^ prec`. -/
  mantissa_bound : m.natAbs < 2 ^ prec

  /-- The exponent is at least `emin`. -/
  exp_lb : emin ≤ e

  /-- The exponent is at most `emax`. -/
  exp_ub : e ≤ emax

/-- Finite IEEE 754 binary64 values: 53 bits of mantissa and exponents in
`[-1074, 971]`, so that every finite double is `m * 2 ^ e` within these
bounds. -/
abbrev FiniteDouble := FiniteFloat 53 (-1074) 971

namespace FiniteFloat

variable {prec : Nat} {emin emax : Int}

/-- The exact rational value `m * 2 ^ e` of a finite floating-point value. -/
def toRat (x : FiniteFloat prec emin emax) : Rat := x.m * 2 ^ x.e

theorem toRat_def (x : FiniteFloat prec emin emax) :
    x.toRat = (x.m : Rat) * 2 ^ x.e := rfl

end FiniteFloat

end Dyadic

end Qtsl
