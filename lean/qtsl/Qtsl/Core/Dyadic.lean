import Qtsl.Core.Prim
import QtslAux.DyadicCore

/-!
# Dyadic-rational float model (computational core)

Definitions the executable checker needs from the float model:
`FloatFmt` (a format as mantissa/exponent bounds), the format-relative
rounding maps (`rdn`, `rup`, `rtz`, `rne`), and the four standard
binary formats. Every theorem about these objects — representability,
directedness, the IEEE correspondence — lives in
`Qtsl.Dyadic` and `Qtsl.IEEE754`, which import this
module together with mathlib.
-/

namespace PPLC

structure FloatFmt where
  prec : Nat
  eMin : Int
  eMax : Int
  prec_pos : 0 < prec
  eMin_le_eMax : eMin ≤ eMax

namespace FloatFmt

variable (fmt : FloatFmt)

def Rep (q : Rat) : Prop :=
  ∃ x : Qtsl.Dyadic.FiniteFloat fmt.prec fmt.eMin fmt.eMax, x.toRat = q

def maxFin : Rat := ((2 : Rat) ^ fmt.prec - 1) * 2 ^ fmt.eMax

def gridExp (q : Rat) : Int :=
  max fmt.eMin (Prim.intLog2 q.abs + 1 - fmt.prec)

def rdnRaw (q : Rat) : Rat :=
  ((q / 2 ^ fmt.gridExp q).floor : Rat) * 2 ^ fmt.gridExp q

def rdn (q : Rat) : Rat :=
  if fmt.maxFin ≤ q then fmt.maxFin
  else if q < -fmt.maxFin then -fmt.maxFin
  else fmt.rdnRaw q

def rup (q : Rat) : Rat := -(fmt.rdn (-q))

def rtz (q : Rat) : Rat := if 0 ≤ q then fmt.rdn q else fmt.rup q

def rne (q : Rat) : Rat :=
  if q - fmt.rdn q < fmt.rup q - q then fmt.rdn q
  else if fmt.rup q - q < q - fmt.rdn q then fmt.rup q
  else if (q / 2 ^ fmt.gridExp q).floor % 2 = 0 then fmt.rdn q else fmt.rup q

def f16  : FloatFmt := ⟨11, -24,   5,    by decide, by decide⟩
def bf16 : FloatFmt := ⟨8,  -133,  120,  by decide, by decide⟩
def f32  : FloatFmt := ⟨24, -149,  104,  by decide, by decide⟩
def f64  : FloatFmt := ⟨53, -1074, 971,  by decide, by decide⟩

end FloatFmt

end PPLC
