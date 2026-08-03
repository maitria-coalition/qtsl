import Qtsl.Core.Dyadic
import Qtsl.Core.ERat
import Qtsl.Core.QArith

/-!
# Kernel-side coverage receipts

Ground facts held by `decide +kernel` at elaboration time for core
definitions that the runtime receipt suite does not exercise. Each
`example` is one-sided evidence (Lean kernel only), deliberately kept
out of the runtime verdict table, whose row set is pinned against an
independently verified twin.
-/

namespace PPLC
namespace KernelReceipts

def kreceipts : List String := [
  "f32.maxFin = 340282346638528859811704183484516925440 (IEEE binary32 max, exact)",
  "f32.rtz(1/3) = 11184810/2^25",
  "f32: rtz(-1/3) = -11184810/2^25 but rdn(-1/3) = -11184811/2^25 (toward-zero vs toward-neg-inf witness)",
  "f16.maxFin = 65504 (IEEE binary16 max, exact)",
  "f16.rtz saturates: rtz(70000) = 65504 and rtz(-70000) = -65504",
  "f16.rtz(1/100000) = 167/2^24 (subnormal regime: gridExp floored at eMin = -24)",
  "ERat.prod? [2, +inf, -3] = -inf (signs multiply through infinities)",
  "ERat.prod? [0, +inf] = none = ERat.prod? [+inf, 0] (0 * inf poisons, both orders)",
  "Poly.totalDeg [] = 0 and totalDeg (5*x0^2*x1^3 + 1) = 5"]

example :
    FloatFmt.f32.maxFin = 340282346638528859811704183484516925440 := by
  decide +kernel

example : FloatFmt.f32.rtz (1/3) = 11184810 / 2 ^ 25 := by
  decide +kernel

example :
    FloatFmt.f32.rtz (-(1/3)) = -(11184810 / 2 ^ 25) ∧
    FloatFmt.f32.rdn (-(1/3)) = -(11184811 / 2 ^ 25) := by
  constructor <;> decide +kernel

example : FloatFmt.f16.maxFin = 65504 := by decide +kernel

example :
    FloatFmt.f16.rtz 70000 = 65504 ∧ FloatFmt.f16.rtz (-70000) = -65504 := by
  constructor <;> decide +kernel

example : FloatFmt.f16.rtz (1/100000) = 167 / 2 ^ 24 := by decide +kernel

example :
    ERat.prod? [.fin 2, .posInf, .fin (-3)] = some .negInf := by
  decide +kernel

example :
    ERat.prod? [.fin 0, .posInf] = none ∧
    ERat.prod? [.posInf, .fin 0] = none := by
  constructor <;> decide +kernel

example :
    QArith.Poly.totalDeg [] = 0 ∧
    QArith.Poly.totalDeg [([(0, 2), (1, 3)], 5), ([], 1)] = 5 := by
  constructor <;> decide +kernel

end KernelReceipts
end PPLC
