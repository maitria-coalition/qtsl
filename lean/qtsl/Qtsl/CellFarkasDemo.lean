import Qtsl.CellFarkas
import Qtsl.ReluExpansion

/-!
# Farkas exclusion certificates: concrete receipts

Hand-written certificates for the interval fan `sigmaPM`'s two ordered
cell pairs, checked by `decide` — and `sigmaPM.CellIntDisjoint`
re-derived through `checkTable_sound`, so the certificate route
demonstrably discharges the same side condition that
`ReluExpansion.sigmaPM_disjoint` proves by hand geometry. (The two
routes meeting is the point: the exclusion needed a bespoke proof per
schema before; now it needs eight rational numbers per ordered pair.)

Three refusal receipts follow, one per checker clause family: the
all-zero certificate (rows balance, gap fails), a negative-multiplier
certificate whose rows balance with `alpha + beta = 1` (only the sign
clause refuses), and a certificate wrong precisely on an extension-
vertex row of the strict cell (only that row clause refuses). Each is
the value-level witness for one preregistered mutant locus of
`checkPair`.
-/

namespace PPLC
namespace CellFarkasDemo

open CellFarkas ReluExpansion

/-- Certificate for (`cNeg` strict, `cPos` weak): the separating
functional is `y ↦ y` (`gamma = 1`), unit multipliers on each side's
extension row, `alpha = beta = 0` — the gap lands in the
`alpha + beta = 0` branch with `p` nonzero at vertex 1. -/
def certNegPos : PairCert sigmaPM where
  alpha := 0
  beta := 0
  gamma := fun _ => 1
  p := fun v => if v.val = 1 then 1 else 0
  q := fun v => if v.val = 2 then 1 else 0

/-- Certificate for (`cPos` strict, `cNeg` weak): the mirror,
`gamma = -1`. -/
def certPosNeg : PairCert sigmaPM where
  alpha := 0
  beta := 0
  gamma := fun _ => -1
  p := fun v => if v.val = 2 then 1 else 0
  q := fun v => if v.val = 1 then 1 else 0

example : checkPair sigmaPM cNeg cPos certNegPos = true := by decide +kernel
example : checkPair sigmaPM cPos cNeg certPosNeg = true := by decide +kernel

/-- The full ordered-pair table for `sigmaPM` (diagonal never
consulted). -/
def sigmaPMTable : CertTable sigmaPM := fun i _ =>
  if i.val = 0 then certNegPos else certPosNeg

example : checkTable sigmaPM sigmaPMTable = true := by decide +kernel

/-- `sigmaPM`'s exclusion, re-derived from eight rational numbers per
ordered pair instead of hand geometry. -/
theorem sigmaPM_disjoint' : sigmaPM.CellIntDisjoint :=
  checkTable_sound (tbl := sigmaPMTable) (by decide +kernel)

/-! ## Refusal receipts (one per preregistered mutant locus)

Each certificate below fails exactly one clause family of `checkPair`;
under the corresponding checker mutation it would be accepted, so these
`decide`s are the value-level red witnesses for the mutant battery. -/

/-- All multipliers zero: every row balances trivially, and only the
gap clause refuses (`alpha + beta = 0` with no nonzero strict-side
multiplier). The locus-1 witness. -/
def certZero : PairCert sigmaPM where
  alpha := 0
  beta := 0
  gamma := fun _ => 0
  p := fun _ => 0
  q := fun _ => 0

example : checkPair sigmaPM cNeg cPos certZero = false := by decide +kernel

/-- Rows balance with `alpha + beta = 1 > 0`, but the vertex-0
multiplier is negative: only the sign clause refuses. The locus-2
witness. -/
def certNegMult : PairCert sigmaPM where
  alpha := 1
  beta := 0
  gamma := fun _ => 1
  p := fun v => if v.val = 0 then -1 else if v.val = 1 then 2 else 0
  q := fun v => if v.val = 2 then 1 else 0

example : checkPair sigmaPM cNeg cPos certNegMult = false := by decide +kernel

/-- `certNegPos` with the extension-vertex multiplier corrupted
(`p 1 = 5`): signs pass, the weak side passes, the gap passes, and only
the strict cell's extension row refuses. The locus-3 witness. -/
def certBadExtRow : PairCert sigmaPM where
  alpha := 0
  beta := 0
  gamma := fun _ => 1
  p := fun v => if v.val = 1 then 5 else 0
  q := fun v => if v.val = 2 then 1 else 0

example : checkPair sigmaPM cNeg cPos certBadExtRow = false := by decide +kernel

end CellFarkasDemo
end PPLC
