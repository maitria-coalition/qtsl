import QtslAux.Enclosure

/-!
# Semantic validity of enclosure judgments

The judgment-level face of the enclosure obligation: an
`EncJudgment{func, n, r, cap}` claims that the tagged primitive
function is enclosed by its degree-`n` canonical Maclaurin prefix
within `cap` on the symmetric interval `[-r, r]`. The prefix is
determined by `(func, n)` and never stored — exactly the discipline
of the executable checkers (the fast path recomputes it; the
reference lane treats it as a pure recomputation).

The mathematics is the established `QtslAux.Enclosure` development:
`encCheck` decides the witness-level obligation (coefficients match,
`0 ≤ r < n + 2`, `tailBound n r ≤ cap`) in exact rational arithmetic,
and `encCheck_sound` carries an accepted witness to the real-analytic
enclosure — mathlib-backed, no axioms beyond the standard three. This
module only specializes it to the canonically built witness, which is
the unique witness an `EncJudgment` denotes.
-/

namespace PPLC
namespace Geolog

open Qtsl.Enclosure

/-- Wire tag → `FnTag`: the three-tag wire roster (0 = exp, 1 = sin,
2 = cos; the wire format carries no fourth tag — `erfT` exists in the
mathematical development but not on the wire). -/
def fnTagOfWire : Nat → Option FnTag
  | 0 => some .exp
  | 1 => some .sin
  | 2 => some .cos
  | _ => none

/-- The canonical degree-`n` Maclaurin prefix of the tagged function,
as the judgment determines it. -/
def encCoeffs (t : FnTag) (n : Nat) : List Rat :=
  (List.range (n + 1)).map (maclaurin t)

/-- The canonical witness an `EncJudgment` denotes. -/
def encWitnessOf (t : FnTag) (n : Nat) (r cap : Rat) : EncWitness :=
  ⟨t, n, r, cap, encCoeffs t n⟩

/-- The enclosing polynomial: the canonical prefix, evaluated over ℝ. -/
noncomputable def encPoly (t : FnTag) (n : Nat) (x : Real) : Real :=
  evalPoly (encCoeffs t n) x

/-- Semantic validity of an enclosure judgment: on `|x| ≤ r` the
tagged function is enclosed by its degree-`n` canonical Maclaurin
prefix to within `cap`. This is the proposition an accepted
enclosure certificate carries. -/
def EncValid (t : FnTag) (n : Nat) (r cap : Rat) : Prop :=
  ∀ x : Real, |x| ≤ (r : Real) →
    |t.eval x - encPoly t n x| ≤ (cap : Real)

/-- Judgment-level checker: `encCheck` on the canonical witness. The
coefficient clause holds by construction but is nonetheless executed,
matching the executable checkers' posture (the recompute IS the
check); the decided content is the radius clause `0 ≤ r < n + 2` and
the tail clause `tailBound n r ≤ cap`. -/
def encJCheck (t : FnTag) (n : Nat) (r cap : Rat) : Bool :=
  encCheck (encWitnessOf t n r cap)

/-- Soundness at judgment grain: an accepted judgment is
semantically valid. Direct specialization of the established
`encCheck_sound` to the canonical witness. -/
theorem encJCheck_sound {t : FnTag} {n : Nat} {r cap : Rat}
    (h : encJCheck t n r cap = true) : EncValid t n r cap :=
  fun x hx => encCheck_sound (encWitnessOf t n r cap) h x hx

end Geolog
end PPLC
