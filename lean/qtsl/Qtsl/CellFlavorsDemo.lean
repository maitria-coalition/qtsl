import Qtsl.CellFlavors
import Qtsl.ReluExpansion

/-!
# Flavored cell schemas: concrete smoke instances

Two miniature instances exercising `Qtsl.CellFlavors` end to end:

* `quadrantsTS` — the planar quadrant fan as a tensor-simplicial
  schema: two singleton clusters, `ReluExpansion.sigmaPM` in each.
  Its exclusion (`quadrantsTS_disjoint`) is discharged by
  `CellSchemaTS.product_exclusion` + the once-proved species lemma
  `sigmaPM_disjoint` — the library-species-citation pattern in
  miniature: per-cluster certificate cost is zero bytes.
* `halfLineSA` — the `k = 1` full-semialgebraic schema whose single
  presenter is the identity hypernet (empty application list, input
  wire = output wire). Its two sign cells are exactly `sigmaPM`'s two
  cells: the sign-to-mask-region dictionary at `k = 1` is already
  mechanized as `maskRegion_cNeg_iff` / `maskRegion_cPos_iff` and
  their strict companions in `Qtsl.ReluExpansion`.
-/

namespace PPLC
namespace CellFlavorsDemo

open ReluExpansion

/-- The planar quadrant fan: two singleton clusters, the interval fan
`sigmaPM` in each. Cells are the four (closed) quadrants, walls shared
weakly. -/
def quadrantsTS : CellSchemaTS where
  D := 2
  m := 2
  part := id
  complexes := fun _ => sigmaPM
  dimsMatch := by decide

/-- Product exclusion for the quadrant fan, by citing the species:
`sigmaPM`'s exclusion is a once-proved lemma, so the per-cluster
certificate burden is zero. -/
theorem quadrantsTS_disjoint : quadrantsTS.CellIntDisjoint :=
  quadrantsTS.product_exclusion (fun _ => sigmaPM_disjoint)

/-- The identity presenter: no applications, the designated input and
output wire coincide. -/
def idNet : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

/-- The half-line split as a `k = 1` full-semialgebraic schema: one
presenter (the identity), two cells `⊕` = `{x ≥ 0}` and `⊖` =
`{x ≤ 0}`, the wall `x = 0` weakly in both — `sigmaPM`'s two cells. -/
def halfLineSA : CellSchemaSA where
  hostShape := [1]
  k := 1
  funs := fun _ => idNet
  inWire := fun _ => 0
  outWire := fun _ => 0
  domOk := fun _ => rfl
  codOk := fun _ => rfl
  cellFree := fun _ _ h => nomatch h

/-- Sign exclusion at the instance, for the record: the two half-lines
satisfy strict-vs-weak exclusion with no certificate. -/
example {y : Fin halfLineSA.k → ℚ} {σ τ : Fin halfLineSA.k → Bool}
    (hστ : σ ≠ τ) (hs : halfLineSA.MemViaStrict y σ) :
    ¬ halfLineSA.MemVia y τ :=
  halfLineSA.sign_exclusion hστ hs

#print axioms quadrantsTS_disjoint

end CellFlavorsDemo
end PPLC
