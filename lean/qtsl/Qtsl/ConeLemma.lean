import Qtsl.Catalogue

/-!
# Bernstein-cone lemma interfaces

The attach points between the exact-rational decision procedures and
the soundness development: the statement shapes `BoundedConvexHullQ`
(the `S = ∅` Bernstein-cone lemma, proved in `QArithKernel`) and
`StarIdentity` (the `S ≠ ∅` frontier obligation, staged in
`StarIdentityDAG`).
-/

namespace PPLC
namespace ConeLemma

open QArith

def StarIdentity : Prop :=
  ∀ (verts : List (List ℚ)) (smask : List Bool) (d : Nat) (p : Poly)
    (u yFace : List ℚ),
    smask.length = verts.length →
    u.length = (smask.filter id).length →
    yFace.length = (smask.filter (!·)).length →
    yFace.foldr (·+·) 0 = 1 →
    (fdBernstein verts smask d p).isSome →
    starIdentityCheck verts smask d p u yFace = some true

def BoundedConvexHullQ : Prop :=
  ∀ (verts : List (List ℚ)) (d : Nat) (p : Poly) (pred : ℚ → Bool)
    (t : FDTable),
    fdBernstein verts (verts.map fun _ => false) d p = some t →
    gridAll pred t = true →

    (∀ a b lam : ℚ, 0 ≤ lam → lam ≤ 1 → pred a → pred b →
      pred (lam * a + (1 - lam) * b)) →
    ∀ (lam : List ℚ), lam.length = verts.length →
      (∀ x ∈ lam, 0 ≤ x) → lam.foldr (·+·) 0 = 1 →
      pred (t.base.foldr
        (fun (α, b) acc =>
          acc + b * (multinomial α : ℚ) *
            ((α.zip lam).foldr (fun (e, l) a => l ^ e * a) 1))
        0)

end ConeLemma
end PPLC
