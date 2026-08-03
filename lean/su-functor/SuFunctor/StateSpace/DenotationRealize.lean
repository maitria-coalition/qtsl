import SuFunctor.StateSpace.Pieces
import Qtsl.DenotationClass

/-! # Realizing denotation-class piece data in the real ambient

The primitive calculus's denotation class (`PPLC.IsPiecewisePolyRel`)
is carried by finite piece data over ℚ: carving polynomials and a
polynomial map per piece.  This module realizes that data in the real
ambient of the ω-semialgebraic development: the realized graph of a
piece is a single basic piece of the joint ambient `ℝ^(d+m)` — the
carving conditions pulled along the input coordinates, plus one
equality pair per output coordinate — so every realized piece graph,
and every finite union of them, is ω-semialgebraic on sight.

This is the outer-stratum half of the calculus's completion story: the
denotation class is the finitary, closed-piece fragment of exactly the
piece data whose countable unions define the ω-semialgebraic sets.
The realization is a statement about the *data*: the denotation
relation itself lives on rational points, and the realized set is the
real-ambient extension of the same carving — the two agree on rational
points by construction, while the topological relationship between a
ℚ-point relation and its real realization is a separate question this
module deliberately does not touch.
-/

namespace SuFunctor.StateSpace

open MvPolynomial Set

noncomputable section

variable {d m : ℕ}

/-- The carving conditions of a realized piece graph: the piece's own
conditions pulled to the joint ambient along the input coordinates,
and one equality pair per output coordinate. -/
def realizeConds (P : PPLC.PieceData d m) : List (PolyCond (d + m)) :=
  P.conds.map (fun q => ⟨-(rename (Fin.castAdd m) q), .le⟩)
    ++ (List.ofFn fun j : Fin m =>
      [(⟨X (Fin.natAdd d j) - rename (Fin.castAdd m) (P.val j), .le⟩ :
          PolyCond (d + m)),
       ⟨rename (Fin.castAdd m) (P.val j) - X (Fin.natAdd d j), .le⟩]).flatten

/-- The realized graph of a piece datum: the subset of the joint real
ambient carved by its conditions and output equations — a single basic
piece. -/
def realizeGraph (P : PPLC.PieceData d m) : Set (Fin (d + m) → ℝ) :=
  BasicSet (realizeConds P)

/-- Membership in the realized graph is the semantic reading: the
carving holds at the input coordinates and each output coordinate is
the piece map's value. -/
theorem mem_realizeGraph_iff {P : PPLC.PieceData d m}
    {z : Fin (d + m) → ℝ} :
    z ∈ realizeGraph P ↔
      (∀ q ∈ P.conds, 0 ≤ aeval (z ∘ Fin.castAdd m) q) ∧
      ∀ j, z (Fin.natAdd d j) = aeval (z ∘ Fin.castAdd m) (P.val j) := by
  rw [realizeGraph, mem_basicSet, realizeConds, List.forall_mem_append]
  constructor
  · rintro ⟨hconds, heqs⟩
    refine ⟨fun q hq => ?_, fun j => ?_⟩
    · have h := hconds _ (List.mem_map_of_mem hq)
      rw [PolyCond.holds_le, map_neg, neg_nonpos, aeval_rename] at h
      exact h
    · have h1 := heqs _ (List.mem_flatten.mpr
        ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, List.mem_cons_self ..⟩)
      have h2 := heqs _ (List.mem_flatten.mpr
        ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩,
          List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩)
      rw [PolyCond.holds_le, map_sub, aeval_X, aeval_rename, sub_nonpos] at h1
      rw [PolyCond.holds_le, map_sub, aeval_rename, aeval_X, sub_nonpos] at h2
      exact le_antisymm h1 h2
  · rintro ⟨hconds, heqs⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [PolyCond.holds_le, map_neg, neg_nonpos, aeval_rename]
      exact hconds q hq
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      rcases List.mem_cons.mp hcl with rfl | hcl'
      · rw [PolyCond.holds_le, map_sub, aeval_X, aeval_rename, sub_nonpos]
        exact le_of_eq (heqs j)
      · rw [List.mem_singleton.mp hcl']
        rw [PolyCond.holds_le, map_sub, aeval_rename, aeval_X, sub_nonpos]
        exact le_of_eq (heqs j).symm

/-- Every realized piece graph is ω-semialgebraic: it is one basic
piece. -/
theorem isOmegaSA_realizeGraph (P : PPLC.PieceData d m) :
    IsOmegaSA (realizeGraph P) :=
  IsOmegaSA.of_basic _

/-- Finite unions of realized piece graphs are ω-semialgebraic: the
denotation class's data realizes inside the ω-semialgebraic stratum. -/
theorem isOmegaSA_realizeUnion (Ps : List (PPLC.PieceData d m)) :
    IsOmegaSA (⋃ P ∈ Ps, realizeGraph P) := by
  induction Ps with
  | nil =>
      have h : (⋃ P ∈ ([] : List (PPLC.PieceData d m)), realizeGraph P)
          = (∅ : Set (Fin (d + m) → ℝ)) := by
        ext z
        simp
      rw [h]
      exact IsOmegaSA.empty
  | cons P Ps ih =>
      have h : (⋃ Q ∈ (P :: Ps), realizeGraph Q)
          = realizeGraph P ∪ ⋃ Q ∈ Ps, realizeGraph Q := by
        ext z
        constructor
        · intro hz
          obtain ⟨Q, hQ, hzQ⟩ := Set.mem_iUnion₂.mp hz
          rcases List.mem_cons.mp hQ with rfl | hQ'
          · exact Or.inl hzQ
          · exact Or.inr (Set.mem_iUnion₂.mpr ⟨Q, hQ', hzQ⟩)
        · rintro (hz | hz)
          · exact Set.mem_iUnion₂.mpr ⟨P, List.mem_cons_self .., hz⟩
          · obtain ⟨Q, hQ, hzQ⟩ := Set.mem_iUnion₂.mp hz
            exact Set.mem_iUnion₂.mpr ⟨Q, List.mem_cons_of_mem _ hQ, hzQ⟩
      rw [h]
      exact (isOmegaSA_realizeGraph P).union ih

#print axioms mem_realizeGraph_iff
#print axioms isOmegaSA_realizeGraph
#print axioms isOmegaSA_realizeUnion

end

end SuFunctor.StateSpace
