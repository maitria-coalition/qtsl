import Qtsl.EventualMember
import Qtsl.Behavioral
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Lattice-invariance soundness

Soundness of the lattice-invariance rule at judgement level: the family
object's invariance alias, via the exactness identity and payload
transport — the tiling half of the identity is the descent lemma
`Semiflow.exists_cellMem_subset` from the eventual-member development.
-/

namespace PPLC
namespace Qtsl

open Set

variable {X : Type*} {ι β : Type*}

section Exactness

variable [Finite ι] [PartialOrder ι]
variable {blocks : β → Set X} {emb : ι → β} {cover : ι → β}
variable {cells : ι → Set X} {C : Set ι}

theorem qLatticeInv_exact
    (hdc : IsLowerSet C)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hcellSub : ∀ i : ι, cells i ⊆ blocks (emb i)) :
    (⋃ i ∈ C, cells i) = ⋃ i ∈ C, blocks (emb i) := by
  refine subset_antisymm (iUnion₂_mono fun i _ => hcellSub i) ?_
  intro x hx
  obtain ⟨i, hiC, hmem⟩ := mem_iUnion₂.mp hx
  obtain ⟨j, hjsub, -, hjcell⟩ :=
    Semiflow.exists_cellMem_subset hJoin hcover hcellsSup i hmem
  exact mem_iUnion₂.mpr ⟨j, hdc (horder j i hjsub) hiC, hjcell⟩

theorem member_subset_cells_le
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (i : ι) :
    blocks (emb i) ⊆ ⋃ j ∈ Set.Iic i, cells j := by
  intro x hx
  obtain ⟨j, hjsub, -, hjcell⟩ :=
    Semiflow.exists_cellMem_subset hJoin hcover hcellsSup i hx
  exact mem_iUnion₂.mpr ⟨j, horder j i hjsub, hjcell⟩

end Exactness

section Soundness

variable [Finite ι] [PartialOrder ι]
variable {blocks : β → Set X} {emb : ι → β} {cover : ι → β}
variable {cells : ι → Set X} {C : Set ι}

theorem Semiflow.qLatticeInv_sound {φ : Semiflow X} {X0 : Set X}
    (hdc : IsLowerSet C)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hcellSub : ∀ i : ι, cells i ⊆ blocks (emb i))
    (hMember : φ.InvScopeSat (⋃ i ∈ C, blocks (emb i)) X0) :
    φ.InvScopeSat (⋃ i ∈ C, cells i) X0 := by
  rw [qLatticeInv_exact hdc hJoin hcover hcellsSup horder hcellSub]
  exact hMember

theorem Semiflow.qLatticeInv_sound_of_blockInv {φ : Semiflow X} {X0 : Set X}
    (hdc : IsLowerSet C)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hcellSub : ∀ i : ι, cells i ⊆ blocks (emb i))
    (hInv : φ.Invariant (⋃ i ∈ C, blocks (emb i)))
    (hInit : X0 ⊆ ⋃ i ∈ C, cells i) :
    φ.InvScopeSat (⋃ i ∈ C, cells i) X0 :=
  Semiflow.qLatticeInv_sound hdc hJoin hcover hcellsSup horder hcellSub
    (Semiflow.qBlockInv_sound hInv
      (qLatticeInv_exact hdc hJoin hcover hcellsSup horder hcellSub ▸ hInit))

theorem Behavior.qLatticeInv_sound {B : Behavior X} {X0 : Set X}
    (hdc : IsLowerSet C)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hcellSub : ∀ i : ι, cells i ⊆ blocks (emb i))
    (hMember : B.InvScopeSat (⋃ i ∈ C, blocks (emb i)) X0) :
    B.InvScopeSat (⋃ i ∈ C, cells i) X0 := by
  rw [qLatticeInv_exact hdc hJoin hcover hcellsSup horder hcellSub]
  exact hMember

theorem Behavior.qLatticeInv_sound_of_blockInv {B : Behavior X} {X0 : Set X}
    (hdc : IsLowerSet C)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hcellSub : ∀ i : ι, cells i ⊆ blocks (emb i))
    (hInv : B.Invariant (⋃ i ∈ C, blocks (emb i)))
    (hInit : X0 ⊆ ⋃ i ∈ C, cells i) :
    B.InvScopeSat (⋃ i ∈ C, cells i) X0 :=
  Behavior.qLatticeInv_sound hdc hJoin hcover hcellsSup horder hcellSub
    (Behavior.qBlockInv_sound hInv
      (qLatticeInv_exact hdc hJoin hcover hcellsSup horder hcellSub ▸ hInit))

end Soundness

end Qtsl

#print axioms Qtsl.qLatticeInv_exact
#print axioms Qtsl.member_subset_cells_le
#print axioms Qtsl.Semiflow.qLatticeInv_sound
#print axioms Qtsl.Semiflow.qLatticeInv_sound_of_blockInv
#print axioms Qtsl.Behavior.qLatticeInv_sound
#print axioms Qtsl.Behavior.qLatticeInv_sound_of_blockInv

end PPLC
