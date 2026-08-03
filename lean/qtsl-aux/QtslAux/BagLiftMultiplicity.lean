import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.NatInt

/-! # Ordered vs unordered selection sums

`sum_embeddings_factorial`: summing a range-factoring function over all
injective tuples (`Fin a ↪ α`) equals `a!` times its sum over `a`-element
subsets — the `∏ a_P!` multiplicity dictionary.
-/

namespace Qtsl.BagLift

/-- The embeddings `Fin a ↪ α` whose range is a fixed `a`-element subset `s`
number exactly `a!`: they are in bijection with `Fin a ≃ ↥s` by corestriction. -/
theorem card_embeddings_range_eq {α : Type} [Fintype α] [DecidableEq α] {a : ℕ}
    {s : Finset α} (hs : s ∈ Finset.univ.powersetCard a) :
    Fintype.card {e : Fin a ↪ α // Finset.univ.map e = s} = a.factorial := by
  obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hs
  have hfs : Fintype.card (↥s) = Fintype.card (Fin a) := by
    rw [Fintype.card_coe, Fintype.card_fin, hcard]
  have hmem : ∀ (e : Fin a ↪ α), Finset.univ.map e = s → ∀ i : Fin a, e i ∈ s := by
    intro e he i
    rw [← he]
    exact Finset.mem_map_of_mem e (Finset.mem_univ i)
  have hbij : ∀ p : {e : Fin a ↪ α // Finset.univ.map e = s},
      Function.Bijective (fun i : Fin a => (⟨p.1 i, hmem p.1 p.2 i⟩ : ↥s)) := fun p =>
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ hij => p.1.injective (congrArg Subtype.val hij), hfs.symm⟩
  have hrange : ∀ g : Fin a ≃ ↥s,
      Finset.univ.map
          ⟨fun i => (g i : α), fun _ _ hij => g.injective (Subtype.coe_injective hij)⟩
        = s := by
    intro g
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      exact (g i).2
    · simp [hcard]
  have E : {e : Fin a ↪ α // Finset.univ.map e = s} ≃ (Fin a ≃ ↥s) :=
    { toFun := fun p => Equiv.ofBijective _ (hbij p)
      invFun := fun g =>
        ⟨⟨fun i => (g i : α), fun _ _ hij => g.injective (Subtype.coe_injective hij)⟩,
          hrange g⟩
      left_inv := fun p => Subtype.ext (Function.Embedding.ext fun _ => rfl)
      right_inv := fun g => Equiv.ext fun _ => Subtype.ext rfl }
  rw [Fintype.card_congr E, Fintype.card_equiv (Fintype.equivOfCardEq hfs.symm),
    Fintype.card_fin]

/-- The `∏ a_P!` multiplicity dictionary: the ordered-selection sum
over injective tuples equals `a!` times the unordered-subset
sum, for any generator term that factors through the selected set. -/
theorem sum_embeddings_factorial {α : Type} [Fintype α] [DecidableEq α] {a : ℕ}
    {A : Type*} [AddCommMonoid A] (G : Finset α → A) :
    (∑ e : Fin a ↪ α, G ((Finset.univ : Finset (Fin a)).map e))
      = a.factorial • ∑ s ∈ Finset.univ.powersetCard a, G s := by
  have hmaps : ∀ e : Fin a ↪ α, e ∈ (Finset.univ : Finset (Fin a ↪ α)) →
      Finset.univ.map e ∈ Finset.univ.powersetCard a := fun e _ =>
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩
  calc (∑ e : Fin a ↪ α, G (Finset.univ.map e))
      = ∑ t ∈ Finset.univ.powersetCard a,
          ∑ e ∈ Finset.univ.filter (fun e : Fin a ↪ α => Finset.univ.map e = t), G t :=
        (Finset.sum_fiberwise_of_maps_to' hmaps G).symm
    _ = ∑ t ∈ Finset.univ.powersetCard a, a.factorial • G t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.sum_const]
        have hsub : Fintype.card {e : Fin a ↪ α // Finset.univ.map e = t}
            = (Finset.univ.filter (fun e : Fin a ↪ α => Finset.univ.map e = t)).card :=
          Fintype.card_of_subtype _ fun e => by simp
        rw [← hsub, card_embeddings_range_eq ht]
    _ = a.factorial • ∑ t ∈ Finset.univ.powersetCard a, G t :=
        Finset.sum_nsmul _ _ _

/-- `a = 2` corollary: the ordered-pair sum is twice the unordered-pair sum. -/
theorem sum_embeddings_two {α : Type} [Fintype α] [DecidableEq α]
    {A : Type*} [AddCommMonoid A] (G : Finset α → A) :
    (∑ e : Fin 2 ↪ α, G ((Finset.univ : Finset (Fin 2)).map e))
      = 2 • ∑ s ∈ Finset.univ.powersetCard 2, G s := by
  simpa [Nat.factorial_two] using sum_embeddings_factorial (a := 2) G

end Qtsl.BagLift

#print axioms Qtsl.BagLift.sum_embeddings_factorial
