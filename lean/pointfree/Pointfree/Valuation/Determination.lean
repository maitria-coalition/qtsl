import Pointfree.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Determination: continuous valuations from generator values

The localic determination principle, frame-generally.  On any frame,
a family of generators that is closed under finite meets and
join-generates the frame determines every Scott-continuous valuation
with finite generator values: two such valuations agreeing on the
generators are equal (`Valuation.ext_of_generators`), and two distinct
ones are separated by a single generator
(`Valuation.exists_generator_ne`).

This is the determination half of the Choquet–Matheron theorem at the
point-free stratum.  The classical statement (the law of a random
closed set is determined by its capacity functional on a generating
class; Choquet, Matheron 1975) carries a σ-algebra, a π–λ argument,
countability of the generating class, and a total-mass hypothesis.
The localic statement needs none of these:

* **modularity** replaces finite additivity and drives the
  inclusion–exclusion induction from generator values to values on
  finite joins of generators;
* **Scott continuity** replaces countable additivity and closes the
  gap from finite joins to arbitrary elements — every element is a
  directed join of finite subjoins of any generator decomposition;
* the finiteness hypothesis is **finite generator values** only
  (`∀ i, μ (G i) ≠ ∞`), strictly weaker than finite total mass:
  finiteness propagates to finite joins by subadditivity, which is
  all the `ℝ≥0∞` cancellation in the induction consumes.  The
  hypothesis is honest load — two distinct multiples of a counting
  measure on a countable dense carrier agree (vacuously, at `∞`) on
  a basis of infinite-mass generators.

No countability, no points, no σ-algebra, no measurability enter
anywhere.  Instances: the presented hyperspace frame
(`Pointfree.Valuation.ext_of_nabla`) and the spatial frame of opens
of any topological space (`Pointfree.Valuation.ext_of_isTopologicalBasis`).
-/

namespace Pointfree

open scoped ENNReal

namespace Valuation

variable {L : Type*} [Order.Frame L] {κ : Type*} {G : κ → L} {μ ν : Valuation L}

/-- Subadditivity on binary joins, from modularity alone. -/
theorem apply_sup_le_add (μ : Valuation L) (a b : L) :
    μ (a ⊔ b) ≤ μ a + μ b :=
  calc μ (a ⊔ b) ≤ μ (a ⊔ b) + μ (a ⊓ b) := le_self_add
    _ = μ a + μ b := (μ.modular a b).symm

/-- Finite generator values give finite values on finite joins of
generators — the finiteness the cancellation steps consume. -/
theorem finsetSup_ne_top (hfin : ∀ i, μ (G i) ≠ ∞) (s : Finset κ) :
    μ (s.sup G) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s _ ih =>
      rw [Finset.sup_insert]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin k, ih⟩)
        (μ.apply_sup_le_add _ _)

private theorem agree_on_finsetSup_of_card
    (hGinf : ∀ i j, ∃ k, G i ⊓ G j = G k)
    (hfin : ∀ i, μ (G i) ≠ ∞)
    (h : ∀ i, μ (G i) = ν (G i)) :
    ∀ n : ℕ, ∀ s : Finset κ, s.card ≤ n → μ (s.sup G) = ν (s.sup G) := by
  classical
  choose c hc using hGinf
  intro n
  induction n with
  | zero =>
      intro s hs
      rw [Nat.le_zero, Finset.card_eq_zero] at hs
      subst hs
      simp
  | succ n ih =>
      intro s hs
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨k, hk⟩
      · simp
      · set t := s.erase k with ht
        have hs' : t.card ≤ n := by
          have hcard : t.card = s.card - 1 := by
            rw [ht]
            exact Finset.card_erase_of_mem hk
          omega
        have hins : s = insert k t := (Finset.insert_erase hk).symm
        rw [hins, Finset.sup_insert]
        -- the meet term is a generator join over an image finset
        have hmeet : G k ⊓ t.sup G = (t.image (c k)).sup G := by
          calc G k ⊓ t.sup G
              = t.sup fun i => G k ⊓ G i := Finset.sup_inf_distrib_left t G (G k)
            _ = t.sup fun i => G (c k i) := Finset.sup_congr rfl fun i _ => hc k i
            _ = (t.image (c k)).sup G := (Finset.sup_image t (c k) G).symm
        have himg : μ ((t.image (c k)).sup G) = ν ((t.image (c k)).sup G) :=
          ih _ (le_trans (Finset.card_image_le) hs')
        have htt : μ (t.sup G) = ν (t.sup G) := ih t hs'
        have hfin' : μ ((t.image (c k)).sup G) ≠ ∞ := finsetSup_ne_top hfin _
        -- modularity on both sides, cancellation of the common finite meet term
        have key : μ (G k ⊔ t.sup G) + μ ((t.image (c k)).sup G)
            = ν (G k ⊔ t.sup G) + μ ((t.image (c k)).sup G) := by
          calc μ (G k ⊔ t.sup G) + μ ((t.image (c k)).sup G)
              = μ (G k ⊔ t.sup G) + μ (G k ⊓ t.sup G) := by rw [hmeet]
            _ = μ (G k) + μ (t.sup G) := (μ.modular _ _).symm
            _ = ν (G k) + ν (t.sup G) := by rw [h k, htt]
            _ = ν (G k ⊔ t.sup G) + ν (G k ⊓ t.sup G) := ν.modular _ _
            _ = ν (G k ⊔ t.sup G) + μ ((t.image (c k)).sup G) := by
                rw [hmeet, himg]
        exact (ENNReal.add_left_inj hfin').mp key

/-- **Inclusion–exclusion propagation**: two valuations with finite
generator values agreeing on a meet-closed generator family agree on
all finite joins of generators.  Modularity is the engine; the
meet-closure hypothesis keeps the correction term inside the family. -/
theorem agree_on_finsetSup
    (hGinf : ∀ i j, ∃ k, G i ⊓ G j = G k)
    (hfin : ∀ i, μ (G i) ≠ ∞)
    (h : ∀ i, μ (G i) = ν (G i)) (s : Finset κ) :
    μ (s.sup G) = ν (s.sup G) :=
  agree_on_finsetSup_of_card hGinf hfin h s.card s le_rfl

/-- **Determination from generator values** (the localic
Choquet–Matheron uniqueness): on any frame, two Scott-continuous
valuations with finite generator values that agree on a meet-closed,
join-generating family of generators are equal.  No countability, no
σ-algebra, no points. -/
theorem ext_of_generators
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hGinf : ∀ i j, ∃ k, G i ⊓ G j = G k)
    (hGgen : ∀ x : L, ∃ S : Set κ, x = ⨆ i ∈ S, G i)
    (hfin : ∀ i, μ (G i) ≠ ∞)
    (h : ∀ i, μ (G i) = ν (G i)) : μ = ν := by
  classical
  ext x
  obtain ⟨S, hS⟩ := hGgen x
  set d : Set L := (fun t : Finset κ => t.sup G) '' {t : Finset κ | ↑t ⊆ S} with hd
  have hdne : d.Nonempty := ⟨⊥, ∅, by simp, by simp⟩
  have hdir : DirectedOn (· ≤ ·) d := by
    rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
    refine ⟨(t₁ ∪ t₂).sup G, ⟨t₁ ∪ t₂, ?_, rfl⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Finset.coe_union]
      exact Set.union_subset ht₁ ht₂
    · rw [Finset.sup_union]
      exact le_sup_left
    · rw [Finset.sup_union]
      exact le_sup_right
  have hsup : sSup d = x := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨t, htS, rfl⟩
      refine Finset.sup_le fun i hi => ?_
      rw [hS]
      exact le_biSup G (htS hi)
    · rw [hS]
      refine iSup₂_le fun i hi => ?_
      refine le_sSup ⟨{i}, ?_, ?_⟩
      · simpa using hi
      · simp
  calc μ x = μ (sSup d) := by rw [hsup]
    _ = ⨆ y ∈ d, μ y := hμS d hdne hdir
    _ = ⨆ y ∈ d, ν y := by
        refine biSup_congr fun y hy => ?_
        obtain ⟨t, -, rfl⟩ := hy
        exact agree_on_finsetSup hGinf hfin h t
    _ = ν (sSup d) := (hνS d hdne hdir).symm
    _ = ν x := by rw [hsup]

/-- **Separation** (the contrapositive package, matching the landed
point-set pair): two distinct Scott-continuous valuations with finite
generator values are separated by a single generator. -/
theorem exists_generator_ne
    (hμS : μ.IsScottContinuous) (hνS : ν.IsScottContinuous)
    (hGinf : ∀ i j, ∃ k, G i ⊓ G j = G k)
    (hGgen : ∀ x : L, ∃ S : Set κ, x = ⨆ i ∈ S, G i)
    (hfin : ∀ i, μ (G i) ≠ ∞)
    (hne : μ ≠ ν) : ∃ i, μ (G i) ≠ ν (G i) := by
  by_contra hcon
  push Not at hcon
  exact hne (ext_of_generators hμS hνS hGinf hGgen hfin hcon)

end Valuation

end Pointfree
